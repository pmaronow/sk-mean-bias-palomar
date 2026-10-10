module
public import QuantitativeFollowup.ChenStandardGaussian
public import QuantitativePaper.NormalizedMoments
public import QuantitativePaper.VectorTerminalSmooth
public import QuantitativePaper.VectorRecursion

@[expose] public section

/-! Chen convexity for the actual finite SK logarithmic partition function.
The disorder law, smoothness, convexity, and every derivative bound are actual
physical definitions; no Gaussian convexity premise is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

abbrev SKGaussianSpace (n : ℕ) := EuclideanSpace ℝ (Edge n)

def skGaussianDisorderLinear (n : ℕ) : SKGaussianSpace n →L[ℝ] Couplings n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Edge n=>ℝ)).toContinuousLinearMap

def skGaussianParameterLinear (n : ℕ) : SKGaussianSpace n →L[ℝ] VectorParameter n :=
  ((skGaussianDisorderLinear n).prod 0).prod 0

theorem hasLaw_skGaussianDisorder (n : ℕ) :
    HasLaw (skGaussianDisorderLinear n) (couplingLaw n) (stdGaussian (SKGaussianSpace n)) := by
  refine ⟨(skGaussianDisorderLinear n).measurable.aemeasurable,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (skGaussianDisorderLinear n).measurable
    (WithLp.measurable_toLp 2 _)]
  change (couplingLaw n).map (fun x=>x)=couplingLaw n
  exact Measure.map_id

theorem normalizedCGF_comp_hasLaw {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {P : Measure Ω} {Q : Measure A} {Y : Ω → A} (hY : HasLaw Y Q P)
    (X : A → ℝ) (hX : Measurable X) :
    normalizedCGF P (fun sample=>X (Y sample))=normalizedCGF Q X := by
  have he : cgf (fun sample=>X (Y sample)) P=cgf X Q := by
    funext m
    unfold cgf mgf
    congr 1
    exact hY.integral_comp ((Real.measurable_exp.comp (hX.const_mul m)).aestronglyMeasurable)
  simp only [normalizedCGF,he]

theorem boundedPositiveJets_vectorTerminalPotential (n : ℕ) (β t : ℝ) :
    BoundedPositiveJets (fun p : VectorParameter n=>vectorTerminalPotential n β t p.1 p.2) := by
  refine ⟨contDiff_infty.mpr (fun N=>contDiff_vectorTerminalPotential_joint n β t N),?_⟩
  intro j hj
  obtain ⟨K,hK,hBound⟩ := exists_vectorTerminalPotential_joint_jet_bound n β t j
  exact ⟨K^j,pow_nonneg (zero_le_one.trans hK) j,hBound j hj (le_refl j)⟩

theorem skGaussianTerminal_eq_logPartition (n : ℕ) (β : ℝ) (z : SKGaussianSpace n) :
    vectorTerminalPotential n β 1 (skGaussianParameterLinear n z).1
      (skGaussianParameterLinear n z).2=logPartition n β (skGaussianDisorderLinear n z) := by
  change vectorTerminalPotential n β 1 (skGaussianDisorderLinear n z,0) 0=_
  rw [vectorTerminalPotential_one_time_zero]
  simp only [completedLogPartition,mul_zero,add_zero]

theorem boundedPositiveJets_logPartition_gaussian (n : ℕ) (β : ℝ) :
    BoundedPositiveJets (fun z : SKGaussianSpace n=>logPartition n β (skGaussianDisorderLinear n z)) := by
  have hh := (boundedPositiveJets_vectorTerminalPotential n β 1).comp_linear (skGaussianParameterLinear n)
  have he : ((fun p : VectorParameter n=>vectorTerminalPotential n β 1 p.1 p.2) ∘
      (skGaussianParameterLinear n))=(fun z=>logPartition n β (skGaussianDisorderLinear n z)) :=
    funext (skGaussianTerminal_eq_logPartition n β)
  rw [he] at hh
  exact hh

theorem convexOn_logPartition_gaussian (n : ℕ) (β : ℝ) :
    ConvexOn ℝ univ (fun z : SKGaussianSpace n=>logPartition n β (skGaussianDisorderLinear n z)) := by
  have hh := (convexOn_vectorRecursion_joint (trivialScheme 0) β 1 0).comp_linearMap
    (skGaussianParameterLinear n).toLinearMap
  have he : ((fun p : VectorParameter n=>vectorRecursion (trivialScheme 0) β 1 p.1 0 p.2) ∘
      (skGaussianParameterLinear n).toLinearMap)=(fun z=>logPartition n β (skGaussianDisorderLinear n z)) :=
    funext (skGaussianTerminal_eq_logPartition n β)
  rw [he] at hh
  simpa only [preimage_univ] using hh

theorem convexOn_normalizedLogPartitionMoment (n : ℕ) (β : ℝ) :
    ConvexOn ℝ univ (normalizedCGF (couplingLaw n) (logPartition n β)) := by
  have hh := convexOn_normalizedCGF_stdGaussian (boundedPositiveJets_logPartition_gaussian n β)
    (convexOn_logPartition_gaussian n β)
  have hcont := continuous_logPartition n β
  rw [normalizedCGF_comp_hasLaw (hasLaw_skGaussianDisorder n) _ hcont.measurable] at hh
  exact hh

theorem convexOn_normalizedEnergyMoment (n : ℕ) (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ univ (normalizedEnergyMoment n β) := by
  have hf := (boundedPositiveJets_logPartition_gaussian n β).const_mul β⁻¹
  have hc := (convexOn_logPartition_gaussian n β).smul (inv_nonneg.mpr hβ.le)
  have hf' : BoundedPositiveJets
      (fun z : SKGaussianSpace n=>energyFreeEnergy n β (skGaussianDisorderLinear n z)) := by
    simpa only [energyFreeEnergy,div_eq_mul_inv,mul_comm] using hf
  have hc' : ConvexOn ℝ univ
      (fun z : SKGaussianSpace n=>energyFreeEnergy n β (skGaussianDisorderLinear n z)) := by
    simpa only [smul_eq_mul,energyFreeEnergy,div_eq_mul_inv,mul_comm] using hc
  have hh := convexOn_normalizedCGF_stdGaussian hf' hc'
  have hmeas : Measurable (energyFreeEnergy n β) := by
    have hm := (continuous_logPartition n β).measurable
    exact hm.div_const β
  rw [normalizedCGF_comp_hasLaw (hasLaw_skGaussianDisorder n) _ hmeas] at hh
  exact hh

end QuantitativeFollowup
