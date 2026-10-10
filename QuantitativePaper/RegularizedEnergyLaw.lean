module
public import QuantitativePaper.RegularizedEnergyLogConcavity
public import FourPapersCommon.ExponentialSurvival
public import Mathlib.MeasureTheory.Integral.Prod

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! The actual independent exponential-regularized SK energy, its moments,
and the exact survival law used by the variance-sensitive tail proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1500000

 def regularizedEnergyLaw (n : ℕ) (β : ℝ) : Measure (Couplings n×ℝ) :=
  (couplingLaw n).prod (expMeasure β)
 def regularizedEnergyVariable (n : ℕ) (β : ℝ) (z : Couplings n×ℝ) : ℝ :=
  energyFreeEnergy n β z.1+z.2

 theorem regularizedEnergyLaw_probability (n : ℕ) (β : ℝ) (hβ : 0<β) :
    IsProbabilityMeasure (regularizedEnergyLaw n β) := by
  let _:=isProbabilityMeasure_expMeasure hβ
  unfold regularizedEnergyLaw
  infer_instance

 theorem continuous_regularizedEnergyVariable (n : ℕ) (β : ℝ) :
    Continuous (regularizedEnergyVariable n β) := by
  exact ((continuous_logPartition n β).div_const β |>.comp continuous_fst).add continuous_snd

 theorem memLp_regularizedEnergyVariable (n : ℕ) (β : ℝ) (hβ : 0<β) :
    MemLp (regularizedEnergyVariable n β) 2 (regularizedEnergyLaw n β) := by
  let _:=isProbabilityMeasure_expMeasure hβ
  exact ((memLp_two_energyFreeEnergy n β).comp_fst (expMeasure β)).add
    ((memLp_two_id_expMeasure β hβ).comp_snd (couplingLaw n))

 theorem integral_regularizedEnergyVariable (n : ℕ) (β : ℝ) (hβ : 0<β) :
    (∫z,regularizedEnergyVariable n β z ∂regularizedEnergyLaw n β)=
      (∫g,energyFreeEnergy n β g ∂couplingLaw n)+β⁻¹ := by
  let _:=isProbabilityMeasure_expMeasure hβ
  have hX:=((memLp_two_energyFreeEnergy n β).comp_fst (expMeasure β)).integrable one_le_two
  have hR:=((memLp_two_id_expMeasure β hβ).comp_snd (couplingLaw n)).integrable one_le_two
  simp only [id_eq] at hR
  change (∫z,energyFreeEnergy n β z.1+z.2 ∂(couplingLaw n).prod (expMeasure β))=_
  have hrint : (∫z : Couplings n×ℝ,z.2 ∂(couplingLaw n).prod (expMeasure β))=β⁻¹ := by
    have hh:=integral_fun_snd (μ:=couplingLaw n) (ν:=expMeasure β) (id : ℝ→ℝ)
    simpa only [id_eq,probReal_univ,one_smul,integral_id_expMeasure β hβ] using hh
  rw [integral_add hX hR,integral_fun_fst,hrint,probReal_univ,one_smul]

 theorem variance_regularizedEnergyVariable (n : ℕ) (β : ℝ) (hβ : 0<β) :
    variance (regularizedEnergyVariable n β) (regularizedEnergyLaw n β)=
      variance (energyFreeEnergy n β) (couplingLaw n)+β⁻¹^2 := by
  let _:=isProbabilityMeasure_expMeasure hβ
  change variance (fun z=>energyFreeEnergy n β z.1+id z.2) ((couplingLaw n).prod (expMeasure β))=_
  rw [variance_add_prod (memLp_two_energyFreeEnergy n β) (memLp_two_id_expMeasure β hβ),
    variance_id_expMeasure β hβ]

 theorem regularizedEnergyTail_eq_survival (n : ℕ) (β x : ℝ) (hβ : 0<β) :
    regularizedEnergyTail n β x=
      (regularizedEnergyLaw n β).real {z | x≤regularizedEnergyVariable n β z} := by
  let _:=regularizedEnergyLaw_probability n β hβ
  let _:=isProbabilityMeasure_expMeasure hβ
  let E : Set (Couplings n×ℝ):={z | x≤regularizedEnergyVariable n β z}
  have hE : MeasurableSet E := (continuous_regularizedEnergyVariable n β).measurable measurableSet_Ici
  have hi : Integrable (E.indicator (fun _=>(1:ℝ))) (regularizedEnergyLaw n β):=
    (integrable_const 1).indicator hE
  rw [←integral_indicator_one hE]
  change regularizedEnergyTail n β x=∫z,E.indicator (fun _=>(1:ℝ)) z
    ∂(couplingLaw n).prod (expMeasure β)
  rw [integral_prod _ hi]
  unfold regularizedEnergyTail regularizedEnergyTailKernel
  apply integral_congr_ae
  filter_upwards with g
  have he : (fun r=>E.indicator (fun _=>(1:ℝ)) (g,r))=
      (Ici (x-energyFreeEnergy n β g)).indicator (fun _=>(1:ℝ)) := by
    funext r
    simp only [Set.indicator_apply,mem_setOf_eq,E,regularizedEnergyVariable,mem_Ici]
    have hh : x≤energyFreeEnergy n β g+r ↔ x-energyFreeEnergy n β g≤r := by constructor <;> intro hh <;> linarith
    simp only [hh]
  rw [he]
  change _=∫r,(Ici (x-energyFreeEnergy n β g)).indicator (1 : ℝ→ℝ) r ∂expMeasure β
  rw [integral_indicator_one measurableSet_Ici,real_expMeasure_Ici β hβ]

 theorem energyUpperTail_le_regularizedEnergyTail (n : ℕ) (β x : ℝ) (hβ : 0<β) :
    (couplingLaw n).real {g | x≤energyFreeEnergy n β g}≤regularizedEnergyTail n β x := by
  let E : Set (Couplings n):={g | x≤energyFreeEnergy n β g}
  have hc : Continuous (energyFreeEnergy n β) := (continuous_logPartition n β).div_const β
  have hE : MeasurableSet E:=hc.measurable measurableSet_Ici
  rw [←integral_indicator_one hE]
  apply integral_mono_ae ((integrable_const (1:ℝ)).indicator hE)
    (integrable_regularizedEnergyTailKernel n β x hβ.le)
  filter_upwards with g
  by_cases hg : g∈E
  · simp only [Set.indicator_of_mem hg]
    have hx : x-energyFreeEnergy n β g≤0 := by exact sub_nonpos.mpr hg
    simp [regularizedEnergyTailKernel,max_eq_right hx]
  · simp only [Set.indicator_of_notMem hg]
    exact (regularizedEnergyTailKernel_pos n β x g).le

end QuantitativePaper
