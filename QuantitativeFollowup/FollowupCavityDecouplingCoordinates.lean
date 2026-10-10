module
public import QuantitativeFollowup.FollowupCavityRestProcess
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! Concrete old-coordinate and final-coordinate projections for the physical
u=0 cavity model. The driving Gaussian splits into its actual product law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper Paper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavityRestCouplingEmbedding (n : ℕ) : AnisotropicCouplingIndex n↪AnisotropicCouplingIndex (n+1) where
  toFun e:=⟨(e.1.1.castSucc,e.1.2.castSucc),by exact_mod_cast e.2⟩
  inj' :=by intro e f h;apply Subtype.ext;apply Prod.ext <;> apply Fin.castSucc_injective <;>
    first | exact congrArg (fun e=>e.1.1) h | exact congrArg (fun e=>e.1.2) h

@[simp] theorem cavityRestCouplingEmbedding_fst (n : ℕ) (e : AnisotropicCouplingIndex n) :
    (cavityRestCouplingEmbedding n e).1.1=e.1.1.castSucc := rfl
@[simp] theorem cavityRestCouplingEmbedding_snd (n : ℕ) (e : AnisotropicCouplingIndex n) :
    (cavityRestCouplingEmbedding n e).1.2=e.1.2.castSucc := rfl

def cavityRestDisorderProjection (n : ℕ) : AnisotropicDisorder (n+1)→L[ℝ]AnisotropicDisorder n :=
  LinearMap.toContinuousLinearMap
    {toFun:=fun g=>WithLp.toLp 2 (fun e=>g (cavityRestCouplingEmbedding n e))
     map_add':=by intro x y;ext e;rfl
     map_smul':=by intro c x;ext e;rfl}

@[simp] theorem cavityRestDisorderProjection_apply (n : ℕ) (g : AnisotropicDisorder (n+1)) (e : AnisotropicCouplingIndex n) :
    cavityRestDisorderProjection n g e=g (cavityRestCouplingEmbedding n e) := rfl

def cavityRestFieldProjection (n : ℕ) : QuantitativePaper.Field (n+1)→L[ℝ]QuantitativePaper.Field n :=
  LinearMap.toContinuousLinearMap
    {toFun:=fun x=>WithLp.toLp 2 (fun i=>x i.castSucc)
     map_add':=by intro x y;ext i;rfl
     map_smul':=by intro c x;ext i;rfl}

@[simp] theorem cavityRestFieldProjection_apply (n : ℕ) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    cavityRestFieldProjection n x i=x i.castSucc := rfl

def cavityFieldSplit (n : ℕ) : QuantitativePaper.Field (n+1)→QuantitativePaper.Field n×ℝ:=
  fun x=>(cavityRestFieldProjection n x,x (Fin.last n))

theorem measurable_cavityFieldSplit (n : ℕ) : Measurable (cavityFieldSplit n) :=
  (cavityRestFieldProjection n).measurable.prodMk (show Measurable (fun x : QuantitativePaper.Field (n+1)=>x (Fin.last n)) from by fun_prop)

theorem stdGaussian_map_cavityFieldSplit (n : ℕ) :
    (stdGaussian (QuantitativePaper.Field (n+1))).map (cavityFieldSplit n)=
      (stdGaussian (QuantitativePaper.Field n)).prod (gaussianReal 0 1) := by
  let e:=MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1)=>ℝ) (Fin.last n)
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1)=>gaussianReal 0 1) (Fin.last n)).map_eq
  have hh : cavityFieldSplit n∘(WithLp.toLp 2 : (Fin (n+1)→ℝ)→QuantitativePaper.Field (n+1))=
      Prod.swap∘Prod.map (id : ℝ→ℝ) (WithLp.toLp 2 : (Fin n→ℝ)→QuantitativePaper.Field n)∘e := by
    funext z
    apply Prod.ext
    · ext i
      change z i.castSucc=z ((Fin.last n).succAbove i)
      rw [Fin.succAbove_last]
    · rfl
  rw [←map_pi_eq_stdGaussian,Measure.map_map (measurable_cavityFieldSplit n) (by fun_prop),hh]
  change Measure.map ((Prod.swap∘Prod.map (id : ℝ→ℝ) (WithLp.toLp 2 : (Fin n→ℝ)→QuantitativePaper.Field n))∘e) _=_
  rw [←Measure.map_map (by fun_prop) e.measurable,he]
  rw [←Measure.map_map measurable_swap (by fun_prop),←Measure.map_prod_map _ _ measurable_id (by fun_prop)]
  simp only [Measure.map_id,map_pi_eq_stdGaussian,Measure.prod_swap]

theorem cavityRestFieldProjection_noise_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (z : QuantitativePaper.Field (n+1)) :
    cavityRestFieldProjection n (anisotropicNoiseMap (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) z)=
      anisotropicNoiseMap (followupCavityRestSpinModel n β ρ hβ hρ) (cavityRestFieldProjection n z) := by
  ext i
  simp only [cavityRestFieldProjection_apply,anisotropicNoiseMap_apply,followupCavitySpinModel_variance_rest,
    followupCavityRestSpinModel]

theorem cavityLastNoise_zero (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (z : QuantitativePaper.Field (n+1)) :
    anisotropicNoiseMap (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) z (Fin.last n)=
      Real.sqrt (followupCavityD n β ρ)*z (Fin.last n) := by
  rw [anisotropicNoiseMap_apply,followupCavitySpinModel_variance_last,followupCavityB_zero]

end QuantitativeFollowup
