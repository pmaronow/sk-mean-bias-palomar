module
public import QuantitativePaper.VectorRecursion
public import FourPapersCommon.FiniteStateCovarianceScheduleTrace
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! One fixed standard Gaussian coordinate space realizes both the actual
vector field noise and the independent triangular disorder completion. The
projections are used at separate cascade levels, so their law is unchanged
when unused coordinates are retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1200000

abbrev VectorInterpolationInput (n : ℕ) := EuclideanSpace ℝ (Fin n ⊕ Option (Edge n))

def vectorInterpolationField (n : ℕ) (z : VectorInterpolationInput n) : Field n :=
  WithLp.toLp 2 (fun i=>z (.inl i))

def vectorInterpolationDisorder (n : ℕ) (z : VectorInterpolationInput n) : Couplings n×ℝ :=
  ((fun e=>z (.inr (.some e))),(1/Real.sqrt 2)*z (.inr .none))

theorem measurable_vectorInterpolationField (n : ℕ) : Measurable (vectorInterpolationField n) := by
  unfold vectorInterpolationField
  fun_prop

theorem measurable_vectorInterpolationDisorder (n : ℕ) : Measurable (vectorInterpolationDisorder n) := by
  unfold vectorInterpolationDisorder
  fun_prop

theorem stdGaussian_map_ofLp {I : Type*} [Fintype I] :
    (stdGaussian (EuclideanSpace ℝ I)).map WithLp.ofLp=
      Measure.pi (fun _ : I=>gaussianReal 0 1) := by
  rw [←map_pi_eq_stdGaussian,Measure.map_map (WithLp.measurable_ofLp 2 _)
    (WithLp.measurable_toLp 2 _)]
  change (Measure.pi (fun _ : I=>gaussianReal 0 1)).map id=_
  rw [Measure.map_id]

private theorem interpolation_pi_left (n : ℕ) :
    (Measure.pi (fun _ : Fin n⊕Option (Edge n)=>gaussianReal 0 1)).map
      (fun z i=>z (.inl i))=Measure.pi (fun _ : Fin n=>gaussianReal 0 1) := by
  have hs:=(measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n⊕Option (Edge n)=>gaussianReal 0 1)).map_eq
  have he:=(congrArg (fun P=>P.map Prod.fst) hs)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  simpa only [Function.comp_def,MeasurableEquiv.coe_sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi_apply,Measure.map_fst_prod,measure_univ,one_smul] using he

private theorem interpolation_pi_right (n : ℕ) :
    (Measure.pi (fun _ : Fin n⊕Option (Edge n)=>gaussianReal 0 1)).map
      (fun z i=>z (.inr i))=Measure.pi (fun _ : Option (Edge n)=>gaussianReal 0 1) := by
  have hs:=(measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n⊕Option (Edge n)=>gaussianReal 0 1)).map_eq
  have he:=(congrArg (fun P=>P.map Prod.snd) hs)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  simpa only [Function.comp_def,MeasurableEquiv.coe_sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi_apply,Measure.map_snd_prod,measure_univ,one_smul] using he

theorem stdGaussian_map_vectorInterpolationField (n : ℕ) :
    (stdGaussian (VectorInterpolationInput n)).map (vectorInterpolationField n)=fieldGaussian n := by
  have h:=congrArg (fun P=>P.map (fun z=>WithLp.toLp 2 z)) (interpolation_pi_left n)
  rw [Measure.map_map (WithLp.measurable_toLp 2 _) (by fun_prop)] at h
  have he : vectorInterpolationField n=(fun z=>WithLp.toLp 2 (fun i=>z (.inl i))) ∘ WithLp.ofLp := rfl
  rw [he,←Measure.map_map (by fun_prop) (WithLp.measurable_ofLp 2 _),stdGaussian_map_ofLp]
  exact h

private theorem interpolation_pi_option (n : ℕ) :
    (Measure.pi (fun _ : Option (Edge n)=>gaussianReal 0 1)).map
      (fun z=>(fun e=>z (.some e),z .none))=
      (couplingLaw n).prod (gaussianReal 0 1) := by
  let e:=MeasurableEquiv.piOptionEquivProd (fun _ : Option (Edge n)=>ℝ)
  have h:=Measure.pi_map_piOptionEquivProd (fun _ : Option (Edge n)=>gaussianReal 0 1)
  change (Measure.pi (fun _ : Option (Edge n)=>gaussianReal 0 1)).map e=_
  rw [←h,Measure.map_map (by fun_prop) (by fun_prop)]
  change ((couplingLaw n).prod (gaussianReal 0 1)).map id=_
  rw [Measure.map_id]

private theorem interpolation_completion_scale :
    (gaussianReal 0 1).map (fun x : ℝ=>(1/Real.sqrt 2)*x)=gaussianReal 0 (1/2) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.coe_injective
    simp only [NNReal.coe_mk,NNReal.coe_one,mul_one,NNReal.coe_div,
      NNReal.coe_ofNat,div_pow,one_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem stdGaussian_map_vectorInterpolationDisorder (n : ℕ) :
    (stdGaussian (VectorInterpolationInput n)).map (vectorInterpolationDisorder n)=completionLaw n := by
  let f : (Option (Edge n)→ℝ)→ Couplings n×ℝ:=
    fun z=>(fun e=>z (.some e),(1/Real.sqrt 2)*z .none)
  have hscale : ((couplingLaw n).prod (gaussianReal 0 1)).map
      (fun z : Couplings n×ℝ=>(z.1,(1/Real.sqrt 2)*z.2))=completionLaw n := by
    change ((couplingLaw n).prod (gaussianReal 0 1)).map
      (Prod.map id (fun x : ℝ=>(1/Real.sqrt 2)*x))=_
    rw [←Measure.map_prod_map (couplingLaw n) (gaussianReal 0 1) measurable_id
      (show Measurable (fun x : ℝ=>(1/Real.sqrt 2)*x) by fun_prop),
      Measure.map_id,interpolation_completion_scale]
    rfl
  have hf : (Measure.pi (fun _ : Option (Edge n)=>gaussianReal 0 1)).map f=completionLaw n := by
    have h:=congrArg (fun P=>P.map (fun z : Couplings n×ℝ=>(z.1,(1/Real.sqrt 2)*z.2)))
      (interpolation_pi_option n)
    rw [Measure.map_map (by fun_prop) (by fun_prop),hscale] at h
    exact h
  have hr:=congrArg (fun P=>P.map f) (interpolation_pi_right n)
  rw [Measure.map_map (by fun_prop) (by fun_prop),hf] at hr
  have he : vectorInterpolationDisorder n=
      (fun z : (Fin n⊕Option (Edge n)→ℝ)=>f (fun i=>z (.inr i))) ∘ WithLp.ofLp := rfl
  rw [he,←Measure.map_map (by fun_prop) (WithLp.measurable_ofLp 2 _),stdGaussian_map_ofLp]
  exact hr

end QuantitativePaper
