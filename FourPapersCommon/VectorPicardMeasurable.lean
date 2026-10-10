module
public import FourPapersCommon.VectorIntegralPicard
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Measurability of the actual integral Picard solution with respect to a
merely measurable parameter. The solution is obtained as the pointwise limit
of genuine measurable Picard iterates. -/
noncomputable section
open Function MeasureTheory Set Filter Metric
open scoped NNReal Topology
namespace FourPapersCommon
namespace VectorIntegralPicard

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {T : ℝ} (hT : 0 ≤ T) (x0 : E) {L K : ℝ≥0}
  (f : Ω → ℝ → E → E) (hf : ∀ sample,IsBoundedVectorDrift (f sample) L K)

def parameterIterate (n : ℕ) (sample : Ω) : Curve hT x0 L :=
  (next hT (hf sample))^[n] default

theorem continuous_parameterIterate (n : ℕ) (sample : Ω) :
    Continuous (fun r => (parameterIterate hT x0 f hf n sample).compProj r) :=
  ODE.FunSpace.continuous_compProj _

theorem measurable_parameterIterate
    (hm : Measurable (fun p : (ℝ × E) × Ω => f p.2 p.1.1 p.1.2)) :
    ∀ n r,Measurable (fun sample => (parameterIterate hT x0 f hf n sample).compProj r) := by
  intro n
  induction n with
  | zero =>
    intro r
    exact measurable_const
  | succ n ih =>
    intro r
    have hi : Measurable (fun p : ℝ × Ω =>
        (parameterIterate hT x0 f hf n p.2).compProj p.1) :=
      measurable_uncurry_of_continuous_of_measurable
        (continuous_parameterIterate hT x0 f hf n) ih
    have harg : Measurable (fun p : ℝ × Ω =>
        ((p.1,(parameterIterate hT x0 f hf n p.2).compProj p.1),p.2)) :=
      (measurable_fst.prodMk hi).prodMk measurable_snd
    have hfi := hm.comp harg
    let u : ℝ := (projIcc (0 : ℝ) T hT r : ℝ)
    have hu : 0 ≤ u := (projIcc (0 : ℝ) T hT r).property.1
    have hmeas : Measurable (fun sample => ∫ s in (0 : ℝ)..u,
        f sample s ((parameterIterate hT x0 f hf n sample).compProj s)) := by
      simp_rw [intervalIntegral.integral_of_le hu]
      exact (hfi.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc 0 u))).measurable
    convert (measurable_const (a := x0)).add hmeas using 1
    funext sample
    unfold parameterIterate
    rw [Function.iterate_succ_apply']
    rfl

theorem tendsto_parameterIterate (r : ℝ) (sample : Ω) :
    Tendsto (fun n => (parameterIterate hT x0 f hf n sample).compProj r)
      atTop (𝓝 ((solution (h := x0) hT (hf sample)).compProj r)) := by
  let α : Curve hT x0 L := default
  let z : Curve hT x0 L := solution (h := x0) hT (hf sample)
  have hlimit : Tendsto (fun n : ℕ => ((K : ℝ)*T)^n/n.factorial*dist α z)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ)*T)).mul_const (dist α z)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hlimit
  have hh := dist_iterate_le hT (hf sample) α z n
  have hz := (solution_fixed (h := x0) hT (hf sample)).iterate n
  change ((next hT (hf sample))^[n] z) = z at hz
  rw [hz] at hh
  have he := ContinuousMap.dist_apply_le_dist
    (f := ODE.FunSpace.toContinuousMap ((next hT (hf sample))^[n] α))
    (g := ODE.FunSpace.toContinuousMap z) (projIcc (0 : ℝ) T hT r)
  exact he.trans hh

theorem measurable_solution_compProj
    (hm : Measurable (fun p : (ℝ × E) × Ω => f p.2 p.1.1 p.1.2)) (r : ℝ) :
    Measurable (fun sample => (solution (h := x0) hT (hf sample)).compProj r) :=
  measurable_of_tendsto_metrizable
    (fun n => measurable_parameterIterate hT x0 f hf hm n r)
    (tendsto_pi_nhds.mpr (tendsto_parameterIterate hT x0 f hf r))

theorem measurable_uncurry_solution_compProj
    (hm : Measurable (fun p : (ℝ × E) × Ω => f p.2 p.1.1 p.1.2)) :
    Measurable (fun p : ℝ × Ω => (solution (h := x0) hT (hf p.2)).compProj p.1) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun _ => ODE.FunSpace.continuous_compProj _)
    (measurable_solution_compProj hT x0 f hf hm)

end VectorIntegralPicard
end FourPapersCommon
