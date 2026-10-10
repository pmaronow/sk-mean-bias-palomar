module
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section

/-! The covariance contractions in the path heat formula use the actual signed
derivative measures. The estimates below keep all diagonal atoms and control
simultaneous changes of the kernel and the derivative measure by total
variation. No replacement of a profile measure by a grid is involved. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace HexagonPaper
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

instance finiteVariationSignedMeasure (μ : SignedMeasure X) :
    IsFiniteMeasure μ.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

/-- The real total variation of a genuine signed derivative measure. -/
def signedTV (μ : SignedMeasure X) : ℝ := μ.variation.real univ

/-- Pairing a bounded continuous covariance kernel with a signed measure. -/
def signedContraction (f : X →ᵇ ℝ) (μ : SignedMeasure X) : ℝ :=
  ∫ᵛ x, f x ∂•μ

theorem signedTV_nonneg (μ : SignedMeasure X) : 0 ≤ signedTV μ :=
  measureReal_nonneg

theorem norm_signedContraction_le (f : X →ᵇ ℝ) (μ : SignedMeasure X) :
    ‖signedContraction f μ‖ ≤ ‖f‖ * signedTV μ := by
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := μ) (f := fun x => f x)
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))
  simpa [signedContraction, signedTV] using h

theorem signedContraction_sub_left (f g : X →ᵇ ℝ) (μ : SignedMeasure X) :
    signedContraction (f-g) μ = signedContraction f μ-signedContraction g μ := by
  exact VectorMeasure.integral_sub (f.integrable μ.variation) (g.integrable μ.variation)

theorem signedContraction_sub_right (f : X →ᵇ ℝ) (μ ν : SignedMeasure X) :
    signedContraction f (μ-ν) = signedContraction f μ-signedContraction f ν := by
  exact VectorMeasure.integral_sub_vectorMeasure
    (f.integrable μ.variation) (f.integrable ν.variation)

theorem norm_signedContraction_sub_le (f g : X →ᵇ ℝ) (μ ν : SignedMeasure X) :
    ‖signedContraction f μ-signedContraction g ν‖ ≤
      ‖f-g‖ * signedTV μ+‖g‖ * signedTV (μ-ν) := by
  have he : signedContraction f μ-signedContraction g ν =
      signedContraction (f-g) μ+signedContraction g (μ-ν) := by
    rw [signedContraction_sub_left,signedContraction_sub_right]
    ring
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_signedContraction_le _ _) (norm_signedContraction_le _ _))

/-- Total-variation continuity of the derivative measure is enough for
convergence of every covariance contraction, including diagonal terms. -/
theorem tendsto_signedContraction {ι : Type*} {l : Filter ι}
    (f : ι → X →ᵇ ℝ) (g : X →ᵇ ℝ) (μ : ι → SignedMeasure X)
    (ν : SignedMeasure X) (C : ℝ) (hC : 0 ≤ C)
    (hμ : ∀i,signedTV (μ i) ≤ C)
    (hf : Tendsto f l (𝓝 g))
    (hν : Tendsto (fun i => signedTV (μ i-ν)) l (𝓝 0)) :
    Tendsto (fun i => signedContraction (f i) (μ i)) l
      (𝓝 (signedContraction g ν)) := by
  have hn : Tendsto (fun i => ‖f i-g‖) l (𝓝 0) := by
    have hc : Tendsto (fun _ : ι => g) l (𝓝 g) := tendsto_const_nhds
    simpa only [sub_self,norm_zero] using (hf.sub hc).norm
  have hupper : Tendsto (fun i => ‖f i-g‖*C+‖g‖*signedTV (μ i-ν)) l (𝓝 0) := by
    simpa only [zero_mul,mul_zero,add_zero] using (hn.mul_const C).add
      (hν.const_mul ‖g‖)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hupper.eventually (Iio_mem_nhds hε)] with i hi
  rw [dist_eq_norm]
  have hb : ‖f i-g‖ * signedTV (μ i) ≤ ‖f i-g‖ * C :=
    mul_le_mul_of_nonneg_left (hμ i) (norm_nonneg (f i-g))
  have hb' : ‖f i-g‖ * signedTV (μ i)+‖g‖*signedTV (μ i-ν) ≤
      ‖f i-g‖ * C+‖g‖*signedTV (μ i-ν) :=
    add_le_add hb le_rfl
  exact (norm_signedContraction_sub_le (f i) g (μ i) ν).trans hb' |>.trans_lt hi

end HexagonPaper
