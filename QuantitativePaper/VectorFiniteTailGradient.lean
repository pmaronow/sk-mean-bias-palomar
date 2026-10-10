module
public import QuantitativePaper.VectorTailCellIdentification
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

@[expose] public section

/-! Literal finite restarted-tail gradients, with actual joint measurability
and dimension-only norm/Lipschitz bounds. Measurability is derived by genuine
spatial difference quotients, without assuming a parameter derivative law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 400000

theorem measurable_vectorTailRecursion_parameter {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (j : ℕ) :
    Measurable (fun z : ℝ×VectorParameter n => vectorTailRecursion s β t z.1 z.2.1 j z.2.2) := by
  induction j with
  | zero =>
    exact (contDiff_vectorTerminalPotential_joint n β t 0).continuous.measurable.comp measurable_snd
  | succ j ih =>
    let v := fun q : ℝ => (1-t)*(β^2*(max q (s.q (k+2-j))-max q (s.q (k+1-j))))
    have hs : Measurable (fun z : (ℝ×VectorParameter n)×Field n =>
        (z.1.1,(z.1.2.1,fieldShift (v z.1.1) z.1.2.2 z.2))) := by
      dsimp only [v,fieldShift]
      fun_prop
    have hm := ih.comp hs
    by_cases h0 : s.m (k+1-j)=0
    · simpa only [vectorTailRecursion,vectorColeHopfStep,h0,ite_true,v,Function.comp_def] using
        (hm.stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable
    · have hE := Real.measurable_exp.comp ((measurable_const (a := s.m (k+1-j))).mul hm)
      have hI := (hE.stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable
      simpa only [vectorTailRecursion,vectorColeHopfStep,ite_eq_right h0,vectorStepPartition,v,
        Function.comp_def,Pi.mul_apply] using
        (Real.measurable_log.comp hI).div_const (s.m (k+1-j))

def vectorFiniteTailGradient {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) : Field n :=
  gradient (vectorTailRecursion s β t q p (k+2)) x

theorem vectorFiniteTailGradient_eq_magnetization {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    vectorFiniteTailGradient s β t q p x=
      vectorMagnetization (vectorClampedScheme s q q.property) β t p (k+2) x := by
  rw [vectorFiniteTailGradient,vectorTailRecursion_eq_clamped s β t q q.property p le_rfl,
    ←vectorMagnetization_eq_gradient]

theorem norm_vectorFiniteTailGradient_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    ‖vectorFiniteTailGradient s β t q p x‖ ≤ Real.sqrt (n : ℝ) := by
  rw [vectorFiniteTailGradient_eq_magnetization]
  exact norm_vectorMagnetization_le_sqrt _ β t p _ x

theorem vectorFiniteTailGradient_lipschitz {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (q : Paper.Overlap) (p : Couplings n×ℝ) :
    LipschitzWith (n : ℝ≥0) (vectorFiniteTailGradient s β t q p) := by
  have he : vectorFiniteTailGradient s β t q p=
      vectorMagnetization (vectorClampedScheme s q q.property) β t p (k+2) :=
    funext (vectorFiniteTailGradient_eq_magnetization s β t q p)
  rw [he]
  exact vectorMagnetization_lipschitz _ β t p _

theorem measurable_vectorFiniteTailGradient {n k : ℕ} (s : RSBScheme k) (β t : ℝ) :
    Measurable (fun z : Paper.Overlap×VectorParameter n =>
      vectorFiniteTailGradient s β t z.1 z.2.1 z.2.2) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  let h := fun j : ℕ => (1 : ℝ)/((j : ℝ)+1)
  have hpos (j : ℕ) : 0 < h j := by dsimp only [h];positivity
  have hlim : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hpos⟩
  let Q := fun j : ℕ => fun z : Paper.Overlap×VectorParameter n =>
    (h j)⁻¹*(vectorTailRecursion s β t z.1 z.2.1 (k+2)
      (z.2.2+h j • EuclideanSpace.single i (1 : ℝ))-
      vectorTailRecursion s β t z.1 z.2.1 (k+2) z.2.2)
  have hQ (j : ℕ) : Measurable (Q j) := by
    have h₁ := (measurable_vectorTailRecursion_parameter s β t (k+2)).comp
      (show Measurable (fun z : Paper.Overlap×VectorParameter n =>
        ((z.1 : ℝ),(z.2.1,z.2.2+h j • EuclideanSpace.single i (1 : ℝ)))) from by fun_prop)
    have h₀ := (measurable_vectorTailRecursion_parameter s β t (k+2)).comp
      (show Measurable (fun z : Paper.Overlap×VectorParameter n => ((z.1 : ℝ),z.2)) from by fun_prop)
    exact measurable_const.mul (h₁.sub h₀)
  apply measurable_of_tendsto_metrizable hQ
  apply tendsto_pi_nhds.mpr
  intro z
  have hs : ContDiff ℝ 2 (vectorTailRecursion s β t z.1 z.2.1 (k+2)) := by
    rw [vectorTailRecursion_eq_clamped s β t z.1 z.1.property z.2.1 le_rfl]
    exact (contDiff_vectorRecursion_field _ β t _ _).of_le (by simp)
  have hd := hasDerivAt_on_affine_line (vectorTailRecursion s β t z.1 z.2.1 (k+2)) hs
    z.2.2 (EuclideanSpace.single i (1 : ℝ)) 0
  have hh := hd.tendsto_slope_zero_right.comp hlim
  change Tendsto (fun j => Q j z) atTop
    (𝓝 ((gradient (vectorTailRecursion s β t z.1 z.2.1 (k+2)) z.2.2) i))
  rw [gradient_euclidean_coordinate]
  simpa only [Q,zero_add,zero_smul,add_zero,smul_eq_mul,
    Function.comp_def] using hh

end QuantitativePaper
