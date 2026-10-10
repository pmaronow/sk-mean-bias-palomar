module
public import QuantitativePaper.VectorProfileExpectedSource
public import FourPapersCommon.ExponentialBoundedLinear
public import FourPapersCommon.LinearDerivativeComposition

@[expose] public section

/-! Genuine scalar time multiplier calculus for the actual field generator.
Affine and quadratic time tests can therefore be integrated cell by cell. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellFieldGenerator_time_mul
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (F : VectorProfileCellParameter n×Field n→ℝ) (w : ℝ→ℝ)
    (a : VectorProfileCellParameter n) (x : Field n)
    (hF : ContDiffAt ℝ 2 F (a,x)) (hw : DifferentiableAt ℝ w a.1) :
    vectorProfileCellFieldGenerator s₀ s₁ β t i (fun z=>w z.1.1*F z) a x=
      deriv w a.1*F (a,x)+w a.1*vectorProfileCellFieldGenerator s₀ s₁ β t i F a x := by
  have hTime : DifferentiableAt ℝ (fun q=>F ((q,a.2),x)) a.1:=
    hF.differentiableAt (by norm_num) |>.comp a.1 (by fun_prop)
  have hSpace : ContDiffAt ℝ 2 (fun y=>F (a,y)) x:=hF.comp x (contDiffAt_const.prodMk contDiffAt_id)
  let L:=(w a.1) • ContinuousLinearMap.id ℝ ℝ
  have hFirst (v : Field n) :
      fderiv ℝ (fun y=>w a.1*F (a,y)) x v=w a.1*fderiv ℝ (fun y=>F (a,y)) x v:=
    fderiv_linear_postcomp L (fun y=>F (a,y)) x v (hSpace.differentiableAt (by norm_num))
  have hSecond (v : Field n) :
      fderiv ℝ (fderiv ℝ (fun y=>w a.1*F (a,y))) x v v=
        w a.1*fderiv ℝ (fderiv ℝ (fun y=>F (a,y))) x v v:=
    second_fderiv_linear_postcomp L (fun y=>F (a,y)) x v hSpace
  unfold vectorProfileCellFieldGenerator
  rw [deriv_fun_mul hw hTime,hFirst]
  simp only [hSecond,←Finset.mul_sum]
  ring

theorem exponentialSmoothOn_vectorProfile_time_coordinate (l u A B : ℝ)
    (hl : 0≤l) (hu : u≤1) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>z.1.1)
      (vectorProfileJointCylinder l u A B) := by
  let L:=(ContinuousLinearMap.fst ℝ ℝ (VectorProfileParameter n)).comp
    (ContinuousLinearMap.fst ℝ (VectorProfileCellParameter n) (Field n))
  apply exponentialSmoothOn_bounded_linear L _ 1 zero_le_one
  intro z hz
  change |z.1.1|≤1
  exact abs_le.mpr ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩

theorem exponentialSmoothOn_vectorProfile_affine_time_mul
    (F : VectorProfileCellParameter n×Field n→ℝ) (l u A B α δ : ℝ)
    (hf : ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (hl : 0≤l) (hu : u≤1) :
    ExponentialSmoothOn (fun z=> (α+δ*z.1.1)*F z) (vectorProfileJointCylinder l u A B) := by
  have hq:=exponentialSmoothOn_vectorProfile_time_coordinate (n:=n) l u A B hl hu
  have hw:=(ExponentialSmoothOn.const α _).add (hq.compCLM (δ • ContinuousLinearMap.id ℝ ℝ))
  exact hw.bilinear hf (ContinuousLinearMap.mul ℝ ℝ)

end QuantitativePaper
