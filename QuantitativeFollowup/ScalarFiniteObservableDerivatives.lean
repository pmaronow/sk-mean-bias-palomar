module
public import QuantitativeFollowup.ScalarFiniteDensityScores
public import QuantitativeFollowup.ScalarProcessContinuity
public import FRSB.OptimalCurvatureMoment
public import FRSB.UniformSpatialRegularity

@[expose] public section

/-! Actual first and second spatial derivatives of the squared gradient
observable on a retained finite history. These are the literal derivatives
used in Step 3 of the scalar transport response, including observations at
zero, one, or repeated nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarFiniteGradientSquare (s : RSBScheme k) (β : ℝ) (p : Fin (k+3))
    (x : QuantitativePaper.Field (k+3)) : ℝ :=
  Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 p,x p)^2

theorem contDiff_scalarFiniteGradientSquare (s : RSBScheme k) (β : ℝ) (p : Fin (k+3)) :
    ContDiff ℝ ∞ (scalarFiniteGradientSquare s β p) :=
  ((Paper.contDiff_parisiGradient_spatial β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 p)).comp
      (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p).contDiff).pow 2

theorem hasFDerivAt_scalarFiniteHistoryGradient (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    HasFDerivAt (fun y : QuantitativePaper.Field (k+3)=>Paper.parisiGradient β
      (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,y p))
      (Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 p,x p) •
        PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p) x := by
  have hd := (Paper.hasDerivAt_parisiGradient_spatial_all β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 p) (x p)).hasFDerivAt.comp x
      (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p).hasFDerivAt
  convert! hd using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,PiLp.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  ring

theorem scalarFiniteGradientSquare_first (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) (x v : QuantitativePaper.Field (k+3)) :
    fderiv ℝ (scalarFiniteGradientSquare s β p) x v=
      2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
        Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*v p := by
  have hd := (hasFDerivAt_scalarFiniteHistoryGradient s β p x).pow 2
  have hh := congrArg (fun D : QuantitativePaper.Field (k+3)→L[ℝ]ℝ=>D v) hd.fderiv
  simp only [smul_apply,smul_eq_mul,PiLp.proj_apply] at hh
  convert! hh using 1 <;> simp only [Nat.cast_ofNat,pow_one] <;> ring

theorem hasFDerivAt_scalarFiniteHistoryHessian (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    HasFDerivAt (fun y : QuantitativePaper.Field (k+3)=>Paper.parisiHessian β
      (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,y p))
      (FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3
        (FRSB.forwardSchemeTime s 1 p) (x p) •
        PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p) x := by
  have hscalar : HasDerivAt (fun y=>Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 p,y))
      (FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3
        (FRSB.forwardSchemeTime s 1 p) (x p)) (x p) := by
    simpa only [show (1:ℕ)+1=2 by norm_num,show (1:ℕ)+2=3 by norm_num,
      FRSB.parisiSpatialJet_two] using
      FRSB.hasDerivAt_parisiSpatialJet_succ β (Paper.parisiSchemeMeasure s) 1
        (FRSB.forwardSchemeTime s 1 p) (x p)
  have hd := hscalar.hasFDerivAt.comp x (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p).hasFDerivAt
  convert! hd using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,PiLp.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  ring

theorem scalarFiniteGradientSquare_second (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) (x u v : QuantitativePaper.Field (k+3)) :
    vectorHessian (scalarFiniteGradientSquare s β p) x u v=
      (2*Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)^2+
        2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
          FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3 (FRSB.forwardSchemeTime s 1 p) (x p))*u p*v p := by
  have hl := hasFDerivAt_directional_field (scalarFiniteGradientSquare s β p)
    ((contDiff_scalarFiniteGradientSquare s β p).of_le (by simp)) x v
  rw [show (fun y=>fderiv ℝ (scalarFiniteGradientSquare s β p) y v)=
      (fun y=>2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,y p)*
        Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,y p)*v p) from
      funext fun y=>scalarFiniteGradientSquare_first s β p y v] at hl
  have hr := (((hasFDerivAt_scalarFiniteHistoryGradient s β p x).const_mul 2).mul
    (hasFDerivAt_scalarFiniteHistoryHessian s β p x)).mul_const (v p)
  have hh := congrArg (fun D : QuantitativePaper.Field (k+3)→L[ℝ]ℝ=>D u) (hl.unique hr)
  simp only [ContinuousLinearMap.flip_apply,add_apply,smul_apply,smul_eq_mul,PiLp.proj_apply] at hh
  rw [hh]
  ring

theorem norm_scalarFiniteGradientSquare_le_one (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    ‖scalarFiniteGradientSquare s β p x‖≤1 := by
  have h := Paper.norm_parisiGradient_le_one β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 p,x p)
  simpa only [scalarFiniteGradientSquare,norm_pow,one_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2

end QuantitativeFollowup
