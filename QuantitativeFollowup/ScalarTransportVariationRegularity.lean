module
public import QuantitativeFollowup.ScalarTransportNodeVariation
public import FRSB.UniformSpatialRegularity
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Genuine joint field-jet continuity and uniform future bounds for the
actual transported potential response. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace QuantitativeFollowup
open FourPapersCommon
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def scalarTransportFutureSquareSpatial (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q r : Paper.Overlap) (x : ℝ) : ℝ :=
  scalarFutureSquareDerivativeExtended β (scalarTransportMeasure μ φ u)
    (scalarLevelTransport φ u q) (scalarLevelTransport φ u r) x

theorem continuous_parisiSpatialJet_measure_joint_succ (β : ℝ) (j : ℕ) :
    Continuous (fun z : Paper.ParisiMeasure×(ℝ×ℝ)=>FRSB.parisiSpatialJet β z.1 (j+1) z.2.1 z.2.2) := by
  have hF : Continuous (fun z : Paper.ParisiMeasure×(ℝ×ℝ)=>
      bcfSpatialDerivative (parisiGradientBCF β z.1) j) :=
    (FRSB.continuous_spatialDerivativeBCF β j).comp continuous_fst
  have ht : Continuous (fun z : Paper.ParisiMeasure×(ℝ×ℝ)=>projIcc 0 1 zero_le_one z.2.1) :=
    (continuous_projIcc (a:=(0:ℝ)) (b:=1) (h:=zero_le_one)).comp
      (continuous_fst.comp continuous_snd)
  have hx : Continuous (fun z : Paper.ParisiMeasure×(ℝ×ℝ)=>z.2.2) :=
    continuous_snd.comp continuous_snd
  have hc : Continuous (fun z : Paper.ParisiMeasure×(ℝ×ℝ)=>
      bcfSpatialDerivative (parisiGradientBCF β z.1) j (projIcc 0 1 zero_le_one z.2.1,z.2.2)) :=
    continuous_eval.comp (hF.prodMk (ht.prodMk hx))
  simpa only [FRSB.parisiSpatialJet,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,
    Nat.add_sub_cancel,parisiSlabExtend] using hc

theorem norm_parisiSpatialJet_three_uniform (β : ℝ) (μ : Paper.ParisiMeasure) (t x : ℝ) :
    ‖FRSB.parisiSpatialJet β μ 3 t x‖ ≤ FRSB.uniformSpatialConstant β 2 := by
  exact (FRSB.norm_parisiSpatialJet_succ_le β μ 2 t x).trans
    (FRSB.norm_spatialDerivativeBCF_le_uniform β μ 2)

theorem scalarTransportFutureSquare_norm_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q r : Paper.Overlap) (x : ℝ) :
    ‖scalarTransportFutureSquare β μ φ u q r x‖ ≤ 1 := by
  unfold scalarTransportFutureSquare scalarFutureSquareExtended
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=canonicalWienerMeasure)
      (.of_forall fun W=>by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (Paper.norm_parisiGradient_le_one β _ _))

theorem scalarTransportFutureSquareSpatial_norm_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q r : Paper.Overlap) (x : ℝ) :
    ‖scalarTransportFutureSquareSpatial β μ φ u q r x‖ ≤ 2*Real.exp (β^2) := by
  unfold scalarTransportFutureSquareSpatial scalarFutureSquareDerivativeExtended
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=canonicalWienerMeasure)
      (.of_forall fun W=>scalarFutureSquareDerivativeExtended_integrand_bound β _ _ _ x W)

theorem continuous_scalarTransportFutureSquare_joint (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>
      scalarTransportFutureSquare β μ φ z.1.1 z.2.1 z.2.2 z.1.2) := by
  have hμ : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>scalarTransportMeasure μ φ z.1.1) :=
    (continuous_scalarTransportMeasure φ).comp (continuous_const.prodMk (continuous_fst.comp continuous_fst))
  have hq : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>scalarLevelTransport φ z.1.1 z.2.1) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  have hr : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>scalarLevelTransport φ z.1.1 z.2.2) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  have hx : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>z.1.2) :=
    continuous_snd.comp continuous_fst
  have harg : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>
      (scalarTransportMeasure μ φ z.1.1,(scalarLevelTransport φ z.1.1 z.2.1,
        (scalarLevelTransport φ z.1.1 z.2.2,z.1.2))) : _→ScalarFutureParameters) :=
    hμ.prodMk (hq.prodMk (hr.prodMk hx))
  simpa only [scalarTransportFutureSquare,Function.comp_def] using (continuous_scalarFutureSquareExtended β).comp harg

theorem continuous_scalarTransportFutureSquareSpatial_joint (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>
      scalarTransportFutureSquareSpatial β μ φ z.1.1 z.2.1 z.2.2 z.1.2) := by
  have hμ : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>scalarTransportMeasure μ φ z.1.1) :=
    (continuous_scalarTransportMeasure φ).comp (continuous_const.prodMk (continuous_fst.comp continuous_fst))
  have hq : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>scalarLevelTransport φ z.1.1 z.2.1) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  have hr : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>scalarLevelTransport φ z.1.1 z.2.2) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  have hx : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>z.1.2) :=
    continuous_snd.comp continuous_fst
  have harg : Continuous (fun z : (ℝ×ℝ)×(Paper.Overlap×Paper.Overlap)=>
      (scalarTransportMeasure μ φ z.1.1,(scalarLevelTransport φ z.1.1 z.2.1,
        (scalarLevelTransport φ z.1.1 z.2.2,z.1.2))) : _→ScalarFutureParameters) :=
    hμ.prodMk (hq.prodMk (hr.prodMk hx))
  simpa only [scalarTransportFutureSquareSpatial,Function.comp_def] using
    (continuous_scalarFutureSquareDerivativeExtended β hβ).comp harg

theorem hasDerivAt_scalarTransportFutureSquare_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| * L < 1) (q r : Paper.Overlap) (hqr : q ≤ r) (x : ℝ) :
    HasDerivAt (scalarTransportFutureSquare β μ φ u q r)
      (scalarTransportFutureSquareSpatial β μ φ u q r x) x := by
  have ho : (scalarLevelTransport φ u q:ℝ) ≤ scalarLevelTransport φ u r :=
    (strictMono_scalarLevelTransport φ L hφ h0 h1 u hu).monotone hqr
  have hd:=hasDerivAt_scalarFutureSquare β hβ (scalarTransportMeasure μ φ u)
    (scalarLevelTransport φ u q) (scalarLevelTransport φ u r) ho x
  have he : scalarTransportFutureSquare β μ φ u q r=
      scalarFutureSquare β (scalarTransportMeasure μ φ u)
        (scalarLevelTransport φ u q) (scalarLevelTransport φ u r) ho := by
    funext y
    exact scalarFutureSquareExtended_eq β _ _ _ ho y
  rw [he]
  simpa only [scalarTransportFutureSquareSpatial,
    scalarFutureSquareDerivativeExtended_eq β _ _ _ ho] using hd

end QuantitativeFollowup
