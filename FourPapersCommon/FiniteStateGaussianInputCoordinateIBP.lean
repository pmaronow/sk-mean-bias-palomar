module
public import FourPapersCommon.FiniteStateCascadeGenerators
public import Targets.CascadeFieldPi

@[expose] public section

/-! Genuine Gaussian integration by parts for an individual coordinate of
an actual normalized finite-state Gaussian step. Every weighted coordinate
integrability obligation is discharged from the actual smooth jet bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 128
variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianInput_coordinate_ibp
    (mass : ℝ) (L : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (F : FiniteStateField S→ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀H,‖fderiv ℝ F H‖≤C)
    (hB : ∀H,‖fderiv ℝ (fderiv ℝ F) H‖≤B)
    (H K : FiniteStateField S) (i : Fin (Fintype.card I)) :
    finiteStateGaussianInputMean mass (fun z=>F (H+L z))
      (fun z=>(finiteStateGaussianBasis I).repr z i*fderiv ℝ F (H+L z) K)=
    finiteStateGaussianInputMean mass (fun z=>F (H+L z))
      (fun z=>fderiv ℝ (fderiv ℝ F) (H+L z) (L (finiteStateGaussianBasis I i)) K+
        mass*fderiv ℝ F (H+L z) K*fderiv ℝ F (H+L z) (L (finiteStateGaussianBasis I i))) := by
  classical
  have hF1 : ContDiff ℝ 1 F:=hF.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ F):=hF.fderiv_right (by norm_num)
  have hLip : LipschitzWith C F:=lipschitzWith_of_nnnorm_fderiv_le hF1.differentiable_one
    (fun y=>NNReal.coe_le_coe.mp (hC y))
  let A:=fun y : Fin (Fintype.card I)→ℝ=>F (H+finiteStateGaussianCoordinateField L y)
  let A':=fun y : Fin (Fintype.card I)→ℝ=>
    fderiv ℝ F (H+finiteStateGaussianCoordinateField L y) (L (finiteStateGaussianBasis I i))
  let G:=fun y : Fin (Fintype.card I)→ℝ=>fderiv ℝ F (H+finiteStateGaussianCoordinateField L y) K
  let G':=fun y : Fin (Fintype.card I)→ℝ=>
    fderiv ℝ (fderiv ℝ F) (H+finiteStateGaussianCoordinateField L y)
      (L (finiteStateGaussianBasis I i)) K
  have hL : ‖L (finiteStateGaussianBasis I i)‖≤‖L‖:=by simpa using L.le_opNorm (finiteStateGaussianBasis I i)
  have hb (y) : |A y|≤|F H|+(C*‖L‖)*SpinGlass.Targets.l1 y := by
    have hs:=hLip.norm_sub_le (H+finiteStateGaussianCoordinateField L y) H
    rw [add_sub_cancel_left,Real.norm_eq_abs] at hs
    change |A y-F H|≤C*‖finiteStateGaussianCoordinateField L y‖ at hs
    calc
      _=|(A y-F H)+F H|:=by congr 1;ring
      _≤|A y-F H|+|F H|:=abs_add_le _ _
      _=|F H|+|A y-F H|:=add_comm _ _
      _≤|F H|+C*‖finiteStateGaussianCoordinateField L y‖:=add_le_add le_rfl hs
      _≤|F H|+C*(‖L‖*SpinGlass.Targets.l1 y):=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_finiteStateGaussianCoordinateField_le L y) C.2)
      _=_:=by ring
  have hAlip (y y') : |A y-A y'|≤(C*‖L‖)*SpinGlass.Targets.l1 (y-y') := by
    have hs:=hLip.norm_sub_le (H+finiteStateGaussianCoordinateField L y)
      (H+finiteStateGaussianCoordinateField L y')
    rw [Real.norm_eq_abs,add_sub_add_left_eq_sub,←map_sub] at hs
    exact hs.trans (by
      calc
        _≤C*(‖L‖*SpinGlass.Targets.l1 (y-y')):=
          mul_le_mul_of_nonneg_left (norm_finiteStateGaussianCoordinateField_le L (y-y')) C.2
        _=_:=by ring)
  have hbA (y) : |A' y|≤C*‖L‖ := by
    have hh:=(fderiv ℝ F (H+finiteStateGaussianCoordinateField L y)).le_opNorm (L (finiteStateGaussianBasis I i))
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul (hC _) hL (norm_nonneg _) C.2)
  have hbG (y) : |G y|≤C*‖K‖ := by
    have hh:=(fderiv ℝ F (H+finiteStateGaussianCoordinateField L y)).le_opNorm K
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  have hbG' (y) : |G' y|≤B*‖L‖*‖K‖ := by
    have h1:=(fderiv ℝ (fderiv ℝ F) (H+finiteStateGaussianCoordinateField L y)).le_opNorm
      (L (finiteStateGaussianBasis I i))
    have h2:=(fderiv ℝ (fderiv ℝ F) (H+finiteStateGaussianCoordinateField L y)
      (L (finiteStateGaussianBasis I i))).le_opNorm K
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right
      (h1.trans (mul_le_mul (hB _) hL (norm_nonneg _) B.2)) (norm_nonneg _))
  have hs (y : Fin (Fintype.card I)→ℝ) (r : ℝ) :
      HasDerivAt (fun b=>H+finiteStateGaussianCoordinateField L (y+b • Pi.single i 1))
        (L (finiteStateGaussianBasis I i)) r := by
    simpa only [map_add,map_smul,finiteStateGaussianCoordinateField_single,one_smul,id_eq,add_assoc] using
      (((hasDerivAt_id r).smul_const (L (finiteStateGaussianBasis I i))).const_add
        (H+finiteStateGaussianCoordinateField L y))
  have hAd (y : Fin (Fintype.card I)→ℝ) (r : ℝ) :
      HasDerivAt (fun b=>A (y+b • Pi.single i 1)) (A' (y+r • Pi.single i 1)) r:=
    hF1.differentiable_one.differentiableAt.hasFDerivAt.comp_hasDerivAt r (hs y r)
  have hGd (y : Fin (Fintype.card I)→ℝ) (r : ℝ) :
      HasDerivAt (fun b=>G (y+b • Pi.single i 1)) (G' (y+r • Pi.single i 1)) r := by
    have hd:=(hD.differentiable_one.differentiableAt.hasFDerivAt.clm_apply
      (hasFDerivAt_const K (H+finiteStateGaussianCoordinateField L (y+r • Pi.single i 1)))).comp_hasDerivAt r (hs y r)
    convert hd using 1
    · rfl
    · simp only [G',add_apply,ContinuousLinearMap.comp_apply,zero_apply,
        ContinuousLinearMap.flip_apply,map_zero,zero_add]
  have hAm : Measurable A:=(hF.continuous.comp
    (continuous_const.add (finiteStateGaussianCoordinateField L).continuous)).measurable
  have hA'm : Measurable A':=((hD.continuous.comp
    (continuous_const.add (finiteStateGaussianCoordinateField L).continuous)).clm_apply continuous_const).measurable
  have hGm : Measurable G:=((hD.continuous.comp
    (continuous_const.add (finiteStateGaussianCoordinateField L).continuous)).clm_apply continuous_const).measurable
  have hG'm : Measurable G':=(((hD.continuous_fderiv (by norm_num)).comp
    (continuous_const.add (finiteStateGaussianCoordinateField L).continuous)).clm_apply
      continuous_const |>.clm_apply continuous_const).measurable
  have hh:=SpinGlass.Targets.stein_tiltWeightPi (A:=A) (A':=A') (G:=G) (G':=G')
    (m:=mass) (v:=1) (C:=|F H|) (D:=(C:ℝ)*‖L‖) (L:=(C:ℝ)*‖L‖)
    (BA:=(C:ℝ)*‖L‖) (BG:=(C:ℝ)*‖K‖) (BG':=(B:ℝ)*‖L‖*‖K‖)
    i 0 (by positivity) (by positivity) hAm hA'm hGm hG'm hb hAlip hbA hbG hbG' hAd hGd
  have he (y : Fin (Fintype.card I)→ℝ) :
      H+L (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ _) y)=
        H+finiteStateGaussianCoordinateField L y := by
    simp [finiteStateGaussianCoordinateField_apply]
  have hcoord (y : Fin (Fintype.card I)→ℝ) :
      (finiteStateGaussianBasis I).repr
        (finiteStateGaussianCoordinateField (ContinuousLinearMap.id ℝ _) y) i=y i := by
    simp [finiteStateGaussianCoordinateField_apply,Pi.single_apply]
  simpa only [finiteStateGaussianInputMean,SpinGlass.Targets.pairedTiltMean,
    Real.sqrt_one,Pi.zero_apply,one_mul,zero_add,he,hcoord,A,A',G,G',mul_assoc] using hh

end FourPapersCommon
