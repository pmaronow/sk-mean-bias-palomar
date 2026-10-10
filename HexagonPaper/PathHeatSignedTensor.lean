module
public import HexagonPaper.PathHeatSignedContractions
public import Mathlib.MeasureTheory.VectorMeasure.Prod

@[expose] public section

/-! Genuine tensor products of finite signed derivative measures. Total
variation estimates give continuity without dropping any diagonal atoms. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def pathHeatSignedTensor (S : SignedMeasure X) (T : SignedMeasure Y) : SignedMeasure (X×Y) :=
  S.prod T (ContinuousLinearMap.lsmul ℝ ℝ)

theorem pathHeatSignedTensor_apply (S : SignedMeasure X) (T : SignedMeasure Y)
    (s : Set X) (t : Set Y) : pathHeatSignedTensor S T (s×ˢt)=S s*T t := by
  simp only [pathHeatSignedTensor,VectorMeasure.prod_apply,
    ContinuousLinearMap.lsmul_apply,smul_eq_mul]

theorem pathHeatSignedTensor_sub_left (S U : SignedMeasure X) (T : SignedMeasure Y) :
    pathHeatSignedTensor (S-U) T=pathHeatSignedTensor S T-pathHeatSignedTensor U T := by
  apply VectorMeasure.prod_eq_of_forall_apply_prod
  intro s t hs ht
  simp only [VectorMeasure.sub_apply,pathHeatSignedTensor_apply,
    ContinuousLinearMap.lsmul_apply,smul_eq_mul,sub_mul]

theorem pathHeatSignedTensor_sub_right (S : SignedMeasure X) (T U : SignedMeasure Y) :
    pathHeatSignedTensor S (T-U)=pathHeatSignedTensor S T-pathHeatSignedTensor S U := by
  apply VectorMeasure.prod_eq_of_forall_apply_prod
  intro s t hs ht
  simp only [VectorMeasure.sub_apply,pathHeatSignedTensor_apply,
    ContinuousLinearMap.lsmul_apply,smul_eq_mul,mul_sub]

theorem signedTV_add_le (S T : SignedMeasure X) :
    signedTV (S+T)≤signedTV S+signedTV T := by
  have h := ENNReal.toReal_mono
    (measure_ne_top (S.variation+T.variation) univ)
    (VectorMeasure.variation_add_le (μ:=S) (ν:=T) univ)
  simpa only [signedTV,Measure.real,Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top S.variation univ) (measure_ne_top T.variation univ)] using h

theorem signedTV_pathHeatSignedTensor_le (S : SignedMeasure X) (T : SignedMeasure Y) :
    signedTV (pathHeatSignedTensor S T)≤signedTV S*signedTV T := by
  have hv : (pathHeatSignedTensor S T).variation≤S.variation.prod T.variation := by
    simpa only [pathHeatSignedTensor,enorm_eq_nnnorm,
      show ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ→L[ℝ]ℝ→L[ℝ]ℝ)‖₊=1 from
        Subtype.ext (ContinuousLinearMap.opNorm_lsmul (𝕜:=ℝ) (R:=ℝ) (E:=ℝ)),
      ENNReal.coe_one,one_smul] using
        (VectorMeasure.variation_prod_le (μ:=S) (ν:=T)
          (B:=ContinuousLinearMap.lsmul ℝ ℝ))
  have h := ENNReal.toReal_mono (measure_ne_top (S.variation.prod T.variation) univ) (hv univ)
  rw [←univ_prod_univ,Measure.prod_prod] at h
  simpa only [signedTV,Measure.real,ENNReal.toReal_mul,univ_prod_univ] using h

theorem signedTV_pathHeatSignedTensor_sub_le
    (S U : SignedMeasure X) (T V : SignedMeasure Y) :
    signedTV (pathHeatSignedTensor S T-pathHeatSignedTensor U V)≤
      signedTV S*signedTV (T-V)+signedTV (S-U)*signedTV V := by
  have he : pathHeatSignedTensor S T-pathHeatSignedTensor U V=
      pathHeatSignedTensor S (T-V)+pathHeatSignedTensor (S-U) V := by
    rw [pathHeatSignedTensor_sub_right,pathHeatSignedTensor_sub_left]
    abel
  rw [he]
  exact (signedTV_add_le _ _).trans
    (add_le_add (signedTV_pathHeatSignedTensor_le _ _) (signedTV_pathHeatSignedTensor_le _ _))

theorem tendsto_pathHeatSignedTensor_TV {A : Type*} {l : Filter A}
    (S : A→SignedMeasure X) (U : SignedMeasure X)
    (T : A→SignedMeasure Y) (V : SignedMeasure Y) (C : ℝ)
    (hS : ∀i,signedTV (S i)≤C)
    (hSU : Tendsto (fun i=>signedTV (S i-U)) l (𝓝 0))
    (hTV : Tendsto (fun i=>signedTV (T i-V)) l (𝓝 0)) :
    Tendsto (fun i=>signedTV (pathHeatSignedTensor (S i) (T i)-pathHeatSignedTensor U V))
      l (𝓝 0) := by
  apply squeeze_zero (fun _=>ENNReal.toReal_nonneg)
    (fun i=>(signedTV_pathHeatSignedTensor_sub_le (S i) U (T i) V).trans
      (add_le_add (mul_le_mul_of_nonneg_right (hS i) ENNReal.toReal_nonneg) le_rfl))
  simpa only [mul_zero,zero_mul,add_zero] using
    (hTV.const_mul C).add (hSU.mul_const (signedTV V))

end HexagonPaper
