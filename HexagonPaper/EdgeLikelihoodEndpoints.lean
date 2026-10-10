module
public import HexagonPaper.EdgeLikelihoodProfileAction

@[expose] public section

/-! Literal endpoint/atom conversion for the native suffix likelihood. The
open-end formula uses the actual left cumulative mass and keeps endpoint
atoms separate, as in the paper's edge likelihood. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgeNativePathPotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) : C(Paper.Overlap,ℝ) :=
  (edgeTailPotentialMap D μ).comp ((ContinuousMap.id Paper.Overlap).prodMk Z)

@[simp] theorem edgeNativePathPotential_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Z : C(Paper.Overlap,AnisotropicParameter n)) (r : Paper.Overlap) :
    edgeNativePathPotential D μ Z r=anisotropicMeasureTailPotential D μ r (Z r) := rfl

def edgeLeftCDF (μ : Paper.ParisiMeasure) (h : Paper.Overlap) : ℝ :=
  (μ:Measure Paper.Overlap).real (Iio h)

theorem edgeSuffixAction_eq_right_CDF (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeSuffixAction D μ q Z=
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)+
        ∫r in Ioi q,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap) := by
  let F:=edgeNativePathPotential D μ Z
  let H : Paper.Overlap→ℝ:=fun r=>if r≤q then 1 else 0
  have hH : Integrable H (μ:Measure Paper.Overlap) := by
    change Integrable ((Iic q).indicator (fun _=>(1:ℝ))) _
    exact (integrable_const _).indicator measurableSet_Iic
  have hF : Integrable F (μ:Measure Paper.Overlap) := continuousMap_integrable_probability _ _
  have he : (fun r=>anisotropicMeasureTailPotential D μ (anisotropicClampOverlap q r)
      (Z (anisotropicClampOverlap q r)))=
      (fun r=>H r*F q)+(Ioi q).indicator F := by
    funext r
    by_cases h : r≤q
    · have hc : anisotropicClampOverlap q r=q := Subtype.ext (max_eq_left h)
      have hr : r∉Ioi q := not_lt_of_ge h
      simp only [hc,H,h,ite_true,one_mul,Pi.add_apply,
        Set.indicator_of_notMem hr,add_zero,F,edgeNativePathPotential_apply]
    · have hc : anisotropicClampOverlap q r=r := Subtype.ext (max_eq_right (le_of_not_ge h))
      have hr : r∈Ioi q := lt_of_not_ge h
      simp only [hc,H,h,ite_false,zero_mul,Pi.add_apply,
        Set.indicator_of_mem hr,zero_add,F,edgeNativePathPotential_apply]
  unfold edgeSuffixAction
  rw [he]
  change (∫r,H r*F q+(Ioi q).indicator F r ∂(μ:Measure Paper.Overlap))=_
  rw [integral_add (hH.mul_const _) (hF.indicator measurableSet_Ioi),
    integral_mul_const,integral_indicator measurableSet_Ioi]
  have hCDF : (∫r,H r ∂(μ:Measure Paper.Overlap))=Paper.parisiCDF μ q :=
    (Paper.parisiCDF_eq_integral_upperIndicator μ q).symm
  rw [hCDF]
  rfl

theorem edgeLeftCDF_one_add_terminal_atom (μ : Paper.ParisiMeasure) :
    edgeLeftCDF μ ⟨1,by norm_num⟩+(μ:Measure Paper.Overlap).real {⟨1,by norm_num⟩}=1 := by
  let one : Paper.Overlap:=⟨1,by norm_num⟩
  have hu : Iio one∪{one}=(univ:Set Paper.Overlap) := by
    rw [Iio_union_right]
    ext r
    simp only [mem_Iic,mem_univ,iff_true]
    exact r.property.2
  have hd : Disjoint (Iio one) ({one}:Set Paper.Overlap) := by
    apply disjoint_singleton_right.mpr
    exact lt_irrefl one
  have hm:=measureReal_union (μ:=(μ:Measure Paper.Overlap)) hd (measurableSet_singleton one)
  rw [hu,probReal_univ] at hm
  exact hm.symm

theorem edgeSuffixLikelihood_eq_open_endpoints
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (q : Paper.Overlap)
    (hq : q<(⟨1,by norm_num⟩:Paper.Overlap)) (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeSuffixLikelihood D μ q Z=ENNReal.ofReal (Real.exp (
      edgeLeftCDF μ ⟨1,by norm_num⟩*anisotropicMeasureTailPotential D μ ⟨1,by norm_num⟩ (Z ⟨1,by norm_num⟩)-
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)-
      ∫r in Ioo q ⟨1,by norm_num⟩,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap))) := by
  let one : Paper.Overlap:=⟨1,by norm_num⟩
  let F:=edgeNativePathPotential D μ Z
  have hF : Integrable F (μ:Measure Paper.Overlap) := continuousMap_integrable_probability _ _
  have hu : Ioi q=Ioo q one∪{one} := by
    rw [Ioo_union_right hq]
    ext r
    simp only [mem_Ioi,mem_Ioc]
    exact ⟨fun hr=>⟨hr,r.property.2⟩,fun hr=>hr.1⟩
  have hd : Disjoint (Ioo q one) ({one}:Set Paper.Overlap) := by
    apply disjoint_singleton_right.mpr
    exact fun h=>lt_irrefl one h.2
  have hi : (∫r in Ioi q,F r ∂(μ:Measure Paper.Overlap))=
      (∫r in Ioo q one,F r ∂(μ:Measure Paper.Overlap))+(μ:Measure Paper.Overlap).real {one}*F one := by
    rw [hu,setIntegral_union hd (measurableSet_singleton one) hF.integrableOn hF.integrableOn,
      integral_singleton,smul_eq_mul]
  have hm:=edgeLeftCDF_one_add_terminal_atom μ
  change edgeLeftCDF μ one+(μ:Measure Paper.Overlap).real {one}=1 at hm
  rw [edgeSuffixLikelihood,edgeSuffixAction_eq_right_CDF]
  change ENNReal.ofReal (Real.exp (F one-(Paper.parisiCDF μ q*F q+∫r in Ioi q,F r ∂(μ:Measure Paper.Overlap))))=_
  rw [hi]
  congr 2
  change F one-(Paper.parisiCDF μ q*F q+
    ((∫r in Ioo q one,F r ∂(μ:Measure Paper.Overlap))+(μ:Measure Paper.Overlap).real {one}*F one))=
      edgeLeftCDF μ one*F one-Paper.parisiCDF μ q*F q-
        ∫r in Ioo q one,F r ∂(μ:Measure Paper.Overlap)
  have hm':=congrArg (fun c : ℝ=>c*F one) hm
  simp only [add_mul,one_mul] at hm'
  linarith

end HexagonPaper
