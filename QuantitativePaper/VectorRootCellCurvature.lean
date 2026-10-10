module
public import QuantitativePaper.VectorRootCellStieltjes
public import QuantitativePaper.VectorSiteCurvatureAverage
public import FourPapersCommon.GaussianTiltedCurvatureRaw
public import QuantitativePaper.ResponseModel

@[expose] public section

/-! Genuine incident-site conditional curvature lower bound for an actual
finite prefix. The only stage conditions are the literal incoming and
outgoing physical masses at the chosen first crossing. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

theorem sitePrefixGaussian_curvature_root_raw_lower {n k N : ℕ} (s : RSBScheme k)
    (β t a U : ℝ) (hβ : 0<β) (ht : t∈Icc 0 1) (ha0 : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0) (hNpos : 0 < N)
    (hN : N ≤ k+2) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (hm : 1 ≤ β*observableDepthMass s (k+2-N))
    (hin : β*(if N=1 then a else s.m (N-1)) ≤ max 1 U) :
    Integrable (fun g=>Real.exp (sitePrefixGaussianLogWeight s β t a i b g))
      (SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)) ∧
    Integrable (fun g=>Real.exp (sitePrefixGaussianLogWeight s β t a i b g)*
      sitePrefixGaussianCurvature s β t i b g)
      (SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)) ∧
    responseCurvatureConstant U*
      (∫g,Real.exp (sitePrefixGaussianLogWeight s β t a i b g)
        ∂SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i))  ≤ 
      ∫g,Real.exp (sitePrefixGaussianLogWeight s β t a i b g)*
        sitePrefixGaussianCurvature s β t i b g
        ∂SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i) := by
  have hMU : 0 < max (1:ℝ) U := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hDV (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
      ‖fderiv ℝ (sitePrefixGaussianLogWeight s β t a i b) g‖ ≤ 2*max 1 U := by
    obtain ⟨M,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    have hh := norm_fderiv_sitePrefixGaussianLogWeight_root_cell_le
      s β t a hβ.le ht ha0 ha hq hN i b g
    have hin' : β*(if M=0 then a else s.m M) ≤ max 1 U := by
      simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,
        show M+1=1 ↔ M=0 by omega] using hin
    nlinarith
  have hh := gaussian_tilted_curvature_raw
    (sitePrefixGaussianLogWeight s β t a i b) (sitePrefixGaussianMagnetization s β t i b)
    (sitePrefixGaussianCurvature s β t i b)
    ((contDiff_sitePrefixGaussianLogWeight s β t a i b).of_le (by simp))
    ((contDiff_sitePrefixGaussianMagnetization s β t i b).of_le (by simp))
    (continuous_sitePrefixGaussianCurvature s β t i b) (2*max 1 U) β (by positivity)
    (abs_sitePrefixGaussianCurvature_le s β t hβ.le i b) hDV
    (norm_fderiv_sitePrefixGaussianMagnetization_le s β t hβ ht hN i b)
    (abs_sitePrefixGaussianMagnetization_le_one s β t i b)
    (fun g=>sitePrefixGaussianCurvature_diagonal_bound s β t hβ.le i b g hm)
    (sitePrefixGaussianLogWeight_even s β t a i b)
    (sitePrefixGaussianMagnetization_odd s β t i b)
  convert hh using 1
  unfold responseCurvatureConstant responsePoincareConstant
  congr 3
  ring

theorem integral_vectorPrefixSiteCurvature_root_lower {n k : ℕ} (s : RSBScheme k)
    (β t a U : ℝ) (hβ : 0 < β) (ht : t ∈ Icc 0 1)
    (ha0 : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0) (N : ℕ) (hNpos : 0 < N) (hN : N ≤ k+2) (i : Fin n)
    (hm : 1 ≤ β*observableDepthMass s (k+2-N))
    (hin : β*(if N=1 then a else s.m (N-1)) ≤ max 1 U) :
    responseCurvatureConstant U ≤
      ∫z,vectorPrefixSiteCurvature s β t N i z ∂vectorPrefixEuclideanLaw s β t a N := by
  let P := SYK.standardGaussianMeasureOnEuclidean (SiteGaussianIndex (N:=N) i)
  let Q := SYK.standardGaussianMeasureOnEuclidean (SiteComplementIndex (N:=N) i)
  let G := SYK.standardGaussianMeasureOnEuclidean (VectorPrefixGaussianIndex n N)
  let J := gaussianCoordinateJoin (siteGaussianPredicate (N:=N) i)
  let V := fun z : VectorPrefixGaussianSpace n N=>
    vectorPrefixLogWeight s β t a N (vectorPrefixEuclideanHistory s β t N z)
  let H := vectorPrefixSiteCurvature s β t N i
  have hJ : Measurable J := J.measurable
  have hV : Measurable V := measurable_vectorPrefixEuclideanLogWeight s β t a N
  have hH : Continuous H := continuous_vectorPrefixSiteCurvature s β t N i
  have hmap : (P.prod Q).map J=G := siteGaussianJoin_law i
  have hI : Integrable (fun z=>Real.exp (V z)) G :=
    integrable_exp_vectorPrefixEuclideanLogWeight s β t a N hN
  have hIp : Integrable (fun z=>Real.exp (V (J z))) (P.prod Q) := by
    apply (integrable_map_measure hV.exp.aestronglyMeasurable hJ.aemeasurable).mp
    rw [hmap]
    exact hI
  have hIH : Integrable (fun z=>Real.exp (V z)*H z) G :=
    hI.mul_bdd hH.aestronglyMeasurable (.of_forall fun z=>by
      simpa only [Real.norm_eq_abs] using abs_vectorPrefixSiteCurvature_le s β t hβ.le N i z)
  have hZI : (∫z,Real.exp (V (J z)) ∂P.prod Q)=vectorOuterPartition (n:=n) s β t a := by
    rw [←integral_map hJ.aemeasurable hV.exp.aestronglyMeasurable,hmap]
    exact integral_exp_vectorPrefixEuclideanLogWeight s β t a N hN
  have hl := lower_bound_normalized_product_density P Q
    (fun z=>V (J z)) (fun z=>H (J z)) (responseCurvatureConstant U) β hIp
    (hH.comp J.continuous).aestronglyMeasurable
    (fun z=>abs_vectorPrefixSiteCurvature_le s β t hβ.le N i (J z))
    (by rw [hZI];exact vectorOuterPartition_pos s β t a)
    (fun b=>(sitePrefixGaussian_curvature_root_raw_lower s β t a U hβ ht ha0 ha hq hNpos hN i b hm hin).2.2)
  have hHI : (∫z,Real.exp (V (J z))*H (J z) ∂P.prod Q)=
      ∫z,Real.exp (V z)*H z ∂G := by
    have he := integral_map (μ:=P.prod Q) (f:=fun z=>Real.exp (V z)*H z)
      hJ.aemeasurable (hV.exp.mul hH.measurable).aestronglyMeasurable
    rw [hmap] at he
    exact he.symm
  rw [hHI,hZI] at hl
  rw [integral_vectorPrefixEuclideanLaw s β t a N hN]
  exact hl


end QuantitativePaper
