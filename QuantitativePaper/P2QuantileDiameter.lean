module
public import QuantitativePaper.P2QuantileBound
public import QuantitativePaper.QuantileDiameterBounds
public import FourPapersCommon.DyadicQuantileShells

@[expose] public section

/-! The p2 profile quantile bound controls the genuine essential diameter,
including jump points of the actual free overlap measure. -/
noncomputable section
open Set MeasureTheory Filter Paper QuantitativeFollowup FourPapersCommon
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1300000

theorem p2_free_quantile_le_of_profile_bound (μ : ParisiMeasure) (β s u v B : ℝ)
    (hβ : 0 < β) (hs : s ∈ Icc (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) (1-s))
    (hlevel : β*(s+v) < 2*u) (hB : 0 ≤ B)
    (hbound : ∀x ∈ Icc (0 : ℝ) 1, β*parisiCDF μ x < 2*u → x ≤ B) :
    (parisiFreeQuantile μ s v : ℝ) ≤ B := by
  by_contra hh
  obtain ⟨x,hBx,hxQ⟩ := exists_between (lt_of_not_ge hh)
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨hB.trans hBx.le,hxQ.le.trans (parisiFreeQuantile μ s v).property.2⟩
  have hCDF : parisiCDF μ x < s+v := by
    by_contra hnot
    have hq := (parisiQuantile_le_iff μ (s+v) x hx).mpr (by
      rw [quantileLevel_eq (show s+v ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hs.1,hv.1,hv.2])]
      exact not_lt.mp hnot)
    exact (not_le_of_gt hxQ) hq
  have hβCDF := mul_lt_mul_of_pos_left hCDF hβ
  exact (not_le_of_gt hBx) (hbound x hx (hβCDF.trans hlevel))

theorem p2_quantile_diameter_le_of_upper (μ : ParisiMeasure) (s : ℝ)
    (I : Set ℝ) (hI : MeasurableSet I) (hvol : 0 < volume.real I) (B : ℝ)
    (hupper : ∀v ∈ I, (parisiFreeQuantile μ s v : ℝ) ≤ B) :
    parisiQuantileImageDiameter μ s I ≤ B := by
  have hIpos : volume I ≠ 0 := by
    intro h
    simp only [Measure.real,h,ENNReal.toReal_zero] at hvol
    exact (lt_irrefl _ hvol)
  have hPpos : (volume.restrict I).prod (volume.restrict I) ≠ 0 := by
    intro h
    have he := congrArg (fun P : Measure (ℝ×ℝ) => P univ) h
    rw [←univ_prod_univ,Measure.prod_prod] at he
    simp only [Measure.restrict_apply_univ] at he
    change volume I*volume I = 0 at he
    exact mul_ne_zero hIpos hIpos he
  let : NeZero ((volume.restrict I).prod (volume.restrict I)) := ⟨hPpos⟩
  unfold parisiQuantileImageDiameter intervalEssentialDiameter
  refine essSup_le_of_ae_le B ?_ ?_
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hI.prod hI)] with p hp
    rw [abs_le]
    constructor <;> linarith [hupper p.1 hp.1,hupper p.2 hp.2,
      (parisiFreeQuantile μ s p.1).property.1,(parisiFreeQuantile μ s p.2).property.1]
  · exact isCoboundedUnder_le_of_le _ (fun p => abs_nonneg _)

theorem p2_dyadic_quantile_diameter_le (T k Cs : ℝ)
    (hT : T ∈ Ioc (0 : ℝ) (1/4)) (hk : 0 < k) (hCs : 0 ≤ Cs)
    (n : ℕ) (hn : 0 < n) (μ ν : ParisiMeasure) (β lam r η : ℝ)
    (hβ : 1 ≤ β) (hlam : lam ∈ Icc (0 : ℝ) β) (hr : r ∈ Ioc (0 : ℝ) 1) (hη : 0 ≤ η)
    (hμ : μ ∈ scalarFloor (lam/β)) (hν : ν ∈ scalarFloor (lam/β))
    (hmin : ∀ρ ∈ scalarFloor (lam/β), responseEnergyFunctional n μ β (1-r) lam ≤
      responseEnergyFunctional n ρ β (1-r) lam)
    (hbudget : responseEnergyFunctional n ν β (1-r) lam-responseEnergyFunctional n μ β (1-r) lam ≤ η)
    (htrial : ∀y ∈ Icc (0 : ℝ) T, k*y ≤ β*parisiCDF ν y ∧ β*parisiCDF ν y ≤ 2)
    (hdensity : ENNReal.ofReal β • (parisiCDFPrimitive ν).measure.restrict (Ioo (0 : ℝ) T) ≤
      ENNReal.ofReal Cs • volume.restrict (Ioo (0 : ℝ) T))
    (j : ℕ) (hlamp : 0 < lam) (hU : (2 : ℝ)^j*lam ≤ 1)
    (hvol : 0 < volume.real (dyadicQuantileShell (lam/β) (lam/β) j)) :
    parisiQuantileImageDiameter μ (lam/β) (dyadicQuantileShell (lam/β) (lam/β) j) ≤
      p2QuantileConstant T k Cs*(r^(-3/5 : ℝ)*((2 : ℝ)^j*lam)+r^(-7/11 : ℝ)*η^(2/11 : ℝ)) := by
  have hβp : 0 < β := by linarith
  have hs : lam/β ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hlam.1 hβp.le,(div_le_one hβp).mpr hlam.2⟩
  have hUp : 0 < (2 : ℝ)^j*lam := by positivity
  have hbound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :=
    p2_quantile_bound_of_trial_data T k Cs hT hk hCs n hn μ ν β lam r η
      ((2 : ℝ)^j*lam) x hβ hlam hr hη ⟨hUp,hU⟩ hx
  apply p2_quantile_diameter_le_of_upper μ (lam/β) _
    (dyadicQuantileShell_ordConnected _ _ j).measurableSet hvol _
  intro v hv
  apply p2_free_quantile_le_of_profile_bound μ β (lam/β) ((2 : ℝ)^j*lam) v _ hβp hs hv.1
  · have hh := mul_lt_mul_of_pos_left hv.2.2 hβp
    have he : β*((2 : ℝ)^(j+1)*(lam/β)-lam/β) = 2*((2 : ℝ)^j*lam)-lam := by
      rw [pow_succ]
      field_simp
    rw [he] at hh
    field_simp
    linarith
  · exact mul_nonneg (p2QuantileConstant_pos T k Cs hT.1 hk).le (by positivity [hr.1])
  · intro x hx hsmall
    exact hbound x hx hμ hν hmin hbudget hsmall htrial hdensity

end QuantitativePaper
