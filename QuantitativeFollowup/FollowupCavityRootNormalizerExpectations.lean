module
public import QuantitativeFollowup.AnisotropicNodeTheta
public import QuantitativeFollowup.AnisotropicNodeB
public import QuantitativeFollowup.FollowupCavityNormalizerVarianceDerivative

@[expose] public section

/-! Atom-exact root response balances of the genuine arbitrary-profile
process. All future squares are actual conditional responses; Fubini and the
root-atom subtraction are proved with their honest integrability bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem bounded_joint_integral_swap {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (P : Measure X) (Q : Measure Y)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (F : X×Y→ℝ) (hF : Measurable F) (C : ℝ) (hb : ∀z,‖F z‖≤C) :
    (∫y,∫x,F (x,y)∂P∂Q)=∫x,∫y,F (x,y)∂Q∂P := by
  have hi : Integrable F (P.prod Q):=(integrable_const C).mono' hF.aestronglyMeasurable (.of_forall hb)
  exact (integral_integral_swap (f:=fun x y=>F (x,y)) hi).symm

private theorem integral_overlap_root_split (P : Measure Paper.Overlap) [IsFiniteMeasure P]
    (F : Paper.Overlap→ℝ) (hF : Measurable F) (C : ℝ) (hb : ∀r,‖F r‖≤C) :
    (∫r,F r∂P)=P.real {zeroOverlap}*F zeroOverlap+
      ∫r,if zeroOverlap<r then F r else 0∂P := by
  classical
  let R:=({zeroOverlap}:Set Paper.Overlap).indicator (fun _=>F zeroOverlap)
  let G:=fun r : Paper.Overlap=>if zeroOverlap<r then F r else 0
  have hR : Integrable R P:=(integrable_const (F zeroOverlap)).indicator (measurableSet_singleton _)
  have hmG : Measurable G:=Measurable.ite (measurableSet_lt measurable_const measurable_id) hF measurable_const
  have hiG : Integrable G P:=(integrable_const C).mono' hmG.aestronglyMeasurable
    (.of_forall fun r=>by dsimp [G];split_ifs;exact hb r;simpa only [norm_zero,abs_zero] using (norm_nonneg (F r)).trans (hb r))
  have he (r : Paper.Overlap) : F r=R r+G r := by
    by_cases hr:r=zeroOverlap
    · simp [R,G,hr]
    · have h0:zeroOverlap<r:=lt_of_le_of_ne r.property.1 (Ne.symm hr)
      simp [R,G,hr,h0]
  calc
    (∫r,F r∂P)=∫r,R r+G r∂P:=integral_congr_ae (.of_forall he)
    _=(∫r,R r∂P)+∫r,G r∂P:=integral_add hR hiG
    _=P.real {zeroOverlap}*F zeroOverlap+∫r,if zeroOverlap<r then F r else 0∂P := by
      dsimp only [R,G]
      rw [integral_indicator (measurableSet_singleton _),setIntegral_const]
      simp only [smul_eq_mul]

private theorem parisiCDF_zero_eq_atom (μ : Paper.ParisiMeasure) :
    Paper.parisiCDF μ 0=(μ:Measure Paper.Overlap).real {zeroOverlap} := by
  have hs : {r : Paper.Overlap | (r:ℝ)≤0}=({zeroOverlap}:Set Paper.Overlap) := by
    ext r
    simp only [mem_setOf_eq,mem_singleton_iff]
    constructor
    · intro hr
      apply Subtype.ext
      exact le_antisymm hr r.property.1
    · rintro rfl
      norm_num [zeroOverlap]
  change ((μ:Measure Paper.Overlap) {r : Paper.Overlap | (r:ℝ)≤0}).toReal=_
  rw [hs]
  rfl

theorem anisotropic_root_pair_response_balance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (e : AnisotropicCouplingIndex n) :
    (∫p,anisotropicProcessPairSecond D μ zeroOverlap e p+
       a*(anisotropicProcessPairResponse D μ zeroOverlap e p)^2∂anisotropicMeasureSampleLaw D μ a)=
      1-∫r,∫p,(anisotropicProcessPairResponse D μ r e p)^2
        ∂anisotropicMeasureSampleLaw D μ a∂parisiFreeMeasure μ a := by
  classical
  let P:=anisotropicMeasureSampleLaw D μ a
  let F:=fun r : Paper.Overlap=>∫p,(anisotropicProcessPairResponse D μ r e p)^2∂P
  have hm:=(measurable_uncurry_anisotropicProcessPairResponse D μ e).pow_const 2
  have hFm : Measurable F:=hm.stronglyMeasurable.integral_prod_right'.measurable
  have hb (r : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) :
      ‖(anisotropicProcessPairResponse D μ r e p)^2‖≤1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessPairResponse_bound D μ r e p) 2).trans_eq (by norm_num)
  have hFb (r : Paper.Overlap) : ‖F r‖≤1 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=P) (C:=1) (.of_forall (hb r))
  have hHi : Integrable (anisotropicProcessPairSecond D μ zeroOverlap e) P:=
    (integrable_const (anisotropicPairSecondBound D e)).mono'
      ((adapted_anisotropicProcessPairSecond D μ zeroOverlap e).mono ((anisotropicBrownianFiltration n).le _) le_rfl).aestronglyMeasurable
      (.of_forall (norm_anisotropicProcessPairSecond_le D μ zeroOverlap e))
  have hMi : Integrable (fun p=>(anisotropicProcessPairResponse D μ zeroOverlap e p)^2) P:=
    (integrable_const (1:ℝ)).mono' ((measurable_anisotropicProcessPairResponse D μ zeroOverlap e).pow_const 2).aestronglyMeasurable
      (.of_forall (hb zeroOverlap))
  have hnode:=anisotropic_native_pair_second_stieltjes_pairing D μ a zeroOverlap e
    (fun _=>1) measurable_const 1 (fun _=>by norm_num)
  simp only [one_mul,integral_const,probReal_univ,smul_eq_mul,mul_one,zeroOverlap,Set.Icc.coe_zero] at hnode
  have hGm : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      if zeroOverlap<z.1 then (anisotropicProcessPairResponse D μ z.1 e z.2)^2 else 0):=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) hm measurable_const
  have hswap:=bounded_joint_integral_swap (μ:Measure Paper.Overlap) P _ hGm 1
    (fun z=>by split_ifs;exact hb z.1 z.2;norm_num)
  have he : (∫p,anisotropicRawFuturePairSquare D μ zeroOverlap e p∂P)=
      ∫r,if zeroOverlap<r then F r else 0∂(μ:Measure Paper.Overlap) := by
    simp only [anisotropicRawFuturePairSquare]
    rw [hswap]
    apply integral_congr_ae
    exact .of_forall fun r=>by by_cases hr:zeroOverlap<r <;> simp [hr,F]
  change (∫p,anisotropicProcessPairSecond D μ zeroOverlap e p∂P)+
    Paper.parisiCDF μ 0*(∫p,(anisotropicProcessPairResponse D μ zeroOverlap e p)^2∂P)+
    (∫p,anisotropicRawFuturePairSquare D μ zeroOverlap e p∂P)=1 at hnode
  rw [he,parisiCDF_zero_eq_atom] at hnode
  have hsplit:=integral_overlap_root_split (μ:Measure Paper.Overlap) F hFm 1 hFb
  have hFνi : Integrable F (parisiFreeMeasure μ a):=(integrable_const (1:ℝ)).mono' hFm.aestronglyMeasurable (.of_forall hFb)
  have hdecomp : (∫r,F r∂(μ:Measure Paper.Overlap))=a*F zeroOverlap+
      ∫r,F r∂parisiFreeMeasure μ a := by
    rw [←root_add_parisiFreeMeasure μ a ha hμ,integral_add_measure
      ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top) hFνi,
      integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal ha.1]
    rfl
  rw [integral_add hHi (hMi.const_mul a),integral_const_mul]
  change (∫p,anisotropicProcessPairSecond D μ zeroOverlap e p∂P)+a*F zeroOverlap=1-∫r,F r∂parisiFreeMeasure μ a
  linarith

end QuantitativeFollowup
