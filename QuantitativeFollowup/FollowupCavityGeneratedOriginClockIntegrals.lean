module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginForkLabels
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The true origin clock integrals are measurable under moving generated
histories. Moving Stieltjes cells are treated as measurable indicators in
the joint space; no continuity at an atom is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [MeasurableSpace H]

theorem measurable_cavityGeneratedMovingCellIntegral
    (ν : Measure Paper.Overlap) [SFinite ν]
    (lo hi : H → Paper.Overlap) (hlo : Measurable lo) (hhi : Measurable hi)
    (f : Paper.Overlap → ℝ) (hf : Measurable f) :
    Measurable (fun h => ∫r in Ioc (lo h) (hi h),f r ∂ν) := by
  let E : Set (H × Paper.Overlap) := {z | lo z.1 < z.2 ∧ z.2 ≤ hi z.1}
  have hE : MeasurableSet E := by
    change MeasurableSet {z : H × Paper.Overlap |
      (lo z.1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ (hi z.1 : ℝ)}
    exact (measurableSet_lt ((measurable_subtype_coe.comp hlo).comp measurable_fst)
      (measurable_subtype_coe.comp measurable_snd)).inter
        (measurableSet_le (measurable_subtype_coe.comp measurable_snd)
          ((measurable_subtype_coe.comp hhi).comp measurable_fst))
  have hm : StronglyMeasurable (E.indicator (fun z : H × Paper.Overlap => f z.2)) :=
    ((hf.comp measurable_snd).indicator hE).stronglyMeasurable
  have he (h : H) :
      (∫r,E.indicator (fun z : H × Paper.Overlap => f z.2) (h,r) ∂ν) =
      ∫r in Ioc (lo h) (hi h),f r ∂ν := by
    change (∫r,(Ioc (lo h) (hi h)).indicator f r ∂ν) = _
    exact integral_indicator measurableSet_Ioc
  exact (funext he) ▸ hm.integral_prod_right'.measurable

theorem measurable_cavityGeneratedOriginClockIntegral
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : H → ℕ → Paper.Overlap) (hq : ∀d,Measurable (fun h => q h d))
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (s : H → ℝ) (hs : Measurable s) (f : Paper.Overlap → ℝ) (hf : Measurable f) :
    Measurable (fun h => nativeStreamingOriginWeightIntegral μ a (q h) T (s h)
      (fun o => f (nativeStreamingOriginLevel (q h) o))) := by
  have hc (d : ℕ) : Measurable (fun h => Paper.parisiCDF μ (q h d)) :=
    (Paper.parisiCDF_measurable μ).comp (measurable_subtype_coe.comp (hq d))
  induction T generalizing s with
  | leaf =>
      exact (measurable_const.sub hs).mul (hf.comp (hq 0))
  | @advance j T ih =>
      simp only [nativeStreamingOriginWeightIntegral,printedGeneratedOriginLevel_child,
        nativeStreamingOriginLevel,FiniteCascadeRecordVertex.depth]
      exact ((ih _ (hc j)).add
        (measurable_cavityGeneratedMovingCellIntegral (parisiFreeMeasure μ a)
          (fun h => q h (j+1)) (fun h => q h j) (hq (j+1)) (hq j) f hf)).add
          (((hc (j+1)).sub hs).mul (hf.comp (hq (j+1))))
  | @fork j T U ihT ihU =>
      simp only [nativeStreamingOriginWeightIntegral,printedGeneratedOriginLevel_left,
        printedGeneratedOriginLevel_right,nativeStreamingOriginLevel,
        FiniteCascadeRecordVertex.depth]
      exact ((ihT _ (hc j)).add (ihU _ (hc j))).add
        ((((hc j).const_mul 2).sub hs).mul (hf.comp (hq j)))

theorem integrable_cavityGeneratedOriginClockCubic
    {n m : ℕ} (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Integrable (fun h => nativeStreamingOriginWeightIntegral μ a
      (W.clockTemplate.clock h c) (W.tree c) a
      (fun o => cavityCubicPairMoment D μ a
        (nativeStreamingOriginLevel (W.clockTemplate.clock h c) o)))
      ((P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)) := by
  haveI := (P.restrict W.clockTemplate.orderSet).isFiniteMeasure_measure
    (parisiFreeMeasure μ a) (cavityGenerated_free_mass_le_one μ a ha.1)
  have hm := measurable_cavityGeneratedOriginClockIntegral μ a
    (fun h => W.clockTemplate.clock h c)
    (fun d => (W.clockTemplate.clock_continuous c d).measurable) (W.tree c)
    (fun _ => a) measurable_const (cavityCubicPairMoment D μ a)
    (continuous_cavityCubicPairMoment D μ a).measurable
  apply (integrable_const (8*(FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ))).mono'
    hm.aestronglyMeasurable
  exact .of_forall fun h => by
    have hq : Antitone (W.clockTemplate.clock h c) :=
      antitone_nat_of_succ_le (fun d => W.clockTemplate.clock_step_le h c d)
    have hs : a ≤ Paper.parisiCDF μ (W.clockTemplate.clock h c (W.depth c)) := by
      let c' : Fin W.clockTemplate.componentCount := c
      change a ≤ Paper.parisiCDF μ (W.clockTemplate.clock h c' (W.clockTemplate.depth c'))
      rw [W.clockTemplate.clock_initial h c']
      exact scalarFloor_cdf_lower hμ (by norm_num)
    have hb := nativeStreamingOriginWeightIntegral_abs_le μ a ha hμ
      (W.clockTemplate.clock h c) hq (W.tree c) a hs 8 (by norm_num)
      (fun o => cavityCubicPairMoment D μ a
        (nativeStreamingOriginLevel (W.clockTemplate.clock h c) o))
      (fun o => by
        rw [abs_of_nonneg (cavityCubicPairMoment_bounds D μ a _).1]
        exact (cavityCubicPairMoment_bounds D μ a _).2)
    rw [Real.norm_eq_abs]
    exact hb.trans (by nlinarith only [ha.1])

theorem cavityGeneratedOriginClockCubic_integral_le
    {n m : ℕ} (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    (∫h,nativeStreamingOriginWeightIntegral μ a (W.clockTemplate.clock h c) (W.tree c) a
      (fun o => cavityCubicPairMoment D μ a
        (nativeStreamingOriginLevel (W.clockTemplate.clock h c) o))
      ∂(P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)) ≤
    ((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ) +
      ((cavityGeneratedOriginForkMarks W c).length : ℝ)*m)*P.budget*
        cavityThirdMoment D μ a := by
  let Q := P.restrict W.clockTemplate.orderSet
  let M := Q.measure (parisiFreeMeasure μ a)
  let χ := cavityCubicPairMoment D μ a
  let k : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c))
  let l : ℝ := (cavityGeneratedOriginForkMarks W c).length
  let S : CavityGeneratedHistory Paper.Overlap m → ℝ := fun h => ∑i : Fin m,χ (h i)
  haveI := Q.isFiniteMeasure_measure (parisiFreeMeasure μ a)
    (cavityGenerated_free_mass_le_one μ a ha.1)
  have hi (i : Fin m) : Integrable (fun h => χ (h i)) M := by
    apply (integrable_const (8 : ℝ)).mono'
      (((continuous_cavityCubicPairMoment D μ a).measurable.comp
        (measurable_pi_apply i)).aestronglyMeasurable)
    exact .of_forall fun h => by
      change ‖cavityCubicPairMoment D μ a (h i)‖ ≤ 8
      rw [Real.norm_of_nonneg (cavityCubicPairMoment_bounds D μ a (h i)).1]
      exact (cavityCubicPairMoment_bounds D μ a (h i)).2
  have hiS : Integrable S M := integrable_finset_sum _ (fun i _ => hi i)
  have hlist (h : CavityGeneratedHistory Paper.Overlap m) (L : List (Fin m)) :
      (L.map (fun i => Paper.parisiCDF μ (h i)*χ (h i))).sum ≤ (L.length : ℝ)*S h := by
    induction L with
    | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.cast_zero,zero_mul,le_refl]
    | cons i L ih =>
        have hc : Paper.parisiCDF μ (h i)*χ (h i) ≤ χ (h i) := by
          exact (mul_le_mul_of_nonneg_right (Paper.parisiCDF_le_one μ (h i))
            (cavityCubicPairMoment_bounds D μ a (h i)).1).trans_eq (one_mul _)
        have hs : χ (h i) ≤ S h :=
          Finset.single_le_sum (fun j _ => (cavityCubicPairMoment_bounds D μ a (h j)).1)
            (Finset.mem_univ i)
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith only [hc,hs,ih]
  have hpoint : ∀ᵐh ∂M,
      nativeStreamingOriginWeightIntegral μ a (W.clockTemplate.clock h c) (W.tree c) a
        (fun o => χ (nativeStreamingOriginLevel (W.clockTemplate.clock h c) o)) ≤
        k*cavityThirdMoment D μ a+l*S h := by
    have hm : ∀ᵐh ∂M,h ∈ W.clockTemplate.orderSet :=
      ae_restrict_mem W.clockTemplate.isClosed_orderSet.measurableSet
    exact hm.mono fun h hh => by
      have hb := cavityGeneratedOriginClockBudget_history_marks μ a ha hμ W c h hh χ
        (integrable_cavityCubicPairMoment D μ a)
        (fun r => (cavityCubicPairMoment_bounds D μ a r).1)
      change _ ≤ k*cavityThirdMoment D μ a +
        ((cavityGeneratedOriginForkMarks W c).map
          (fun i => Paper.parisiCDF μ (h i)*χ (h i))).sum at hb
      exact hb.trans (add_le_add_right (hlist h (cavityGeneratedOriginForkMarks W c)) _)
  have hcomp := integral_mono_ae
    (integrable_cavityGeneratedOriginClockCubic D μ a ha hμ P W c)
    ((integrable_const (k*cavityThirdMoment D μ a)).add (hiS.const_mul l)) hpoint
  have hmass : M.real univ ≤ (P.budget : ℝ) := by
    have hb := Q.measure_univ_le_budget (parisiFreeMeasure μ a)
      (cavityGenerated_free_mass_le_one μ a ha.1)
    exact (ENNReal.toReal_mono (ENNReal.natCast_ne_top Q.budget) hb).trans_eq
      (by simp only [ENNReal.toReal_natCast,Q,CavityGeneratedMarkProgram.budget])
  have hS : (∫h,S h ∂M) ≤ (m : ℝ)*P.budget*cavityThirdMoment D μ a := by
    simpa only [Q,M,S,χ,CavityGeneratedMarkProgram.budget] using
      cavityGenerated_sum_marks_cubic_le D μ a ha.1 Q
  change _ ≤ ∫h,k*cavityThirdMoment D μ a + l*S h ∂M at hcomp
  rw [integral_add (integrable_const _) (hiS.const_mul l)] at hcomp
  simp only [integral_const_mul,integral_const,smul_eq_mul] at hcomp
  have hmass' : M.real univ*(k*cavityThirdMoment D μ a) ≤
      (P.budget : ℝ)*(k*cavityThirdMoment D μ a) :=
    mul_le_mul_of_nonneg_right hmass
      (mul_nonneg (Nat.cast_nonneg _) (cavityThirdMoment_nonneg D μ a))
  have hS' : l*(∫h,S h ∂M) ≤ l*((m : ℝ)*P.budget*cavityThirdMoment D μ a) :=
    mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
  change _ ≤ (k+l*m)*P.budget*cavityThirdMoment D μ a
  nlinarith only [hcomp,hmass',hS']

end QuantitativeFollowup
