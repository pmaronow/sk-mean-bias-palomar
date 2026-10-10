module
public import QuantitativeFollowup.ScalarFiniteGaussianLaw
public import QuantitativeFollowup.ParisiFreeIntegralContinuity
public import FRSB.FiniteForwardAction

@[expose] public section

/-! The literal finite observed scalar/spin density, with u=log2+potential
and an arbitrary prescribed root split. The free measure may still charge
zero. Density and observation laws are derived from the actual recursion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option maxHeartbeats 1900000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarPrintedPotential (β : ℝ) (μ : Paper.ParisiMeasure) (q x : ℝ) : ℝ :=
  Real.log 2+parisiPotential β μ (q,x)

def scalarPrintedBrownianFreeDensity (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p : Paper.BrownianSample×Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (Paper.spinSign p.2*(β*canonicalBrownian 1 p.1)-
    a*scalarPrintedPotential β μ 0 0-
    ∫q : Paper.Overlap,scalarPrintedPotential β μ q (β*canonicalBrownian (q : ℝ).toNNReal p.1)
      ∂parisiFreeMeasure μ a))

def scalarPrintedBrownianHistory (s : RSBScheme k) (β : ℝ) :
    Paper.BrownianSample → (Fin (k+3)→ℝ) :=
  FRSB.historySample (fun r ω=>β*canonicalBrownian r ω) (FRSB.forwardSchemeTime s 1) (k+2)

def scalarPrintedBrownianHistoryMarkMap (s : RSBScheme k) (β : ℝ) :
    (Paper.BrownianSample×Bool) → ((Fin (k+3)→ℝ)×Bool) :=
  fun p=>(scalarPrintedBrownianHistory s β p.1,p.2)

theorem measurable_scalarPrintedBrownianHistory (s : RSBScheme k) (β : ℝ) :
    Measurable (scalarPrintedBrownianHistory s β) :=
  FRSB.measurable_historySample _ (fun r=>(measurable_canonicalBrownian r).const_mul β) _ _

theorem scalarPrintedPotential_root_free_action (s : RSBScheme k) (β a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : Paper.parisiSchemeMeasure s ∈ QuantitativePaper.scalarFloor a)
    (ω : Paper.BrownianSample) :
    a*scalarPrintedPotential β (Paper.parisiSchemeMeasure s) 0 0+
      (∫q : Paper.Overlap,scalarPrintedPotential β (Paper.parisiSchemeMeasure s) q
        (β*canonicalBrownian (q : ℝ).toNNReal ω)∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) =
      Real.log 2+FRSB.forwardBrownianAction β (Paper.parisiSchemeMeasure s) 1 ω := by
  let μ := Paper.parisiSchemeMeasure s
  let f := fun q : Paper.Overlap=>scalarPrintedPotential β μ q (β*canonicalBrownian (q : ℝ).toNNReal ω)
  have hf : Continuous f := by
    unfold f scalarPrintedPotential
    apply continuous_const.add
    exact (continuous_parisiPotential β μ).comp (continuous_subtype_val.prodMk
      (((continuous_canonicalBrownian ω).comp (continuous_real_toNNReal.comp continuous_subtype_val)).const_mul β))
  have H := integral_parisiFreeMeasure_continuous μ a ha hμ f hf
  have hz : f QuantitativePaper.zeroOverlap=scalarPrintedPotential β μ 0 0 := by
    simp [f,QuantitativePaper.zeroOverlap]
  rw [hz] at H
  have hfull : (∫q,f q ∂(μ : Measure Paper.Overlap))=
      Real.log 2+FRSB.forwardBrownianAction β μ 1 ω := by
    unfold f scalarPrintedPotential
    rw [integral_add (integrable_const _) (FRSB.integrable_parisiSchemeMeasure s _)]
    simp only [integral_const,probReal_univ,one_smul]
    congr 1
    unfold FRSB.forwardBrownianAction
    apply integral_congr_ae
    exact .of_forall fun q=>by
      dsimp only
      simp only [NNReal.coe_one,ite_eq_left q.property.2]
  change a*scalarPrintedPotential β μ 0 0+(∫q,f q ∂parisiFreeMeasure μ a)=_
  rw [H,hfull]
  ring

theorem scalarPrintedBrownianHistory_density (s : RSBScheme k) (β a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : Paper.parisiSchemeMeasure s ∈ QuantitativePaper.scalarFloor a)
    (p : Paper.BrownianSample×Bool) :
    scalarFiniteHistoryDensity s β (scalarPrintedBrownianHistoryMarkMap s β p) =
      scalarPrintedBrownianFreeDensity β (Paper.parisiSchemeMeasure s) a p := by
  let μ := Paper.parisiSchemeMeasure s
  let x := β*canonicalBrownian 1 p.1
  let A := FRSB.forwardBrownianAction β μ 1 p.1
  have ht : scalarPrintedBrownianHistory s β p.1 (Fin.last (k+2))=x := by
    simp only [scalarPrintedBrownianHistory,FRSB.historySample,Fin.val_last,
      FRSB.forwardSchemeTime_top s 1 (by norm_num) le_rfl]
    rfl
  rw [←scalarFiniteHistory_transition_spin_density]
  change FRSB.finiteHistoryDensity (FRSB.forwardSchemeWeight s β 1) (k+2)
    (scalarPrintedBrownianHistory s β p.1)*
      ENNReal.ofReal (scalarSpinWeight (scalarPrintedBrownianHistory s β p.1 (Fin.last (k+2))) p.2)=_
  rw [ht]
  unfold scalarPrintedBrownianHistory
  rw [FRSB.finiteHistoryDensity_eq_forwardBrownianWeight s β 1 (by norm_num)]
  have hfree := scalarPrintedPotential_root_free_action s β a ha hμ p.1
  have he : Paper.spinSign p.2*x-a*scalarPrintedPotential β μ 0 0-
      (∫q : Paper.Overlap,scalarPrintedPotential β μ q (β*canonicalBrownian (q : ℝ).toNNReal p.1)
        ∂parisiFreeMeasure μ a)=Paper.spinSign p.2*x-Real.log 2-A := by
    change a*scalarPrintedPotential β μ 0 0+_=Real.log 2+A at hfree
    linarith
  change ENNReal.ofReal (Real.exp (parisiCDF μ 1*parisiPotential β μ (1,x)-A))*
    ENNReal.ofReal (scalarSpinWeight x p.2)=_
  rw [parisiCDF_eq_one_of_one_le μ (by norm_num),one_mul,parisiPotential_terminal,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le]
  change ENNReal.ofReal (Real.exp (Real.log (Real.cosh x)-A)*scalarSpinWeight x p.2)=
    ENNReal.ofReal (Real.exp (Paper.spinSign p.2*x-a*scalarPrintedPotential β μ 0 0-
      ∫q : Paper.Overlap,scalarPrintedPotential β μ q (β*canonicalBrownian (q : ℝ).toNNReal p.1)
        ∂parisiFreeMeasure μ a))
  rw [he]
  congr 1
  rw [scalarSpinWeight,Real.exp_sub,Real.exp_log (Real.cosh_pos x),Real.exp_sub,
    Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  field_simp [(Real.cosh_pos x).ne',Real.exp_ne_zero A]

theorem scalarMarkedSpinLaw_printed_root_free_density (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : Paper.parisiSchemeMeasure s ∈ QuantitativePaper.scalarFloor a) :
    (scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s)).map
      (fun p=>(scalarSelectedHistory s β hβ p.1,p.2)) =
    (((canonicalBrownianMeasure).prod (Measure.count : Measure Bool)).withDensity
      (scalarPrintedBrownianFreeDensity β (Paper.parisiSchemeMeasure s) a)).map
        (scalarPrintedBrownianHistoryMarkMap s β) := by
  have hm : Measurable (scalarPrintedBrownianHistoryMarkMap s β) :=
    ((measurable_scalarPrintedBrownianHistory s β).comp measurable_fst).prodMk measurable_snd
  have he : (fun p=>scalarFiniteHistoryDensity s β (scalarPrintedBrownianHistoryMarkMap s β p)) =
      scalarPrintedBrownianFreeDensity β (Paper.parisiSchemeMeasure s) a :=
    funext (scalarPrintedBrownianHistory_density s β a ha hμ)
  rw [←he,FourPapersCommon.map_withDensity_pullback _ _ hm _ (measurable_scalarFiniteHistoryDensity s β),
    scalarMarkedSpinLaw_history_density]
  congr 1
  conv_lhs => rhs;rw [←Measure.map_id (μ:=(Measure.count : Measure Bool))]
  exact Measure.map_prod_map _ _ (measurable_scalarPrintedBrownianHistory s β) measurable_id

end QuantitativeFollowup
