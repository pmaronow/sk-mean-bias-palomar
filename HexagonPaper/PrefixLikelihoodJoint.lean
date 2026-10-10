module
public import HexagonPaper.PrefixLikelihoodAllProfiles
public import QuantitativeFollowup.SupportingPrintedScalarRootFreeDensity

@[expose] public section

/-! The exact marked scalar likelihood for arbitrary overlap profiles. The
law is the actual diffusion with its actual conditional terminal spin, and
the reference law is the full Gaussian path times counting measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open QuantitativeFollowup QuantitativePaper SpinGlass.Targets
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem scalarStoppedBrownianPath_one (β : ℝ) (sample : Paper.BrownianSample) :
    scalarStoppedBrownianPath β 1 sample=scaledBrownianPath β (canonicalBrownianPath sample) := by
  ext q
  change β*canonicalBrownian (stoppedOverlapTime 1 q) sample=
    β*canonicalBrownian (q:ℝ).toNNReal sample
  have ht : stoppedOverlapTime 1 q=(q:ℝ).toNNReal := by
    apply NNReal.eq
    change min (q:ℝ) 1=Real.toNNReal (q:ℝ)
    rw [min_eq_left q.property.2,Real.coe_toNNReal _ q.property.1]
  rw [ht]

theorem scalarStoppedStatePath_terminal (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (sample : Paper.BrownianSample) :
    scalarStoppedStatePath β μ 1 sample 1=parisiPhysicalSplitState β 0 μ 1 sample := by
  rw [parisiPhysicalSplitState_eq_selected β hβ]
  change optimalStateReal β μ sample (min (1:ℝ) 1)=_
  simp only [min_self,Real.toNNReal_one]
  rw [←optimalState_eq_selected β hβ]
  change optimalStateReal β μ sample 1=optimalState β μ (1:ℝ).toNNReal sample
  rw [Real.toNNReal_one]
  exact (optimalState_eq_real β μ (by norm_num : ((1:ℝ≥0):ℝ)≤1) sample).symm

def scalarFullPathSpinKernel : Kernel C(Paper.Overlap,ℝ) Bool :=
  scalarSpinMarkKernel (fun p=>p 1) (ContinuousMap.measurable_eval _)

instance scalarFullPathSpinKernel_markov : IsMarkovKernel scalarFullPathSpinKernel :=
  scalarSpinMarkKernel_markov _ _

theorem scalarMarkedSpinLaw_fullPath_map (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) :
    (scalarMarkedSpinLaw β hβ μ).map (fun p=>(scalarStoppedStatePath β μ 1 p.1,p.2))=
      (canonicalBrownianMeasure.map (scalarStoppedStatePath β μ 1)) ⊗ₘ scalarFullPathSpinKernel := by
  have hm := measurable_scalarStoppedStatePath β hβ μ 1 (by norm_num)
  have he := compProd_comap_map_history canonicalBrownianMeasure
    (scalarStoppedStatePath β μ 1) hm scalarFullPathSpinKernel
  have hk : scalarFullPathSpinKernel.comap (scalarStoppedStatePath β μ 1) hm=
      scalarTerminalSpinKernel β hβ μ := by
    ext sample : 1
    change scalarSpinLaw (scalarStoppedStatePath β μ 1 sample 1)=
      scalarSpinLaw (parisiPhysicalSplitState β 0 μ 1 sample)
    rw [scalarStoppedStatePath_terminal β hβ μ sample]
  rw [hk] at he
  exact he

theorem scalarStoppedPath_likelihood_pathDensity (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) :
    canonicalBrownianMeasure.map (scalarStoppedStatePath β μ 1)=
      (canonicalBrownianMeasure.map (scalarStoppedBrownianPath β 1)).withDensity
        (forwardPathWeight β μ 1 (by norm_num)) := by
  rw [scalarStoppedPath_likelihood β hβ μ 1 (by norm_num),
    ←FRSB.map_withDensity_pullback canonicalBrownianMeasure
      (scalarStoppedBrownianPath β 1) (measurable_scalarStoppedBrownianPath β 1)
      (forwardPathWeight β μ 1 (by norm_num))
      (measurable_forwardPathWeight β μ 1 (by norm_num))]
  congr 1
  congr 1
  funext sample
  rw [scalarStoppedBrownianPath_one,
    forwardPathWeight_scaledBrownian β μ 1 (by norm_num),Real.toNNReal_one]

theorem scalarPrintedPotential_root_free_action_allProfiles (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (sample : Paper.BrownianSample) :
    a*scalarPrintedPotential β μ 0 0+
      (∫q : Paper.Overlap,scalarPrintedPotential β μ q
        (β*canonicalBrownian (q:ℝ).toNNReal sample) ∂parisiFreeMeasure μ a)=
          Real.log 2+forwardBrownianAction β μ 1 sample := by
  let f := fun q : Paper.Overlap=>scalarPrintedPotential β μ q
    (β*canonicalBrownian (q:ℝ).toNNReal sample)
  have hf : Continuous f := by
    unfold f scalarPrintedPotential
    exact continuous_const.add ((continuous_parisiPotential β μ).comp
      (continuous_subtype_val.prodMk (((continuous_canonicalBrownian sample).comp
        (continuous_real_toNNReal.comp continuous_subtype_val)).const_mul β)))
  have H := integral_parisiFreeMeasure_continuous μ a ha hμ f hf
  have hz : f zeroOverlap=scalarPrintedPotential β μ 0 0 := by
    simp [f,zeroOverlap]
  rw [hz] at H
  have hi : Integrable (fun q : Paper.Overlap=>parisiPotential β μ
      (q,β*canonicalBrownian (q:ℝ).toNNReal sample)) (μ : Measure Paper.Overlap) := by
    apply Integrable.of_bound
      (((continuous_parisiPotential β μ).comp (continuous_subtype_val.prodMk
        (((continuous_canonicalBrownian sample).comp
          (continuous_real_toNNReal.comp continuous_subtype_val)).const_mul β))).measurable.aestronglyMeasurable)
      (β^2+|β| *‖canonicalBrownianPath sample‖)
    exact .of_forall (scalarBrownianPotential_bound β μ sample)
  have hfull : (∫q,f q ∂(μ : Measure Paper.Overlap))=
      Real.log 2+forwardBrownianAction β μ 1 sample := by
    unfold f scalarPrintedPotential
    rw [integral_add (integrable_const _) hi]
    simp only [integral_const,probReal_univ,one_smul]
    congr 1
    unfold forwardBrownianAction
    exact integral_congr_ae (.of_forall fun q=>by simp only [NNReal.coe_one,ite_eq_left q.property.2])
  change a*scalarPrintedPotential β μ 0 0+(∫q,f q ∂parisiFreeMeasure μ a)=_
  rw [H,hfull]
  ring

theorem scalarPrefixSpinDensity_eq_printed_allProfiles (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (p : Paper.BrownianSample×Bool) :
    forwardBrownianWeight β μ 1 p.1 * ENNReal.ofReal
      (scalarSpinWeight (β*canonicalBrownian 1 p.1) p.2)=scalarPrintedBrownianFreeDensity β μ a p := by
  let x := β*canonicalBrownian 1 p.1
  let A := forwardBrownianAction β μ 1 p.1
  have hf := scalarPrintedPotential_root_free_action_allProfiles β μ a ha hμ p.1
  have he : Paper.spinSign p.2*x-a*scalarPrintedPotential β μ 0 0-
      (∫q : Paper.Overlap,scalarPrintedPotential β μ q (β*canonicalBrownian (q:ℝ).toNNReal p.1)
        ∂parisiFreeMeasure μ a)=Paper.spinSign p.2*x-Real.log 2-A := by
    change a*scalarPrintedPotential β μ 0 0+_=Real.log 2+A at hf
    linarith
  change ENNReal.ofReal (Real.exp (parisiCDF μ 1*parisiPotential β μ (1,x)-A))*
    ENNReal.ofReal (scalarSpinWeight x p.2)=_
  rw [parisiCDF_eq_one_of_one_le μ (by norm_num),one_mul,parisiPotential_terminal,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le]
  change ENNReal.ofReal (Real.exp (Real.log (Real.cosh x)-A)*scalarSpinWeight x p.2)=
    ENNReal.ofReal (Real.exp (Paper.spinSign p.2*x-a*scalarPrintedPotential β μ 0 0-
      ∫q : Paper.Overlap,scalarPrintedPotential β μ q (β*canonicalBrownian (q:ℝ).toNNReal p.1)
        ∂parisiFreeMeasure μ a))
  rw [he]
  congr 1
  rw [scalarSpinWeight,Real.exp_sub,Real.exp_log (Real.cosh_pos x),Real.exp_sub,
    Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)]
  field_simp [(Real.cosh_pos x).ne',Real.exp_ne_zero A]

/-- The printed source joint scalar/spin law on the full continuous path,
with the exact prescribed root split and all atoms of the free profile. -/
theorem scalarMarkedSpinLaw_fullPath_printed_density (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    (scalarMarkedSpinLaw β hβ μ).map (fun p=>(scalarStoppedStatePath β μ 1 p.1,p.2))=
      ((canonicalBrownianMeasure.prod (Measure.count : Measure Bool)).withDensity
        (scalarPrintedBrownianFreeDensity β μ a)).map
          (fun p=>(scalarStoppedBrownianPath β 1 p.1,p.2)) := by
  rw [scalarMarkedSpinLaw_fullPath_map β hβ μ,scalarStoppedPath_likelihood_pathDensity β hβ μ]
  have hk : scalarFullPathSpinKernel=
      (Kernel.const C(Paper.Overlap,ℝ) (Measure.count : Measure Bool)).withDensity
        (fun h e=>ENNReal.ofReal (scalarSpinWeight (h 1) e)) :=
    scalarSpinMarkKernel_eq_withDensity _ _
  haveI : IsSFiniteKernel ((Kernel.const C(Paper.Overlap,ℝ) (Measure.count : Measure Bool)).withDensity
      (fun h e=>ENNReal.ofReal (scalarSpinWeight (h 1) e))) := by
    rw [←hk]
    infer_instance
  rw [hk,Measure.withDensity_compProd_withDensity
    (measurable_forwardPathWeight β μ 1 (by norm_num))
      (measurable_scalarSpinMarkWeight (fun h : C(Paper.Overlap,ℝ)=>h 1)
        (ContinuousMap.measurable_eval _)),Measure.compProd_const]
  have hm : Measurable (fun p : Paper.BrownianSample×Bool=>(scalarStoppedBrownianPath β 1 p.1,p.2)) :=
    ((measurable_scalarStoppedBrownianPath β 1).comp measurable_fst).prodMk measurable_snd
  have hprod : (canonicalBrownianMeasure.map (scalarStoppedBrownianPath β 1)).prod
      (Measure.count : Measure Bool)=(canonicalBrownianMeasure.prod (Measure.count : Measure Bool)).map
        (fun p=>(scalarStoppedBrownianPath β 1 p.1,p.2)) := by
    conv_lhs => rhs;rw [←Measure.map_id (μ:=(Measure.count : Measure Bool))]
    exact Measure.map_prod_map _ _ (measurable_scalarStoppedBrownianPath β 1) measurable_id
  rw [hprod]
  let D : C(Paper.Overlap,ℝ)×Bool→ℝ≥0∞ := fun p=>
    forwardPathWeight β μ 1 (by norm_num) p.1*ENNReal.ofReal (scalarSpinWeight (p.1 1) p.2)
  have hD : Measurable D :=
    ((measurable_forwardPathWeight β μ 1 (by norm_num)).comp measurable_fst).mul
      (measurable_scalarSpinMarkWeight (fun h : C(Paper.Overlap,ℝ)=>h 1)
        (ContinuousMap.measurable_eval _))
  change ((canonicalBrownianMeasure.prod (Measure.count : Measure Bool)).map
    (fun p=>(scalarStoppedBrownianPath β 1 p.1,p.2))).withDensity D=_
  rw [←FRSB.map_withDensity_pullback _ _ hm D hD]
  congr 2
  funext p
  change forwardPathWeight β μ 1 (by norm_num) (scalarStoppedBrownianPath β 1 p.1)*
    ENNReal.ofReal (scalarSpinWeight (scalarStoppedBrownianPath β 1 p.1 1) p.2)=_
  rw [scalarStoppedBrownianPath_one,
    forwardPathWeight_scaledBrownian β μ 1 (by norm_num),Real.toNNReal_one]
  change forwardBrownianWeight β μ 1 p.1*ENNReal.ofReal
    (scalarSpinWeight (β*canonicalBrownian (1:ℝ).toNNReal p.1) p.2)=_
  rw [Real.toNNReal_one]
  exact scalarPrefixSpinDensity_eq_printed_allProfiles β μ a ha hμ p

theorem isProbabilityMeasure_scalarPrintedBrownianFreeDensity (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    IsProbabilityMeasure ((canonicalBrownianMeasure.prod (Measure.count : Measure Bool)).withDensity
      (scalarPrintedBrownianFreeDensity β μ a)) := by
  have hm : Measurable (fun p : Paper.BrownianSample×Bool=>(scalarStoppedBrownianPath β 1 p.1,p.2)) :=
    ((measurable_scalarStoppedBrownianPath β 1).comp measurable_fst).prodMk measurable_snd
  haveI : IsProbabilityMeasure (((canonicalBrownianMeasure.prod (Measure.count : Measure Bool)).withDensity
      (scalarPrintedBrownianFreeDensity β μ a)).map
        (fun p=>(scalarStoppedBrownianPath β 1 p.1,p.2))) := by
    rw [←scalarMarkedSpinLaw_fullPath_printed_density β hβ μ a ha hμ]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map hm.aemeasurable

end HexagonPaper
