module
public import QuantitativeFollowup.AnisotropicRestartLevelContinuity
public import QuantitativeFollowup.AnisotropicRecordedProfileLawConvergence

@[expose] public section

/-! Weak convergence of the actual observation genealogy when its profile
and every retained observation level move. CDF atoms and coinciding
observation levels remain part of the actual process. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal Topology BoundedContinuousFunction
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem tendsto_anisotropicRecordedProfileTreeProbability_moving_schedule
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (q : L→ℕ→Paper.Overlap) (Q : ℕ→Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hq : ∀p,p≤J→Tendsto (fun j=>q j p) l (𝓝 (Q p)))
    (hm : ∀j,∀p,p<J→q j (p+1)≤q j p) (hM : ∀p,p<J→Q (p+1)≤Q p)
    (g : AnisotropicDisorder n) {x : L→Field n} {y : Field n} (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun j=>anisotropicRecordedProfileTreeProbability D (μ j) (q j) T (g,x j)) l
      (𝓝 (anisotropicRecordedProfileTreeProbability D ν Q T (g,y))) := by
  induction T generalizing x y with
  | leaf =>
      have hP : Tendsto (fun j=>anisotropicEnergyMap D (anisotropicObservationParameter D (g,x j))) l
          (𝓝 (anisotropicEnergyMap D (anisotropicObservationParameter D (g,y)))) :=
        (anisotropicEnergyMap D).continuous.tendsto _ |>.comp
          ((tendsto_const_nhds (x:=anisotropicDisorderInjection n g)).add
            ((anisotropicUnitInput D).continuous.tendsto y |>.comp hx))
      exact (continuous_finiteStateGibbsProbability (fun _:Configuration n=>0)).tendsto _ |>.comp hP
  | @advance J T ih =>
      haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
      intro f
      have hfun : (fun i:L=>∫v,f v ∂(anisotropicRecordedProfileTreeProbability D (μ i) (q i) (.advance T) (g,x i):Measure _))=
          (fun i=>∫W,∫v,f v ∂(anisotropicRecordedProfileJointProbability D (μ i) (q i) T
            (anisotropicObservationNoiseAdvance D (μ i) (q i (J+1)) (q i J) ((g,x i),W)):Measure _)
              ∂vectorWienerMeasure n) := by
        funext i
        exact anisotropicRecordedProfileTreeProbability_advance_integral D (μ i) (q i) T (g,x i) f
      rw [hfun,anisotropicRecordedProfileTreeProbability_advance_integral D ν Q T (g,y) f]
      have hsub (j : L) : ((q j J:Paper.Overlap):ℝ)-((q j (J+1):Paper.Overlap):ℝ)∈
          Icc (0:ℝ) (1-((q j (J+1):Paper.Overlap):ℝ)) :=
        ⟨sub_nonneg.mpr (hm j J (Nat.lt_succ_self J)),sub_le_sub_right (q j J).property.2 _⟩
      have hSub : ((Q J:Paper.Overlap):ℝ)-((Q (J+1):Paper.Overlap):ℝ)∈
          Icc (0:ℝ) (1-((Q (J+1):Paper.Overlap):ℝ)) :=
        ⟨sub_nonneg.mpr (hM J (Nat.lt_succ_self J)),sub_le_sub_right (Q J).property.2 _⟩
      let X:=fun j W=>anisotropicRestartNoiseStatePath D (μ j) (q j (J+1)) ((g,x j),W)
        ((q j J:ℝ)-(q j (J+1):ℝ))
      let Y:=fun W=>anisotropicRestartNoiseStatePath D ν (Q (J+1)) ((g,y),W)
        ((Q J:ℝ)-(Q (J+1):ℝ))
      have htime : Tendsto (fun j=>(q j J:ℝ)-(q j (J+1):ℝ)) l (𝓝 ((Q J:ℝ)-(Q (J+1):ℝ))) :=
        (continuous_subtype_val.tendsto _ |>.comp (hq J (by omega))).sub
          (continuous_subtype_val.tendsto _ |>.comp (hq (J+1) le_rfl))
      have hX (W : VectorWienerPath n) : Tendsto (fun j=>X j W) l (𝓝 (Y W)) :=
        tendsto_anisotropicRestartNoiseStatePath_profile_level D hμ g (hq (J+1) le_rfl) hx W htime hsub hSub
      have hp (W : VectorWienerPath n) : Tendsto (fun j=>
          anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,X j W)) l
          (𝓝 (anisotropicRecordedProfileJointProbability D ν Q T (g,Y W))) := by
        have ht:=ih (fun p h=>hq p (by omega)) (fun j p h=>hm j p (by omega))
          (fun p h=>hM p (by omega)) (hX W)
        have hz := (tendsto_const_nhds (x:=g)).prodMk_nhds (hX W)
        have hh:=ProbabilityMeasure.continuous_prod.tendsto _ |>.comp
          ((tendsto_dirac_probability hz).prodMk_nhds ht)
        simpa only [anisotropicRecordedProfileJointProbability,Function.comp_def] using hh
      have hmj (j : L) : AEStronglyMeasurable (fun W=>∫v,f v
          ∂(anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,X j W):Measure _))
          (vectorWienerMeasure n) := by
        have hs : Measurable (X j):=measurable_anisotropicRestartNoiseStatePath_section
          D (μ j) (q j (J+1)) g (x j) ((q j J:ℝ)-(q j (J+1):ℝ))
        have hmap : Measurable (fun W : VectorWienerPath n=>(g,X j W)):=measurable_const.prodMk hs
        exact ((measurable_anisotropicRecordedProfileJointMean D (μ j) (q j) T f).comp hmap).aestronglyMeasurable
      have hb (j : L) (W : VectorWienerPath n) :
          ‖∫v,f v ∂(anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,X j W):Measure _)‖≤‖f‖ := by
        simpa only [probReal_univ,mul_one] using
          norm_integral_le_of_norm_le_const
            (μ:=(anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,X j W):Measure _))
            (.of_forall f.norm_coe_le_norm)
      have hi:=tendsto_integral_filter_of_dominated_convergence (fun _:VectorWienerPath n=>‖f‖)
        (.of_forall hmj) (.of_forall fun j=>.of_forall (hb j)) (integrable_const ‖f‖)
        (.of_forall fun W=>ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hp W) f)
      simpa only [anisotropicObservationNoiseAdvance,X,Y,Function.comp_def] using hi
  | fork T U ihT ihU =>
      haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) U):=inferInstance
      haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) U):=inferInstance
      haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
      haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) U):=inferInstance
      have h:=ProbabilityMeasure.continuous_prod.tendsto _ |>.comp
        ((ihT hq hm hM hx).prodMk_nhds (ihU hq hm hM hx))
      simpa only [anisotropicRecordedProfileTreeProbability_fork,Function.comp_def] using h

end QuantitativeFollowup
