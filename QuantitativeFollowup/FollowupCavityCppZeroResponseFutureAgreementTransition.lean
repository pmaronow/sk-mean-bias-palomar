module
public import QuantitativeFollowup.AnisotropicRecordedProfileFiniteCell
public import QuantitativeFollowup.AnisotropicObservationSemigroup
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeMeanSquare

@[expose] public section

/-! Actual finite continuation expectations are the genuine native restart
kernel at original profile nodes. The observation state uses whitened fields;
the final restart observable uses the physical field. Repeated nodes remain. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets OverlapPaper
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFutureAgreement_node_mono (s : RSBScheme k) (i u : ℕ)
    (hi : i≤u) (hu : u≤k+2) :
    anisotropicFiniteMeshNode s i≤anisotropicFiniteMeshNode s u := by
  change (anisotropicFiniteMeshNode s i:ℝ)≤(anisotropicFiniteMeshNode s u:ℝ)
  rw [anisotropicFiniteMeshNode_coe s i (by omega),anisotropicFiniteMeshNode_coe s u hu]
  exact s.q_mono' u hu i hi

theorem cavityFutureAgreement_finite_expectation_transition (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i u : ℕ) (hi : i≤u) (hu : u≤k+2)
    (F : AnisotropicParameter n→ℝ) (hF : Measurable F) (B : ℝ)
    (hb : ∀P,‖F P‖≤B) (z : AnisotropicObservationState n) :
    anisotropicFiniteFutureExpectation D s i u F (anisotropicObservationParameter D z)=
      ∫y,F (anisotropicObservationParameter D y)
        ∂anisotropicObservationTransition D (Paper.parisiSchemeMeasure s)
          (anisotropicFiniteMeshNode s i) (anisotropicFiniteMeshNode s u) z := by
  induction u generalizing F z with
  | zero =>
      have hi0 : i=0:=by omega
      subst i
      simp only [anisotropicFiniteFutureExpectation,Nat.sub_self,sourceKernelExpectation,
        anisotropicObservationTransition_same_time,Kernel.id_apply,integral_dirac]
  | succ u ih =>
      by_cases he : i=u+1
      · subst i
        simp only [anisotropicFiniteFutureExpectation,Nat.sub_self,sourceKernelExpectation,
          anisotropicObservationTransition_same_time,Kernel.id_apply,integral_dirac]
      · have hi' : i≤u:=by omega
        have hu' : u≤k+1:=by omega
        let G : AnisotropicParameter n→ℝ:=
          fun P=>∫y,F y∂anisotropicFiniteTransition D s u P
        have hG : Measurable G:=hF.stronglyMeasurable.integral_kernel.measurable
        have hGb : ∀P,‖G P‖≤B:=fun P=>by
          simpa only [probReal_univ,mul_one] using
            norm_integral_le_of_norm_le_const (μ:=anisotropicFiniteTransition D s u P)
              (.of_forall hb)
        rw [anisotropicFiniteFutureExpectation_step D s i u hi' hu']
        rw [ih hi' (by omega) G hG hGb z]
        have hobs : Measurable (fun y=>F (anisotropicObservationParameter D y)):=
          hF.comp (measurable_anisotropicObservationParameter D)
        have hinner (y : AnisotropicObservationState n) :
            G (anisotropicObservationParameter D y)=
              ∫w,F (anisotropicObservationParameter D w)
                ∂anisotropicObservationTransition D (Paper.parisiSchemeMeasure s)
                  (anisotropicFiniteMeshNode s u) (anisotropicFiniteMeshNode s (u+1)) y := by
          dsimp only [G]
          rw [←anisotropicObservationTransition_scheme_parameter D s u hu' y]
          exact integral_map (measurable_anisotropicObservationParameter D).aemeasurable
            hF.aestronglyMeasurable
        simp_rw [hinner]
        exact (anisotropicObservationTransition_semigroup_mean D (Paper.parisiSchemeMeasure s)
          (anisotropicFiniteMeshNode s i) (anisotropicFiniteMeshNode s u)
          (anisotropicFiniteMeshNode s (u+1))
          (cavityFutureAgreement_node_mono s i u hi' (by omega))
          (cavityFutureAgreement_node_mono s u (u+1) (by omega) hu)
          z.1 z.2 _ hobs B (fun y=>hb _)).symm

theorem cavityFutureAgreement_restart_spin_square_transition (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) (x : Field n) (i : Fin n) :
    anisotropicRestartSpinSquare D μ g q x i r=
      ∫y,(anisotropicMeasureTailMagnetization D μ r
        (anisotropicObservationParameter D y) i)^2
        ∂anisotropicObservationTransition D μ q r (g,anisotropicInverseNoiseMap D x) := by
  have hF : Measurable (fun y : AnisotropicObservationState n=>
      (anisotropicMeasureTailMagnetization D μ r (anisotropicObservationParameter D y) i)^2) :=
    ((EuclideanSpace.proj i).measurable.comp
      ((measurable_anisotropicMeasureTailMagnetization D μ).comp
        (measurable_const.prodMk (measurable_anisotropicObservationParameter D)))).pow_const 2
  let z : AnisotropicObservationState n:=(g,anisotropicInverseNoiseMap D x)
  let t : ℝ≥0:=((r:ℝ)-(q:ℝ)).toNNReal
  have ht : (t:ℝ)=(r:ℝ)-(q:ℝ):=Real.coe_toNNReal _ (sub_nonneg.mpr hqr)
  have htH : t≤vectorRestartHorizon q := by
    rw [←NNReal.coe_le_coe,vectorRestartHorizon,ht,
      Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)]
    linarith [r.property.2]
  have hm : Measurable (fun W : VectorWienerPath n=>anisotropicObservationNoiseAdvance D μ q r (z,W)) :=
    (measurable_anisotropicObservationNoiseAdvance D μ q r).comp
      (measurable_const.prodMk measurable_id)
  have hc : HasLaw (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n):=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  rw [anisotropicObservationTransition_apply]
  change _=∫y,(anisotropicMeasureTailMagnetization D μ r
    (anisotropicObservationParameter D y) i)^2
    ∂(vectorWienerMeasure n).map (fun W=>anisotropicObservationNoiseAdvance D μ q r (z,W))
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
  have hci:=hc.integral_comp (hF.comp hm).aestronglyMeasurable
  simp only [Function.comp_def] at hci
  rw [←hci]
  unfold anisotropicRestartSpinSquare
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change _=(anisotropicMeasureTailMagnetization D μ r
      (anisotropicObservationParameter D (g,anisotropicRestartNoiseStatePath D μ q
        (z,vectorCanonicalBrownianPath sample.2) ((r:ℝ)-(q:ℝ)))) i)^2
    rw [←ht,anisotropicRestartNoiseStatePath_canonical D μ g q
      (anisotropicInverseNoiseMap D x) t htH sample]
    rfl

theorem cavityFutureAgreement_finite_coordinate_square (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (p j : ℕ) (hp : p≤j) (hj : j≤k+2)
    (g : AnisotropicDisorder n) (x : Field n) (i : Fin n) :
    sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (p+r)) (j-p)
      (fun P=>(anisotropicFiniteFeatureMean D s p (fun σ=>Paper.spinSign (σ i)) P)^2)
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)=
      anisotropicRestartSpinSquare D (Paper.parisiSchemeMeasure s) g
        (anisotropicFiniteMeshNode s (k+2-j)) x i (anisotropicFiniteMeshNode s (k+2-p)) := by
  let F : AnisotropicParameter n→ℝ:=fun P=>
    (anisotropicFiniteFeatureMean D s p (fun σ=>Paper.spinSign (σ i)) P)^2
  have hF : Measurable F:=(measurable_anisotropicFiniteFeatureMean D s p _).pow_const 2
  have hb : ∀P,‖F P‖≤(1:ℝ):=fun P=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply (sq_le_one_iff_abs_le_one _).mpr
    unfold anisotropicFiniteFeatureMean
    rw [←anisotropicMagnetization_eq_spin_mean]
    exact anisotropicMagnetization_component_bound D s p P i
  have he:=cavityFutureAgreement_finite_expectation_transition D s (k+2-j) (k+2-p)
    (by omega) (by omega) F hF 1 hb (g,anisotropicInverseNoiseMap D x)
  have hdepth : k+2-(k+2-p)=p:=by omega
  have hlen : (k+2-p)-(k+2-j)=j-p:=by omega
  have hparam : anisotropicObservationParameter D (g,anisotropicInverseNoiseMap D x)=
      anisotropicDisorderInjection n g+anisotropicFieldInjection n x := by
    simp only [anisotropicObservationParameter,anisotropicUnitInput,
      ContinuousLinearMap.comp_apply,anisotropicNoiseMap_inverseNoise]
  simp only [anisotropicFiniteFutureExpectation,hdepth,hlen,hparam] at he
  rw [cavityFutureAgreement_restart_spin_square_transition D _ g _ _
    (cavityFutureAgreement_node_mono s (k+2-j) (k+2-p) (by omega) (by omega)) x i]
  refine he.trans ?_
  apply integral_congr_ae
  exact .of_forall fun y=>by
    dsimp only [F]
    rw [anisotropicMeasureTailMagnetization_scheme_eq_finite]
    have hn : anisotropicFiniteMeshNode s (k+2-p)=
        anisotropicSchemeNode s (k+2-p) (by omega) :=
      Subtype.ext (anisotropicFiniteMeshNode_coe s _ (by omega))
    rw [hn,anisotropicFiniteTailMagnetization_node,hdepth,
      anisotropicMagnetization_eq_spin_mean]
    rfl

end QuantitativeFollowup
