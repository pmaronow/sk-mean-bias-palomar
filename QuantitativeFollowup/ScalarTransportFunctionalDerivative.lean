module
public import QuantitativeFollowup.ScalarTransportFunctionalBasics
public import QuantitativeFollowup.ScalarTransportNodeVariation

@[expose] public section

/-! Actual first and second derivatives of the finite-profile Parisi
functional under endpoint-fixed overlap transports. Finite integration is
performed against the literal scheme law, including repeated atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportFirstDerivative (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) : ℝ :=
  β^2/2*(∫q : Paper.Overlap,φ q*((scalarLevelTransport φ u q:ℝ)-
    Gamma β (scalarTransportMeasure μ φ u) (scalarLevelTransport φ u q)) ∂(μ:Measure Paper.Overlap))

theorem hasDerivAt_scalarScheme_integral (s : RSBScheme k)
    (F : Paper.Overlap→ℝ→ℝ) (D : Paper.Overlap→ℝ) (u : ℝ)
    (hF : ∀ q,HasDerivAt (F q) (D q) u) :
    HasDerivAt (fun v=>∫q,F q v ∂(parisiSchemeMeasure s:Measure Paper.Overlap))
      (∫q,D q ∂(parisiSchemeMeasure s:Measure Paper.Overlap)) u := by
  simp only [integral_scalarScheme_nodes]
  convert! HasDerivAt.sum (u:=Finset.univ)
    (fun (i : Fin (k+1)) _=>
      (hF (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))).const_mul (s.m (i+1)-s.m i)) using 1
  funext v
  simp only [Finset.sum_apply]

theorem hasDerivAt_scalarLevelTransport_coe (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ)
    (hu : |u| *L<1) (q : Paper.Overlap) :
    HasDerivAt (fun v : ℝ=>(scalarLevelTransport φ v q:ℝ)) (φ q) u := by
  have he : (fun v : ℝ=>(scalarLevelTransport φ v q:ℝ))=ᶠ[𝓝 u]
      fun v=>(q:ℝ)+v*φ q := by
    filter_upwards [(isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds hu]
      with v hv
    exact scalarLevelTransport_eq_affine φ L hφ h0 h1 v hv.le q
  simpa only [one_mul] using
    (((hasDerivAt_id u).mul_const (φ q)).const_add (q:ℝ)).congr_of_eventuallyEq he

theorem scalarTransportFutureSquare_root (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0) (u : ℝ) (q : Paper.Overlap) :
    scalarTransportFutureSquare β μ φ u 0 q 0=
      Gamma β (scalarTransportMeasure μ φ u) (scalarLevelTransport φ u q) := by
  rw [scalarTransportFutureSquare,scalarLevelTransport_root φ h0 u,
    scalarFutureSquare_root β hβ]

theorem scalarTransportPotentialVariation_root (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0) (u : ℝ) :
    scalarTransportPotentialVariation β μ φ u 0 0=
      -(β^2/2)*(∫q : Paper.Overlap,φ q*
        Gamma β (scalarTransportMeasure μ φ u) (scalarLevelTransport φ u q)
        ∂(μ:Measure Paper.Overlap)) := by
  unfold scalarTransportPotentialVariation
  simp only [h0,zero_mul,zero_add,scalarTransportFutureSquare_root β hβ μ φ h0 u]
  congr 1
  rw [←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact .of_forall fun q=>by
    by_cases hq : (0:Paper.Overlap)<q
    · simp only [indicator_apply,mem_Ioi,ite_eq_left hq]
    · have hz : q=(0:Paper.Overlap) := le_antisymm (le_of_not_gt hq) q.property.1
      subst q
      simp [h0]

theorem hasDerivAt_scalarTransportRootPotential (s : RSBScheme k) (β : ℝ) (hβ : 0<β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (hu : |u|<δ) :
    HasDerivAt (fun v=>parisiPotential β (scalarTransportMeasure (parisiSchemeMeasure s) φ v) (0,0))
      (-(β^2/2)*(∫q : Paper.Overlap,φ q*
        Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u) (scalarLevelTransport φ u q)
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap))) u := by
  have hz : scalarSchemeTransportNode s 0=(0:Paper.Overlap) := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe s 0 (by omega),s.q_zero]
    rfl
  have hd := hasDerivAt_scalarTransportNodePotential_variation s β hβ φ L hφ h0 h1 δ u 0
    hδ hsmall hu (k+2) le_rfl
  simp only [Nat.sub_self,hz,scalarTransportPotentialVariation_root β hβ.ne' _ φ h0 u] at hd
  simpa only [scalarTransportNodePotential,hz,scalarLevelTransport_root φ h0,
    show ((0:Paper.Overlap):ℝ)=0 from rfl] using hd

theorem hasDerivAt_scalarTransportFunctional (s : RSBScheme k) (β : ℝ) (hβ : 0<β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (hu : |u|<δ) :
    HasDerivAt (scalarTransportFunctional β (parisiSchemeMeasure s) φ)
      (scalarTransportFirstDerivative β (parisiSchemeMeasure s) φ u) u := by
  have husmall : |u| *L<1 :=
    (mul_le_mul_of_nonneg_right hu.le L.coe_nonneg).trans_lt hsmall
  have hP := hasDerivAt_scalarTransportRootPotential s β hβ φ L hφ h0 h1 δ u hδ hsmall hu
  have hQ := hasDerivAt_scalarScheme_integral s
    (fun q v=>(scalarLevelTransport φ v q:ℝ)^2)
    (fun q=>2*(scalarLevelTransport φ u q:ℝ)*φ q) u
    (fun q=>by
      convert! (hasDerivAt_scalarLevelTransport_coe φ L hφ h0 h1 u husmall q).pow 2 using 1
      simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one])
  have hd := ((hP.const_add (Real.log 2)).sub_const (β^2/4)).add (hQ.const_mul (β^2/4))
  have hI1 : Integrable (fun q : Paper.Overlap=>φ q*(scalarLevelTransport φ u q:ℝ))
      (parisiSchemeMeasure s:Measure Paper.Overlap) :=
    integrable_overlap_continuous
      (φ.continuous.mul (continuous_subtype_val.comp (continuous_scalarLevelTransport_parameter φ u))) _
  have hI2 : Integrable (fun q : Paper.Overlap=>φ q*
      Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u) (scalarLevelTransport φ u q))
      (parisiSchemeMeasure s:Measure Paper.Overlap) := by
    apply integrable_overlap_continuous
    exact φ.continuous.mul ((continuousOn_Gamma β hβ.ne' _).comp_continuous
      (continuous_subtype_val.comp (continuous_scalarLevelTransport_parameter φ u))
      (fun q=>(scalarLevelTransport φ u q).property))
  have he : scalarTransportFirstDerivative β (parisiSchemeMeasure s) φ u=
      -(β^2/2)*(∫q : Paper.Overlap,φ q*
        Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u) (scalarLevelTransport φ u q)
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap))+
      β^2/4*(∫q : Paper.Overlap,2*(scalarLevelTransport φ u q:ℝ)*φ q
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap)) := by
    rw [scalarTransportFirstDerivative]
    simp_rw [mul_sub]
    rw [integral_sub hI1 hI2]
    have htwo : (∫q : Paper.Overlap,2*(scalarLevelTransport φ u q:ℝ)*φ q
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap))=
        2*(∫q : Paper.Overlap,φ q*(scalarLevelTransport φ u q:ℝ)
          ∂(parisiSchemeMeasure s:Measure Paper.Overlap)) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun q=>by ring
    rw [htwo]
    ring
  rw [he]
  exact hd.congr_of_eventuallyEq (.of_forall fun v=>scalarTransportFunctional_eq_second_moment β _ φ v)

theorem hasDerivAt_scalarTransportFirstDerivative_zero (s : RSBScheme k) (β : ℝ) (hβ : 0<β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    HasDerivAt (scalarTransportFirstDerivative β (parisiSchemeMeasure s) φ)
      (β^2/2*(∫q : Paper.Overlap,φ q*(φ q-
        scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q)
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap))) 0 := by
  have hT (q : Paper.Overlap) := hasDerivAt_scalarLevelTransport_coe φ L hφ h0 h1 0
    (by simp : |(0:ℝ)| *L<1) q
  have hG (q : Paper.Overlap) := hasDerivAt_scalarTransportGamma_seven_terms s β hβ φ L hφ h0 h1
    δ hδ hsmall a ha hμ q
  exact (hasDerivAt_scalarScheme_integral s _ _ 0
    (fun q=>((hT q).sub (hG q)).const_mul (φ q))).const_mul (β^2/2)

theorem hasDerivAt_deriv_scalarTransportFunctional_zero (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    HasDerivAt (deriv (scalarTransportFunctional β (parisiSchemeMeasure s) φ))
      (β^2/2*(∫q : Paper.Overlap,φ q*(φ q-
        scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ q)
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap))) 0 := by
  have he : deriv (scalarTransportFunctional β (parisiSchemeMeasure s) φ)=ᶠ[𝓝 (0:ℝ)]
      scalarTransportFirstDerivative β (parisiSchemeMeasure s) φ := by
    have hz : (0:ℝ)∈Ioo (-δ) δ := by constructor <;> linarith
    filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
    exact (hasDerivAt_scalarTransportFunctional s β hβ φ L hφ h0 h1 δ u
      hδ hsmall (abs_lt.mpr hu)).deriv
  exact (hasDerivAt_scalarTransportFirstDerivative_zero s β hβ φ L hφ h0 h1
    δ hδ hsmall a ha hμ).congr_of_eventuallyEq he

end QuantitativeFollowup
