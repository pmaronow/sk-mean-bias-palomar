module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowSecondSpatialSmooth
public import QuantitativeFollowup.ScalarFiniteRestartPointwiseLaw
public import OverlapPaper.ReplicaSourceGroupedMoments
public import OverlapPaper.ReplicaSourceSiteStepLaw
public import Paper.ParisiPDEFormula

@[expose] public section

/-! Pointwise scalar finite/native future-square agreement, with the actual
normalized Gaussian kernels and all repeated original profile nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets OverlapPaper
variable {k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFutureAgreement_scalar_aux_node (s : RSBScheme k) (β : ℝ)
    (p j : ℕ) (hp : p≤j) (hj : j≤k+2) (x : ℝ) :
    Paper.parisiFinitePotentialAux s β j (s.q (k+2-p)) x=parisiF s β p x := by
  induction j with
  | zero =>
      have he : p=0:=by omega
      subst p
      rfl
  | succ j ih =>
      by_cases he : p=j+1
      · subst p
        exact Paper.parisiFinitePotentialAux_left s β hj x
      · have hpj : p≤j:=by omega
        have hq : s.q (k+2-j) ≤ s.q (k+2-p):=
          s.q_mono' _ (by omega) _ (by omega)
        by_cases ht : s.q (k+2-p)≤ s.q (k+2-j)
        · have hqt:=le_antisymm ht hq
          have hv:=ih hpj (by omega)
          rw [hqt,Paper.parisiFinitePotentialAux_left s β (by omega) x] at hv
          simp only [Paper.parisiFinitePotentialAux,hqt,le_refl,ite_true,
            Paper.parisiSlabPotential_terminal]
          exact hv
        · simpa only [Paper.parisiFinitePotentialAux,if_neg ht] using ih hpj (by omega)

theorem cavityFutureAgreement_scalar_potential_node (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p : ℕ) (hp : p≤k+2) (x : ℝ) :
    Paper.parisiPotential β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),x)=
      parisiF s β p x := by
  rw [Paper.parisiSchemePotential_eq_actual s β hβ.ne' _ _
    ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩]
  have ht0 : 0≤ s.q (k+2-p):=s.q_nonneg (by omega)
  have ht1 : s.q (k+2-p)≤1:=s.q_le_one (by omega)
  simpa only [Paper.parisiFinitePotential,Prod.fst,Prod.snd,
    min_eq_right ht1,max_eq_right ht0] using
      cavityFutureAgreement_scalar_aux_node s β p (k+2) hp le_rfl x

theorem cavityFutureAgreement_scalar_gradient_node (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p : ℕ) (hp : p≤k+2) (x : ℝ) :
    Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),x)=
      parisiFDeriv s β p x := by
  have hd:=Paper.hasDerivAt_parisiPotential_spatial β hβ.ne' (Paper.parisiSchemeMeasure s)
    (s.q (k+2-p)) x ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
  have he : (fun y=>Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (s.q (k+2-p),y))=parisiF s β p:=
    funext (cavityFutureAgreement_scalar_potential_node s β hβ p hp)
  rw [he] at hd
  exact hd.unique ((parisiF_C2_props s β p).1.1 x)

theorem cavityFutureAgreement_scalar_depth_kernel (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p : ℕ) (hp : p≤k+1) :
    cavityScalarDepthKernel s β p=
      mixedSchemeScalarStep (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ))
        s (k+1-p) := by
  ext x : 1
  let ξ:=AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)
  have hpotential : (fun y=>mixedPotential ξ (Paper.parisiSchemeMeasure s)
      (s.q (k+1-p+1),y))=parisiF s β p := by
    funext y
    simp only [ξ,mixedPotential_quadratic,Real.sqrt_sq hβ.le,
      show k+1-p+1=k+2-p by omega]
    exact cavityFutureAgreement_scalar_potential_node s β hβ p (by omega) y
  have hvariance : ξ.first (s.q (k+1-p+1))-ξ.first (s.q (k+1-p))=
      β^2*(s.q (k+2-p)-s.q (k+1-p)) := by
    simp only [ξ,AdmissibleEvenMixture.quadratic_first,
      show k+1-p+1=k+2-p by omega]
    ring
  have hv : 0≤β^2*(s.q (k+2-p)-s.q (k+1-p)):=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (s.q_mono' _ (by omega) _ (by omega)))
  let v:=β^2*(s.q (k+2-p)-s.q (k+1-p))
  have hraw : (gaussianReal 0 1).map (fun z=>x+Real.sqrt v*z)=
      gaussianReal x v.toNNReal := by
    have hh:=ColeHopfFoundation.ProbabilityTheory.gaussianReal_map_sqrt_mul v.toNNReal
    rw [Real.coe_toNNReal _ hv] at hh
    have hs:=congrArg (fun P : Measure ℝ=>P.map (fun z=>x+z)) hh
    rw [Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_add,zero_add] at hs
    exact hs
  rw [cavityScalarDepthKernel_apply]
  have htilt : (fun z=>anisotropicSchemeMass s p*cavityScalarFinite s β p
      (x+Real.sqrt v*z))=(fun z=>anisotropicSchemeMass s p*parisiF s β p
        (x+Real.sqrt v*z)+anisotropicSchemeMass s p*Real.log 2) := by
    funext z
    rw [cavityScalarFinite]
    ring
  change ((gaussianReal 0 1).tilted
    (fun z=>anisotropicSchemeMass s p*cavityScalarFinite s β p (x+Real.sqrt v*z))).map _=_
  rw [htilt,tilted_add_const_eq]
  change ((gaussianReal 0 1).tilted
    ((fun y=>anisotropicSchemeMass s p*parisiF s β p y) ∘ (fun z=>x+Real.sqrt v*z))).map
      (fun z=>x+Real.sqrt v*z)=_
  rw [map_tilted_pullback (gaussianReal 0 1)
    (fun z=>x+Real.sqrt v*z) (by fun_prop) (fun y=>anisotropicSchemeMass s p*parisiF s β p y)
    ((parisiF_measurable s β p).const_mul _),hraw]
  change _=FRSB.constantMassKernel (s.m (k+1-p))
    (ξ.first (s.q (k+1-p+1))-ξ.first (s.q (k+1-p))).toNNReal _ x
  rw [constantMassKernel_eq_tilted _ _ _
    (continuous_mixedPotential_section ξ _ _)
    (mixedPotential_hasLinearGrowth ξ _ ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩) x,
    hvariance]
  simp_rw [show ∀ y,mixedPotential ξ (Paper.parisiSchemeMeasure s)
    (s.q (k+1-p+1),y)=parisiF s β p y from fun y=>congrFun hpotential y]
  rfl

theorem cavityFiniteRowFutureScalarSquare_eq_native (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p j : ℕ) (hp : p≤j) (hj : j≤k+2)
    (q r : Paper.Overlap) (hq : (q:ℝ)=s.q (k+2-j))
    (hr : (r:ℝ)=s.q (k+2-p)) (hqr : (q:ℝ)≤r) (x : ℝ) :
    cavityFiniteRowFutureScalarSquare s β p (j-p) x=
      scalarFutureSquare β (Paper.parisiSchemeMeasure s) q r hqr x := by
  let ξ:=AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)
  have htest : (fun y=>(parisiFDeriv s β p y)^2)=
      fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (r,y)^2 := by
    funext y
    rw [hr,cavityFutureAgreement_scalar_gradient_node s β hβ p (by omega)]
  unfold cavityFiniteRowFutureScalarSquare
  rw [sourceKernelExpectation_congr_kernels _
    (fun i=>mixedSchemeScalarStep ξ s ((k+2-j)+(j-p)-1-i)) (j-p) (fun i hi=>by
      rw [cavityFutureAgreement_scalar_depth_kernel s β hβ (p+i) (by omega)]
      congr 1
      omega),htest]
  have hf : Measurable (fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (r,y)^2) :=
    (((Paper.continuous_parisiGradient β (Paper.parisiSchemeMeasure s)).comp
      (continuous_const.prodMk continuous_id)).pow 2).measurable
  rw [scalar_reverse_endpoint_mean ξ s (k+2-j) (j-p) (by omega)
    (fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (r,y)^2) hf
    1 zero_le_one (fun y=>by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (by
        simpa only [Real.norm_eq_abs] using Paper.norm_parisiGradient_le_one β _ (r,y)))]
  exact scalarSchemeEndpoint_eq_futureSquare s β hβ (k+2-j) (j-p) (by omega)
    q r hq (by convert hr using 1 <;> congr 1 <;> omega) hqr x

theorem deriv_cavityFiniteRowFutureScalarSquare_eq_native (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p j : ℕ) (hp : p≤j) (hj : j≤k+2)
    (q r : Paper.Overlap) (hq : (q:ℝ)=s.q (k+2-j))
    (hr : (r:ℝ)=s.q (k+2-p)) (hqr : (q:ℝ)≤r) (x : ℝ) :
    deriv (cavityFiniteRowFutureScalarSquare s β p (j-p)) x=
      deriv (scalarFutureSquare β (Paper.parisiSchemeMeasure s) q r hqr) x := by
  have he:=funext (cavityFiniteRowFutureScalarSquare_eq_native s β hβ p j hp hj q r hq hr hqr)
  rw [he]

theorem contDiff_cavityFutureAgreement_scalarFutureSquare (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p j : ℕ) (hp : p≤j) (hj : j≤k+2)
    (q r : Paper.Overlap) (hq : (q:ℝ)=s.q (k+2-j))
    (hr : (r:ℝ)=s.q (k+2-p)) (hqr : (q:ℝ)≤r) :
    ContDiff ℝ ∞ (scalarFutureSquare β (Paper.parisiSchemeMeasure s) q r hqr) := by
  have he:=funext (cavityFiniteRowFutureScalarSquare_eq_native s β hβ p j hp hj q r hq hr hqr)
  rw [←he]
  exact contDiff_cavityFiniteRowFutureScalarSquare s β hβ p (j-p)

theorem hasDerivAt_cavityFiniteRowFutureScalarSquare_native (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p j : ℕ) (hp : p≤j) (hj : j≤k+2)
    (q r : Paper.Overlap) (hq : (q:ℝ)=s.q (k+2-j))
    (hr : (r:ℝ)=s.q (k+2-p)) (hqr : (q:ℝ)≤r) (x : ℝ) :
    HasDerivAt (cavityFiniteRowFutureScalarSquare s β p (j-p))
      (scalarFutureSquareDerivative β (Paper.parisiSchemeMeasure s) q r hqr x) x := by
  have he:=funext (cavityFiniteRowFutureScalarSquare_eq_native s β hβ p j hp hj q r hq hr hqr)
  rw [he]
  exact hasDerivAt_scalarFutureSquare β hβ.ne' _ q r hqr x

theorem deriv_cavityFiniteRowFutureScalarSquare_eq_restart_derivative (s : RSBScheme k) (β : ℝ)
    (hβ : 0<β) (p j : ℕ) (hp : p≤j) (hj : j≤k+2)
    (q r : Paper.Overlap) (hq : (q:ℝ)=s.q (k+2-j))
    (hr : (r:ℝ)=s.q (k+2-p)) (hqr : (q:ℝ)≤r) (x : ℝ) :
    deriv (cavityFiniteRowFutureScalarSquare s β p (j-p)) x=
      scalarFutureSquareDerivative β (Paper.parisiSchemeMeasure s) q r hqr x :=
  (hasDerivAt_cavityFiniteRowFutureScalarSquare_native s β hβ p j hp hj q r hq hr hqr x).deriv

end QuantitativeFollowup
