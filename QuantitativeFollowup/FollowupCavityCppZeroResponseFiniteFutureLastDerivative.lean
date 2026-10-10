module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFutureProduct

@[expose] public section

/-! Actual spatial derivatives of the averaged incident-feature future
square. The pointwise finite/native product is an equality of field
functions before differentiation; repeated original nodes are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets OverlapPaper
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem futureLastDerivative_parameter_smooth (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (K : FiniteStateField (QuantitativePaper.Configuration n))
    (r : Paper.Overlap) :
    ContDiff ℝ ∞ (fun P => cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P) K r) := by
  let p := cavityFiniteFutureDepth s J r
  let F := fun H => (cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n => 0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p K H)^2
  have hmean := boundedJets_cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) p K
  have hF : BoundedJets F := by
    simpa only [F, pow_two] using hmean.mul hmean
  have hc := contDiff_cavityRowSecondSpatial_futureEnergy (fun _ : QuantitativePaper.Configuration n => 0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s))
    (cavityFiniteEnergyInput D s) p (J-p) F hF
  have hfield : ContDiff ℝ ∞ (fun H => cavityFiniteFutureSquare D s J H K r) := by
    simpa only [cavityFiniteFutureSquare, finiteStateCascadePairMoment, F, p,
      cavityFiniteEnergyFeatureMean, pow_two] using hc
  exact hfield.comp (anisotropicEnergyMap D).contDiff

private theorem futureLastDerivative_rest_last (n : ℕ) :
    cavityRestParameterProjection n (anisotropicCoordinateDirection (n+1) (Fin.last n)) = 0 := by
  ext i
  cases i <;> simp [cavityRestParameterProjection, anisotropicCoordinateDirection,
    anisotropicFieldInjection, EuclideanSpace.single_apply]

private theorem futureLastDerivative_last_last (n : ℕ) :
    anisotropicCoordinateDirection (n+1) (Fin.last n) (Sum.inr (Fin.last n)) = 1 := by
  simp [anisotropicCoordinateDirection, anisotropicFieldInjection, EuclideanSpace.single_apply]

private theorem futureLastDerivative_rest_old (n : ℕ) (l : Fin n) :
    cavityRestParameterProjection n (anisotropicCoordinateDirection (n+1) l.castSucc) =
      anisotropicFieldInjection n (EuclideanSpace.single l 1) := by
  ext i
  cases i <;> simp [cavityRestParameterProjection, anisotropicCoordinateDirection,
    anisotropicFieldInjection, EuclideanSpace.single_apply]

private theorem futureLastDerivative_old_last (n : ℕ) (l : Fin n) :
    anisotropicCoordinateDirection (n+1) l.castSucc (Sum.inr (Fin.last n)) = 0 := by
  have hn : Fin.last n ≠ l.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  simp [anisotropicCoordinateDirection, anisotropicFieldInjection, EuclideanSpace.single_apply, hn]

theorem cavityFiniteIncidentFutureSquare_average_last_derivative
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (J p : ℕ) (hJ : J ≤ k+2) (hp : p ≤ J)
    (P : AnisotropicParameter (n+1)) (g : AnisotropicDisorder n)
    (x : Field n) (y : ℝ)
    (hrest : cavityRestParameterProjection n P =
      anisotropicDisorderInjection n g + anisotropicFieldInjection n x)
    (hlast : P (Sum.inr (Fin.last n)) = y)
    (q r : Paper.Overlap) (hq : (q : ℝ) = s.q (k+2-J))
    (hr : (r : ℝ) = s.q (k+2-p)) (hqr : (q : ℝ) ≤ r) :
    let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
    fderiv ℝ (fun Q => (∑ i : Fin n,
      cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n : ℝ)) P
      (anisotropicCoordinateDirection (n+1) (Fin.last n)) =
      anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g q x r *
      scalarFutureSquareDerivative (followupCavityScalarBeta n β ρ)
        (Paper.parisiSchemeMeasure s) q r hqr y := by
  dsimp only
  let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
  let F := fun Q => (∑ i : Fin n,
    cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n : ℝ)
  let v := anisotropicCoordinateDirection (n+1) (Fin.last n)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.div_const
    exact ContDiff.sum fun i _ => futureLastDerivative_parameter_smooth D s J _ r
  have hdF := ((hF.differentiable (by simp) P).hasFDerivAt).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).smul_const v)) (by simp)
  simp only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] at hdF
  have he : (fun z : ℝ => F (P+z • v)) = fun z =>
      anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g q x r *
      scalarFutureSquare (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s)
        q r hqr (y+z) := by
    funext z
    have hrest' : cavityRestParameterProjection n (P+z • v) =
        anisotropicDisorderInjection n g + anisotropicFieldInjection n x := by
      simp only [map_add, map_smul, v, futureLastDerivative_rest_last, smul_zero, add_zero, hrest]
    have hlast' : (P+z • v) (Sum.inr (Fin.last n)) = y+z := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v,
        futureLastDerivative_last_last, mul_one, hlast]
    exact cavityFiniteIncidentFutureSquare_average_eq_native_product s n β ρ hβ hρ
      J p hJ hp (P+z • v) g x (y+z) hrest' hlast' q r hq hr hqr
  change HasDerivAt (fun z : ℝ => F (P+z • v)) (fderiv ℝ F P v) 0 at hdF
  rw [he] at hdF
  have hd := (hasDerivAt_scalarFutureSquare (followupCavityScalarBeta n β ρ)
    (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' (Paper.parisiSchemeMeasure s)
    q r hqr y).comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add y) (by simp)
  have hdR := hd.const_mul (anisotropicRestartMeanSquare
    (followupCavityRestSpinModel n β ρ hβ hρ) (Paper.parisiSchemeMeasure s) g q x r)
  have hdR' : HasDerivAt (fun z =>
      anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g q x r *
      scalarFutureSquare (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s)
        q r hqr (y+z))
      (anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g q x r *
      scalarFutureSquareDerivative (followupCavityScalarBeta n β ρ)
        (Paper.parisiSchemeMeasure s) q r hqr y) 0 := by
    simpa only [Function.comp_def, id_eq, add_zero, mul_one] using hdR
  exact hdF.unique hdR'

theorem cavityFiniteIncidentFutureSquare_average_old_derivative
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (J p : ℕ) (hJ : J ≤ k+2) (hp : p ≤ J)
    (P : AnisotropicParameter (n+1)) (g : AnisotropicDisorder n)
    (x : Field n) (y : ℝ)
    (hrest : cavityRestParameterProjection n P =
      anisotropicDisorderInjection n g + anisotropicFieldInjection n x)
    (hlast : P (Sum.inr (Fin.last n)) = y)
    (q r : Paper.Overlap) (hq : (q : ℝ) = s.q (k+2-J))
    (hr : (r : ℝ) = s.q (k+2-p)) (hqr : (q : ℝ) ≤ r) (l : Fin n) :
    let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
    fderiv ℝ (fun Q => (∑ i : Fin n,
      cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n : ℝ)) P
      (anisotropicCoordinateDirection (n+1) l.castSucc) =
      scalarFutureSquare (followupCavityScalarBeta n β ρ)
        (Paper.parisiSchemeMeasure s) q r hqr y *
      fderiv ℝ (fun z => anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) g q z r) x (EuclideanSpace.single l 1) := by
  dsimp only
  let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
  let F := fun Q => (∑ i : Fin n,
    cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) r)/(n : ℝ)
  let v := anisotropicCoordinateDirection (n+1) l.castSucc
  let e := EuclideanSpace.single l (1 : ℝ)
  let A := fun z => anisotropicRestartMeanSquare (followupCavityRestSpinModel n β ρ hβ hρ)
    (Paper.parisiSchemeMeasure s) g q z r
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.div_const
    exact ContDiff.sum fun i _ => futureLastDerivative_parameter_smooth D s J _ r
  have hdF := ((hF.differentiable (by simp) P).hasFDerivAt).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).smul_const v)) (by simp)
  simp only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] at hdF
  have he : (fun z : ℝ => F (P+z • v)) = fun z => A (x+z • e) *
      scalarFutureSquare (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s)
        q r hqr y := by
    funext z
    have hrest' : cavityRestParameterProjection n (P+z • v) =
        anisotropicDisorderInjection n g + anisotropicFieldInjection n (x+z • e) := by
      simp only [map_add, map_smul, v, e, futureLastDerivative_rest_old, hrest]
      module
    have hlast' : (P+z • v) (Sum.inr (Fin.last n)) = y := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v,
        futureLastDerivative_old_last, mul_zero, add_zero, hlast]
    exact cavityFiniteIncidentFutureSquare_average_eq_native_product s n β ρ hβ hρ
      J p hJ hp (P+z • v) g (x+z • e) y hrest' hlast' q r hq hr hqr
  change HasDerivAt (fun z : ℝ => F (P+z • v)) (fderiv ℝ F P v) 0 at hdF
  rw [he] at hdF
  have hA : ContDiff ℝ 1 A := contDiff_anisotropicRestartMeanSquare_field _ _ g q r hqr
  have hdA := ((hA.differentiable (by norm_num) x).hasFDerivAt).comp_hasDerivAt_of_eq 0
    ((hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const e)) (by simp)
  simp only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] at hdA
  have hdR := hdA.mul_const (scalarFutureSquare (followupCavityScalarBeta n β ρ)
    (Paper.parisiSchemeMeasure s) q r hqr y)
  exact (hdF.unique hdR).trans (mul_comm _ _)

end QuantitativeFollowup
