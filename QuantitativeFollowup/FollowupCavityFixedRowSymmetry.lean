module
public import QuantitativeFollowup.FollowupCavityFixedRowReflectionModel

@[expose] public section

/-! The last-spin square, rest square, and their product are invariant at
every retained node. Their actual normalized fixed-row expectations and
the actual outer normalizer are even; their Frechet derivatives at zero
therefore vanish. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityGaussianCascade_feature_statePermutation
    {S I : Type} [Fintype S] [Fintype I] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (e : S ≃ S) (V : S → ℝ) (hV : ∀s, V (e s) = V s)
    (a : ℕ → ℝ) (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (hL : ∀j z, cavityStatePermutation e (L j z) = L j (A j z))
    (j : ℕ) (H K : FiniteStateField S) :
    fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) (cavityStatePermutation e H)
        (cavityStatePermutation e K) =
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K := by
  let U := finiteStateGaussianTerminalCascade V a L j
  let P := cavityStatePermutation e
  have hU : Differentiable ℝ U :=
    (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).differentiable (by norm_num)
  have he : (fun Q => U (P Q)) = U := by
    funext Q
    exact cavityGaussianCascade_statePermutation e V hV a ha L A hL j Q
  have hc := (hU (P H)).hasFDerivAt.comp H
    P.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  simp only [Function.comp_def] at hc
  rw [he] at hc
  have hd := hc.unique (hU H).hasFDerivAt
  exact congrArg (fun T => T K) hd

theorem cavityLastEnergyReflection_feature_mean (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (j : ℕ) (H K : FiniteStateField (Configuration (n+1))) :
    cavityFiniteEnergyFeatureMean (fun _ => 0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) j (cavityLastEnergyReflection n K)
        (cavityLastEnergyReflection n H) =
      cavityFiniteEnergyFeatureMean (fun _ => 0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) j K H :=
  cavityGaussianCascade_feature_statePermutation (flipSpinEquiv (Fin.last n)) _
    (fun _ => rfl) _ (anisotropicSchemeMass_nonneg s) _
    (fun _ => siteFieldReflection (Fin.last n)) (cavityLastEnergyReflection_input D s) j H K

theorem cavityFixedRowLineField_permutation
    {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (e : S ≃ S) (j d : ℕ) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S (observationLinearTree j)) :
    cavityFixedRowLineField j d (cavityStatePermutation e H)
        (cavityPermuteRecords e (observationLinearTree j) z) =
      cavityStatePermutation e (cavityFixedRowLineField j d H z) := by
  induction j generalizing H with
  | zero => rfl
  | succ j ih =>
      change (if d = j+1 then cavityStatePermutation e H else
        cavityFixedRowLineField j d (cavityStatePermutation e z.1)
          (cavityPermuteRecords e (observationLinearTree j) z.2)) =
        cavityStatePermutation e (if d = j+1 then H else cavityFixedRowLineField j d z.1 z.2)
      split_ifs
      · rfl
      · exact ih z.1 z.2

theorem measurable_cavityFixedRowLineField
    {E S : Type} [MeasurableSpace E] [MeasurableSpace S] (j d : ℕ) :
    Measurable (fun z : E × Records E S (observationLinearTree j) =>
      cavityFixedRowLineField j d z.1 z.2) := by
  induction j with
  | zero => exact measurable_fst
  | succ j ih =>
      change Measurable (fun z : E × (E × Records E S (observationLinearTree j)) =>
        if d = j+1 then z.1 else cavityFixedRowLineField j d z.2.1 z.2.2)
      by_cases hd : d = j+1
      · simpa only [hd, ite_true] using
          (measurable_fst : Measurable (fun z : E × (E × Records E S (observationLinearTree j)) => z.1))
      · simpa only [hd, ite_false, Function.comp_def] using ih.comp measurable_snd

theorem cavityFixedRowLastSquare_reflection (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (z : FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1))
        (observationLinearTree (k+2))) :
    cavityFixedRowLastSquare D s d
      (Prod.map (cavityLastEnergyReflection n)
        (cavityPermuteRecords (flipSpinEquiv (Fin.last n)) (observationLinearTree (k+2))) z) =
      cavityFixedRowLastSquare D s d z := by
  let K : FiniteStateField (Configuration (n+1)) :=
    WithLp.toLp 2 (fun sigma => Paper.spinSign (sigma (Fin.last n)))
  have hK : cavityLastEnergyReflection n K = -K := by
    ext sigma
    change Paper.spinSign (flipSpin (Fin.last n) sigma (Fin.last n)) = -Paper.spinSign (sigma (Fin.last n))
    simp [spinSign_flipSpin, siteSign]
  have hm := cavityLastEnergyReflection_feature_mean D s d
    (cavityFixedRowLineField (k+2) d z.1 z.2) K
  rw [hK] at hm
  simp only [cavityFiniteEnergyFeatureMean, map_neg] at hm
  change -cavityFiniteEnergyFeatureMean _ _ _ d K
      (cavityLastEnergyReflection n (cavityFixedRowLineField (k+2) d z.1 z.2)) =
    cavityFiniteEnergyFeatureMean _ _ _ d K (cavityFixedRowLineField (k+2) d z.1 z.2) at hm
  simp only [cavityFixedRowLastSquare, Prod.map_fst, Prod.map_snd]
  dsimp only [cavityLastEnergyReflection]
  rw [cavityFixedRowLineField_permutation]
  change (cavityFiniteEnergyFeatureMean _ _ _ d K
      (cavityLastEnergyReflection n (cavityFixedRowLineField (k+2) d z.1 z.2)))^2 =
    (cavityFiniteEnergyFeatureMean _ _ _ d K (cavityFixedRowLineField (k+2) d z.1 z.2))^2
  exact (congrArg (fun t : ℝ => t^2) (neg_eq_iff_eq_neg.mp hm)).trans (by ring)

theorem cavityFixedRowRestSquare_reflection (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (z : FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1))
        (observationLinearTree (k+2))) :
    cavityFixedRowRestSquare D s d
      (Prod.map (cavityLastEnergyReflection n)
        (cavityPermuteRecords (flipSpinEquiv (Fin.last n)) (observationLinearTree (k+2))) z) =
      cavityFixedRowRestSquare D s d z := by
  simp only [cavityFixedRowRestSquare, cavityFiniteEnergyRestOverlap, Prod.map_fst, Prod.map_snd]
  dsimp only [cavityLastEnergyReflection]
  rw [cavityFixedRowLineField_permutation]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let K : FiniteStateField (Configuration (n+1)) :=
    WithLp.toLp 2 (fun sigma => Paper.spinSign (sigma i.castSucc))
  have hK : cavityLastEnergyReflection n K = K := by
    ext sigma
    exact congrArg Paper.spinSign (flipSpin_away (Fin.last n) i.castSucc sigma (Fin.castSucc_ne_last i))
  have hm := cavityLastEnergyReflection_feature_mean D s d
    (cavityFixedRowLineField (k+2) d z.1 z.2) K
  rw [hK] at hm
  exact congrArg (fun x : ℝ => x^2) hm

theorem cavityFixedRow_integral_reflection (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (theta : QuantitativePaper.Field n)
    (F : FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1))
        (observationLinearTree (k+2)) → ℝ) (hF : Measurable F)
    (hFP : ∀z, F (Prod.map (cavityLastEnergyReflection n)
      (cavityPermuteRecords (flipSpinEquiv (Fin.last n)) (observationLinearTree (k+2))) z) = F z) :
    (∫z, F z ∂cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a (-theta)) =
      ∫z, F z ∂cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a theta := by
  rw [←cavityFixedRowLaw_reflection beta rho hbeta hrho s a theta,
    integral_map ((cavityLastEnergyReflection n).continuous.measurable.prodMap
      (measurable_cavityPermuteRecords _ _)).aemeasurable hF.aestronglyMeasurable]
  simp only [hFP]

theorem measurable_cavityFixedRowLastSquare (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) : Measurable (cavityFixedRowLastSquare D s d) :=
  ((boundedJets_cavityFiniteEnergyFeatureMean _ _ (anisotropicSchemeMass_nonneg s) _ d _).1.continuous.measurable.comp
    (measurable_cavityFixedRowLineField (k+2) d)).pow_const 2

theorem measurable_cavityFixedRowRestSquare (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) : Measurable (cavityFixedRowRestSquare D s d) :=
  (boundedJets_cavityFiniteEnergyRestOverlap _ _ (anisotropicSchemeMass_nonneg s) _ d _).1.continuous.measurable.comp
    (measurable_cavityFixedRowLineField (k+2) d)

theorem cavityFixedRowLastSquare_integral_reflection (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (theta : QuantitativePaper.Field n) :
    (∫z, cavityFixedRowLastSquare (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s d z ∂cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a (-theta)) =
      ∫z, cavityFixedRowLastSquare (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s d z ∂cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a theta :=
  cavityFixedRow_integral_reflection beta rho hbeta hrho s a theta _
    (measurable_cavityFixedRowLastSquare _ s d) (cavityFixedRowLastSquare_reflection _ s d)

theorem cavityFixedRowRestSquare_integral_reflection (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (theta : QuantitativePaper.Field n) :
    (∫z, cavityFixedRowRestSquare (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s d z ∂cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a (-theta)) =
      ∫z, cavityFixedRowRestSquare (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s d z ∂cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a theta :=
  cavityFixedRow_integral_reflection beta rho hbeta hrho s a theta _
    (measurable_cavityFixedRowRestSquare _ s d) (cavityFixedRowRestSquare_reflection _ s d)

theorem cavityFixedRowProduct_integral_reflection (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (theta : QuantitativePaper.Field n) :
    let D := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    (∫z, cavityFixedRowLastSquare D s d z * cavityFixedRowRestSquare D s d z
      ∂cavityFixedRowLaw D s a (-theta)) =
      ∫z, cavityFixedRowLastSquare D s d z * cavityFixedRowRestSquare D s d z
        ∂cavityFixedRowLaw D s a theta := by
  dsimp only
  apply cavityFixedRow_integral_reflection beta rho hbeta hrho s a theta
  · exact (measurable_cavityFixedRowLastSquare _ s d).mul (measurable_cavityFixedRowRestSquare _ s d)
  · intro z
    rw [cavityFixedRowLastSquare_reflection, cavityFixedRowRestSquare_reflection]

theorem fderiv_even_at_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (heven : ∀x, f (-x) = f x) : fderiv ℝ f 0 = 0 := by
  by_cases hf : DifferentiableAt ℝ f 0
  · have he : (fun x => f (-x)) = f := funext heven
    have hn : HasFDerivAt f (fderiv ℝ f 0) (- (0 : E)) := by simpa using hf.hasFDerivAt
    have hc := hn.comp 0 (hasFDerivAt_id (0 : E)).neg
    simp only [Function.comp_def] at hc
    rw [he] at hc
    have hd := hc.unique hf.hasFDerivAt
    ext w
    have hw := congrArg (fun T => T w) hd
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg] at hw
    change -fderiv ℝ f 0 w = fderiv ℝ f 0 w at hw
    change fderiv ℝ f 0 w = 0
    linarith
  · exact fderiv_zero_of_not_differentiableAt hf

theorem fderiv_cavityFixedRowNormalizer_zero (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) :
    fderiv ℝ (cavityFixedRowNormalizer (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a) 0 = 0 :=
  fderiv_even_at_zero _ (cavityFixedRowNormalizer_reflection beta rho hbeta hrho s a)

theorem fderiv_cavityFixedRowLastSquare_integral_zero (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) :
    let D := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    fderiv ℝ (fun theta : QuantitativePaper.Field n => ∫z, cavityFixedRowLastSquare D s d z
      ∂cavityFixedRowLaw D s a theta) 0 = 0 :=
  fderiv_even_at_zero _ (cavityFixedRowLastSquare_integral_reflection beta rho hbeta hrho s a d)

theorem fderiv_cavityFixedRowRestSquare_integral_zero (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) :
    let D := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    fderiv ℝ (fun theta : QuantitativePaper.Field n => ∫z, cavityFixedRowRestSquare D s d z
      ∂cavityFixedRowLaw D s a theta) 0 = 0 :=
  fderiv_even_at_zero _ (cavityFixedRowRestSquare_integral_reflection beta rho hbeta hrho s a d)

theorem fderiv_cavityFixedRowProduct_integral_zero (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) :
    let D := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
    fderiv ℝ (fun theta : QuantitativePaper.Field n => ∫z, cavityFixedRowLastSquare D s d z *
      cavityFixedRowRestSquare D s d z ∂cavityFixedRowLaw D s a theta) 0 = 0 :=
  fderiv_even_at_zero _ (cavityFixedRowProduct_integral_reflection beta rho hbeta hrho s a d)

end QuantitativeFollowup
