module
public import QuantitativePaper.VectorMeasureSitePermutationGeometry
public import QuantitativePaper.VectorMeasureGradient

@[expose] public section

/-! Site covariance of the genuine finite recursions and their arbitrary-profile
limits. All future Gaussian fields are changed by their actual isometry. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
variable {n : ℕ}

theorem siteEdgeMap_product (π : Equiv.Perm (Fin n)) (e : Edge n) (f : Fin n → ℝ) :
    f (siteEdgeMap π e).1.1 * f (siteEdgeMap π e).1.2 =
      f (π e.1.1) * f (π e.1.2) := by
  unfold siteEdgeMap orderedSiteEdge
  split_ifs <;> simp [mul_comm]

theorem energy_site_permutation (π : Equiv.Perm (Fin n))
    (p : Couplings n × ℝ) (σ : Configuration n) :
    energy n (siteDisorderPermutation π p).1 (siteSpinPermutation π σ) =
      energy n p.1 σ := by
  unfold energy Paper.skHamiltonian
  simp only [zero_mul,add_zero,siteDisorderPermutation_apply,siteSpinPermutation_apply]
  congr 1
  calc
    _ = ∑e : Edge n,p.1 (siteEdgeMap π e)*Paper.spinSign (σ (siteEdgeMap π e).1.1)*
        Paper.spinSign (σ (siteEdgeMap π e).1.2) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [mul_assoc,mul_assoc,siteEdgeMap_product π e (fun i=>Paper.spinSign (σ i))]
    _ = _ := (siteEdgePermutation π).sum_comp
      (fun e : Edge n=>p.1 e*Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))

theorem fieldDot_site_permutation (π : Equiv.Perm (Fin n))
    (x : Field n) (σ : Configuration n) :
    fieldDot (siteFieldPermutation π x) (siteSpinPermutation π σ) = fieldDot x σ := by
  unfold fieldDot
  simp only [siteFieldPermutation_apply,siteSpinPermutation_apply]
  exact Equiv.sum_comp π (fun i : Fin n=>x i*Paper.spinSign (σ i))

theorem vectorTerminalExponent_site_permutation (π : Equiv.Perm (Fin n))
    (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) (σ : Configuration n) :
    vectorTerminalExponent n β t (siteDisorderPermutation π p)
      (siteFieldPermutation π x) (siteSpinPermutation π σ) =
      vectorTerminalExponent n β t p x σ := by
  unfold vectorTerminalExponent
  rw [energy_site_permutation,fieldDot_site_permutation]
  rfl

theorem vectorTerminalExponent_site_permutation_reindex (π : Equiv.Perm (Fin n))
    (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) :
    vectorTerminalExponent n β t (siteDisorderPermutation π p) (siteFieldPermutation π x) =
      (vectorTerminalExponent n β t p x) ∘ siteSpinPermutation π.symm := by
  funext σ
  have h := vectorTerminalExponent_site_permutation π β t p x (siteSpinPermutation π.symm σ)
  have hs : siteSpinPermutation π (siteSpinPermutation π.symm σ)=σ := by ext i;simp
  rw [hs] at h
  exact h

theorem integral_siteFieldPermutation (π : Equiv.Perm (Fin n)) (f : Field n → ℝ) :
    (∫z,f (siteFieldPermutation π z) ∂fieldGaussian n)=∫z,f z ∂fieldGaussian n := by
  have hp : MeasurePreserving (siteFieldPermutation π) (fieldGaussian n) (fieldGaussian n) :=
    ⟨(siteFieldPermutation π).continuous.measurable,by
      unfold fieldGaussian SYK.standardGaussianMeasureOnEuclidean
      rw [map_pi_eq_stdGaussian]
      exact stdGaussian_map (siteFieldPermutation π)⟩
  exact hp.integral_comp (siteFieldPermutation π).toHomeomorph.measurableEmbedding f

theorem fieldShift_site_permutation (π : Equiv.Perm (Fin n)) (c : ℝ) (x z : Field n) :
    fieldShift c (siteFieldPermutation π x) (siteFieldPermutation π z)=
      siteFieldPermutation π (fieldShift c x z) := by simp [fieldShift]

theorem vectorColeHopfStep_site_permutation (π : Equiv.Perm (Fin n)) (c m : ℝ)
    (f g : Field n → ℝ) (hfg : ∀x,f (siteFieldPermutation π x)=g x) (x : Field n) :
    vectorColeHopfStep c m f (siteFieldPermutation π x)=vectorColeHopfStep c m g x := by
  have hi (h : ℝ → ℝ) :
      (∫z,h (f (fieldShift c (siteFieldPermutation π x) z)) ∂fieldGaussian n)=
        ∫z,h (g (fieldShift c x z)) ∂fieldGaussian n := by
    rw [←integral_siteFieldPermutation π
      (fun z=>h (f (fieldShift c (siteFieldPermutation π x) z)))]
    simp_rw [fieldShift_site_permutation,hfg]
  unfold vectorColeHopfStep vectorStepPartition
  split_ifs
  · exact hi id
  · rw [hi (fun a=>Real.exp (m*a))]

theorem vectorRecursion_site_permutation {k : ℕ} (s : RSBScheme k)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    vectorRecursion s β t (siteDisorderPermutation π p) j (siteFieldPermutation π x)=
      vectorRecursion s β t p j x := by
  induction j generalizing x with
  | zero =>
    unfold vectorRecursion vectorTerminalPotential terminalPotential
    rw [vectorTerminalExponent_site_permutation_reindex,terminalPartition_reindex]
  | succ j ih =>
    simp only [vectorRecursion]
    exact vectorColeHopfStep_site_permutation π _ _ _ _ ih x

theorem vectorTailRecursion_site_permutation {k : ℕ} (s : RSBScheme k)
    (π : Equiv.Perm (Fin n)) (β t q : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    vectorTailRecursion s β t q (siteDisorderPermutation π p) j (siteFieldPermutation π x)=
      vectorTailRecursion s β t q p j x := by
  induction j generalizing x with
  | zero => exact vectorRecursion_site_permutation s π β t p 0 x
  | succ j ih =>
    simp only [vectorTailRecursion]
    exact vectorColeHopfStep_site_permutation π _ _ _ _ ih x

theorem vectorMeasurePotential_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (p : Couplings n × ℝ) (x : Field n) :
    vectorMeasurePotential μ β t (siteDisorderPermutation π p) (siteFieldPermutation π x)=
      vectorMeasurePotential μ β t p x := by
  apply tendsto_nhds_unique (tendsto_vectorDyadicPotential μ β t ht _ _)
  convert tendsto_vectorDyadicPotential μ β t ht p x using 1
  funext j
  exact vectorRecursion_site_permutation _ π β t p _ x

theorem vectorMeasureTailPotential_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (p : Couplings n × ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β t q (siteDisorderPermutation π p) (siteFieldPermutation π x)=
      vectorMeasureTailPotential μ β t q p x := by
  apply tendsto_nhds_unique (tendsto_vectorDyadicTailPotential μ β t q ht q.property _ _)
  convert tendsto_vectorDyadicTailPotential μ β t q ht q.property p x using 1
  funext j
  exact vectorTailRecursion_site_permutation _ π β t q p _ x

theorem vectorStepResponse_site_permutation (π : Equiv.Perm (Fin n)) (c m : ℝ)
    (f g v w : Field n → ℝ) (hfg : ∀x,f (siteFieldPermutation π x)=g x)
    (hvw : ∀x,v (siteFieldPermutation π x)=w x) (x : Field n) :
    vectorStepResponse c m f v (siteFieldPermutation π x)=vectorStepResponse c m g w x := by
  have hp : vectorStepPartition c m f (siteFieldPermutation π x)=vectorStepPartition c m g x := by
    unfold vectorStepPartition
    rw [←integral_siteFieldPermutation π
      (fun z=>Real.exp (m*f (fieldShift c (siteFieldPermutation π x) z)))]
    simp_rw [fieldShift_site_permutation,hfg]
  unfold vectorStepResponse vectorStepWeight
  rw [hp,←integral_siteFieldPermutation π
    (fun z=>Real.exp (m*f (fieldShift c (siteFieldPermutation π x) z))/
      vectorStepPartition c m g x*v (fieldShift c (siteFieldPermutation π x) z))]
  simp_rw [fieldShift_site_permutation,hfg,hvw]

theorem vectorMagnetization_site_permutation {k : ℕ} (s : RSBScheme k)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (p : Couplings n × ℝ)
    (j : ℕ) (x : Field n) (i : Fin n) :
    vectorMagnetization s β t (siteDisorderPermutation π p) j (siteFieldPermutation π x) i=
      vectorMagnetization s β t p j x (π i) := by
  have hm (j : ℕ) (x : Field n) :
      vectorConditionalMean s β t (siteDisorderPermutation π p) (fun _=>0)
        (fun σ=>Paper.spinSign (σ i)) j 0 (siteFieldPermutation π x)=
      vectorConditionalMean s β t p (fun _=>0)
        (fun σ=>Paper.spinSign (σ (π i))) j 0 x := by
    induction j generalizing x with
    | zero =>
      simp only [vectorConditionalMean,terminalTilt_zero]
      rw [vectorTerminalExponent_site_permutation_reindex]
      have hd : (fun σ : Configuration n=>Paper.spinSign (σ i))=
          (fun σ : Configuration n=>Paper.spinSign (σ (π i))) ∘ siteSpinPermutation π.symm := by
        funext σ;simp
      rw [hd]
      exact terminalMean_reindex _ _ _
    | succ j ih =>
      simp only [vectorConditionalMean,vectorPerturbedRecursion_zero]
      exact vectorStepResponse_site_permutation π _ _ _ _ _ _
        (vectorRecursion_site_permutation s π β t p j) ih x
  change vectorObservableResponse s β t (siteDisorderPermutation π p)
    (fun σ=>Paper.spinSign (σ i)) j 0 (siteFieldPermutation π x)=
      vectorObservableResponse s β t p (fun σ=>Paper.spinSign (σ (π i))) j 0 x
  simpa only [vectorConditionalMean_zero_eq_response] using hm j x

theorem vectorFiniteTailGradient_site_permutation {k : ℕ} (s : RSBScheme k)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (q : Paper.Overlap)
    (p : Couplings n × ℝ) (x : Field n) :
    vectorFiniteTailGradient s β t q (siteDisorderPermutation π p) (siteFieldPermutation π x)=
      siteFieldPermutation π (vectorFiniteTailGradient s β t q p x) := by
  ext i
  simp only [siteFieldPermutation_apply,vectorFiniteTailGradient_eq_magnetization]
  exact vectorMagnetization_site_permutation _ π β t p _ x i

theorem vectorMeasureGradient_site_permutation (μ : Paper.ParisiMeasure)
    (π : Equiv.Perm (Fin n)) (β t : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (p : Couplings n × ℝ) (x : Field n) :
    vectorMeasureGradient μ β t q (siteDisorderPermutation π p) (siteFieldPermutation π x)=
      siteFieldPermutation π (vectorMeasureGradient μ β t q p x) := by
  apply tendsto_nhds_unique (tendsto_vectorDyadicTailGradient μ β t ht q _ _)
  convert (siteFieldPermutation π).continuous.tendsto _ |>.comp
    (tendsto_vectorDyadicTailGradient μ β t ht q p x) using 1
  funext j
  exact vectorFiniteTailGradient_site_permutation _ π β t q p x

end QuantitativePaper
