module
public import QuantitativeFollowup.AnisotropicFiniteCell
public import QuantitativePaper.VectorJointObservableRecursion

@[expose] public section

/-! Actual bounded-jet data for arbitrary smooth Fourier observables in the
diagonal-whitened anisotropic cell. Initial auxiliary disorder is unused;
physical anisotropic disorder remains fixed throughout each test. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 800000

def anisotropicWhiteJointInput (D : AnisotropicSpinModel n) : VectorParameter n→L[ℝ]AnisotropicParameter n :=
  (anisotropicUnitInput D).comp (ContinuousLinearMap.snd ℝ (Couplings n×ℝ) (Field n))

def anisotropicWhitenedFiniteJointPotential (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (g : AnisotropicDisorder n) (p : VectorParameter n) : ℝ :=
  anisotropicFinitePotential D s j (anisotropicDisorderInjection n g+anisotropicWhiteJointInput D p)

@[simp] theorem anisotropicWhitenedFiniteJointPotential_apply (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (g : AnisotropicDisorder n) (p : VectorParameter n) :
    anisotropicWhitenedFiniteJointPotential D s j g p=anisotropicWhitenedFinitePotential D s j g p.2 := rfl

theorem anisotropicWhitenedFiniteJointPotential_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (g : AnisotropicDisorder n) :
    LipschitzWith (‖anisotropicEnergyMap D‖₊*‖anisotropicWhiteJointInput D‖₊)
      (anisotropicWhitenedFiniteJointPotential D s j g) := by
  have hp : LipschitzWith ‖anisotropicWhiteJointInput D‖₊
      (fun p : VectorParameter n=>anisotropicDisorderInjection n g+anisotropicWhiteJointInput D p) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [dist_add_left] using (anisotropicWhiteJointInput D).lipschitzWith.dist_le_mul p q
  exact (anisotropicFinitePotential_lipschitz D s j).comp hp

theorem anisotropicWhitenedFiniteJointPotential_smooth_bounded_jets (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (N j : ℕ) (g : AnisotropicDisorder n) :
    ContDiff ℝ N (anisotropicWhitenedFiniteJointPotential D s j g) ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ r, 1 ≤ r → r ≤ N → ∀ p : VectorParameter n,
        ‖iteratedFDeriv ℝ r (anisotropicWhitenedFiniteJointPotential D s j g) p‖ ≤ C^r := by
  obtain ⟨hu,K,hK,hjets⟩ := anisotropicFinitePotential_smooth_bounded_jets D s N j
  let A := anisotropicWhiteJointInput D
  let c := anisotropicDisorderInjection n g
  let F := fun P : AnisotropicParameter n=>anisotropicFinitePotential D s j (c+P)
  have hf : ContDiff ℝ N F := hu.comp (contDiff_const.add contDiff_id)
  refine ⟨hu.comp (contDiff_const.add A.contDiff),K*(‖A‖+1),?_,?_⟩
  · nlinarith [norm_nonneg A]
  · intro r hr hrN p
    change ‖iteratedFDeriv ℝ r (F ∘ A) p‖ ≤ _
    rw [A.iteratedFDeriv_comp_right hf p (by exact_mod_cast hrN)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    have hF : ‖iteratedFDeriv ℝ r F (A p)‖ ≤ K^r := by
      rw [iteratedFDeriv_comp_add_left]
      exact hjets r hr hrN _
    calc
      _ ≤ K^r*‖A‖^r := mul_le_mul_of_nonneg_right hF (by positivity)
      _=(K*‖A‖)^r := (mul_pow _ _ _).symm
      _ ≤ (K*(‖A‖+1))^r := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hK)) _

theorem exists_anisotropicWhitenedFinite_jointResponseData (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (g : AnisotropicDisorder n)
    {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) :
    Nonempty (VectorJointResponseTestData (anisotropicWhitenedFiniteJointPotential D s j g) G) := by
  obtain ⟨hF,K,hK,hjets⟩ := anisotropicWhitenedFiniteJointPotential_smooth_bounded_jets D s 3 j g
  exact ⟨{
    potentialRegularity := hF
    observableRegularity := hG.regularity
    fieldLip := ‖anisotropicEnergyMap D‖₊*‖anisotropicWhiteJointInput D‖₊
    lipschitz := anisotropicWhitenedFiniteJointPotential_lipschitz D s j g
    potentialPower := ⟨K,zero_le_one.trans hK⟩
    potentialPower_ge_one := hK
    potentialJets := hjets
    observableBounds := hG.bounds
    observableBounds_nonneg := hG.bounds_nonneg
    observableJets := hG.jets }⟩

def anisotropicWhitenedFiniteJointResponseData (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (g : AnisotropicDisorder n) {G : VectorParameter n→ℝ} (hG : VectorBoundedC3 G) :
    VectorJointResponseTestData (anisotropicWhitenedFiniteJointPotential D s j g) G :=
  Classical.choice (exists_anisotropicWhitenedFinite_jointResponseData D s j g hG)

end QuantitativeFollowup
