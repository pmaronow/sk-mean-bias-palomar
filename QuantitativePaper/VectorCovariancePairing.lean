module
public import QuantitativePaper.VectorConditionalVariance
public import QuantitativePaper.VectorMagnetizationSmooth
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-! Actual centered terminal-observable pairing and its finite spin covariance
matrix. All conditional means come from the constructed finite path law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem integrable_vectorEuclidean_bounded {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (f : VectorGaussianSpace n k × Configuration n → ℝ)
    (hf : Measurable f) (K : ℝ) (hK : ∀p,|f p|≤K) :
    Integrable f (vectorEuclideanJointLaw s β t a) := by
  let := vectorEuclideanJointLaw_probability (n := n) s β t a
  exact memLp_one_iff_integrable.mp (MemLp.of_bound hf.aestronglyMeasurable K
    (.of_forall fun p => by simpa only [Real.norm_eq_abs] using hK p))

theorem integral_vector_terminal_centered_pairing {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (d e : Configuration n → ℝ) (i : ℕ) (hi : i≤k+2)
    (g : VectorState n → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p, g (vectorEuclideanStateLinear s β t i p.1)*
        (d p.2-vectorBackwardMean s β t d i (vectorEuclideanStateLinear s β t i p.1))*
        (e p.2-vectorBackwardMean s β t e i (vectorEuclideanStateLinear s β t i p.1))
      ∂vectorEuclideanJointLaw s β t a)=
      ∫p,g (vectorEuclideanStateLinear s β t i p.1)*
        (vectorBackwardMean s β t (fun σ => d σ*e σ) i (vectorEuclideanStateLinear s β t i p.1)-
          vectorBackwardMean s β t d i (vectorEuclideanStateLinear s β t i p.1)*
            vectorBackwardMean s β t e i (vectorEuclideanStateLinear s β t i p.1))
        ∂vectorEuclideanJointLaw s β t a := by
  let P := vectorEuclideanJointLaw (n := n) s β t a
  let X := fun p : VectorGaussianSpace n k × Configuration n => vectorEuclideanStateLinear s β t i p.1
  let D := vectorBackwardMean s β t d i
  let E := vectorBackwardMean s β t e i
  let R := ∑σ : Configuration n,|d σ|
  let S := ∑σ : Configuration n,|e σ|
  have hd (σ : Configuration n) : |d σ|≤R :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)
  have he (σ : Configuration n) : |e σ|≤S :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (e τ)) (Finset.mem_univ σ)
  have hD (x : VectorState n) : |D x|≤R := abs_vectorBackwardMean_le s β t d R hd i x
  have hE (x : VectorState n) : |E x|≤S := abs_vectorBackwardMean_le s β t e S he i x
  have hmD : Measurable D := measurable_vectorBackwardMean s β t d i
  have hmE : Measurable E := measurable_vectorBackwardMean s β t e i
  have hmX : Measurable X := by dsimp [X];fun_prop
  have hD0 : 0≤R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE0 : 0≤S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmul {x y : ℝ} (hx : |x|≤R) (hy : |y|≤S) : |x*y|≤R*S := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hD0
  have htest (x : VectorState n) {y : ℝ} (hy : |y|≤R*S) : |g x*y|≤K*(R*S) := by
    rw [abs_mul]
    exact mul_le_mul (hK x) hy (abs_nonneg _) ((abs_nonneg _).trans (hK x))
  have hU : Integrable (fun p => g (X p)*(d p.2*e p.2)) P :=
    integrable_vectorEuclidean_bounded s β t a _
      ((hg.comp hmX).mul (((measurable_of_finite d).comp measurable_snd).mul
        ((measurable_of_finite e).comp measurable_snd))) (K*(R*S))
      (fun p => htest _ (hmul (hd _) (he _)))
  have hV : Integrable (fun p => g (X p)*(D (X p)*e p.2)) P :=
    integrable_vectorEuclidean_bounded s β t a _
      ((hg.comp hmX).mul ((hmD.comp hmX).mul ((measurable_of_finite e).comp measurable_snd)))
      (K*(R*S)) (fun p => htest _ (hmul (hD _) (he _)))
  have hW : Integrable (fun p => g (X p)*(d p.2*E (X p))) P :=
    integrable_vectorEuclidean_bounded s β t a _
      ((hg.comp hmX).mul (((measurable_of_finite d).comp measurable_snd).mul (hmE.comp hmX)))
      (K*(R*S)) (fun p => htest _ (hmul (hd _) (hE _)))
  have hZ : Integrable (fun p => g (X p)*(D (X p)*E (X p))) P :=
    integrable_vectorEuclidean_bounded s β t a _
      ((hg.comp hmX).mul ((hmD.comp hmX).mul (hmE.comp hmX)))
      (K*(R*S)) (fun p => htest _ (hmul (hD _) (hE _)))
  have hUV := integral_vectorEuclideanJointLaw_terminal_pairing s β t a
    (fun σ => d σ*e σ) i hi g hg K hK
  have hVZ := integral_vectorEuclideanJointLaw_terminal_pairing s β t a e i hi
    (fun x => g x*D x) (hg.mul hmD) (K*R) (fun x => by
      rw [abs_mul];exact mul_le_mul (hK x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hK x)))
  have hWZ := integral_vectorEuclideanJointLaw_terminal_pairing s β t a d i hi
    (fun x => g x*E x) (hg.mul hmE) (K*S) (fun x => by
      rw [abs_mul];exact mul_le_mul (hK x) (hE x) (abs_nonneg _) ((abs_nonneg _).trans (hK x)))
  have hVZ' : (∫p,g (X p)*(D (X p)*e p.2) ∂P)=∫p,g (X p)*(D (X p)*E (X p)) ∂P := by
    simpa only [X,D,E,mul_assoc] using hVZ
  have hWZ' : (∫p,g (X p)*(d p.2*E (X p)) ∂P)=∫p,g (X p)*(D (X p)*E (X p)) ∂P := by
    simpa only [X,D,E,mul_assoc,mul_comm,mul_left_comm] using hWZ
  have hT : Integrable (fun p => g (X p)*vectorBackwardMean s β t (fun σ => d σ*e σ) i (X p)) P := by
    have hR (σ : Configuration n) : |d σ*e σ|≤R*S := hmul (hd σ) (he σ)
    exact integrable_vectorEuclidean_bounded s β t a _
      ((hg.comp hmX).mul ((measurable_vectorBackwardMean s β t (fun σ => d σ*e σ) i).comp hmX))
      (K*(R*S)) (fun p => htest _ (abs_vectorBackwardMean_le s β t _ _ hR i _))
  change (∫p,g (X p)*(d p.2-D (X p))*(e p.2-E (X p)) ∂P)=_
  calc
    _ = ∫p,((g (X p)*(d p.2*e p.2)-g (X p)*(D (X p)*e p.2))-
        g (X p)*(d p.2*E (X p)))+g (X p)*(D (X p)*E (X p)) ∂P := by
      apply integral_congr_ae
      exact .of_forall fun _ => by ring
    _ = (∫p,g (X p)*(d p.2*e p.2) ∂P)-(∫p,g (X p)*(D (X p)*e p.2) ∂P)-
        (∫p,g (X p)*(d p.2*E (X p)) ∂P)+(∫p,g (X p)*(D (X p)*E (X p)) ∂P) := by
      have ha := integral_add ((hU.sub hV).sub hW) hZ
      have hb := integral_sub (hU.sub hV) hW
      have hc := integral_sub hU hV
      simp only [Pi.sub_apply] at ha hb hc
      rw [ha,hb,hc]
    _ = (∫p,g (X p)*vectorBackwardMean s β t (fun σ => d σ*e σ) i (X p) ∂P)-
        (∫p,g (X p)*(D (X p)*E (X p)) ∂P) := by
      change (∫p,g (X p)*(fun σ => d σ*e σ) p.2 ∂P)=_ at hUV
      rw [hUV,hVZ',hWZ']
      ring
    _ = _ := by
      rw [←integral_sub hT hZ]
      apply integral_congr_ae
      exact .of_forall fun _ => by dsimp only [X,D,E];ring

def vectorSpinCovariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) : Matrix (Fin n) (Fin n) ℝ := fun l j =>
  vectorBackwardMean s β t (fun σ => Paper.spinSign (σ l)*Paper.spinSign (σ j)) i x-
    vectorMagnetization s β t x.1 (k+2-i) x.2 l*
      vectorMagnetization s β t x.1 (k+2-i) x.2 j

theorem vectorSpinCovariance_symmetric {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) (l j : Fin n) :
    vectorSpinCovariance s β t i x l j=vectorSpinCovariance s β t i x j l := by
  unfold vectorSpinCovariance
  have he : (fun σ : Configuration n => Paper.spinSign (σ l)*Paper.spinSign (σ j))=
      fun σ => Paper.spinSign (σ j)*Paper.spinSign (σ l) := funext fun _ => mul_comm _ _
  rw [he,mul_comm (vectorMagnetization _ _ _ _ _ _ _)]

theorem measurable_vectorSpinCovariance_component {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (l j : Fin n) :
    Measurable (fun x : VectorState n => vectorSpinCovariance s β t i x l j) :=
  (measurable_vectorBackwardMean s β t _ i).sub
    ((boundedJets_vectorMagnetization_component s β t (k+2-i) l).1.continuous.measurable.mul
      (boundedJets_vectorMagnetization_component s β t (k+2-i) j).1.continuous.measurable)

theorem abs_vectorSpinCovariance_component_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (l j : Fin n) :
    |vectorSpinCovariance s β t i x l j| ≤ 2 := by
  have hmean : |vectorBackwardMean s β t
      (fun σ => Paper.spinSign (σ l)*Paper.spinSign (σ j)) i x|≤1 :=
    abs_vectorBackwardMean_le s β t _ 1 (fun σ => by simp [abs_mul]) i x
  have hm : |vectorMagnetization s β t x.1 (k+2-i) x.2 l*
      vectorMagnetization s β t x.1 (k+2-i) x.2 j|≤1 := by
    rw [abs_mul]
    exact (mul_le_mul (vectorMagnetization_component_bound s β t x.1 _ x.2 l)
      (vectorMagnetization_component_bound s β t x.1 _ x.2 j) (abs_nonneg _)
      (by norm_num)).trans (by norm_num)
  exact (abs_sub _ _).trans (by linarith)

theorem abs_vectorSpinResidual_le {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) (σ : Configuration n) (l : Fin n) :
    |Paper.spinSign (σ l)-vectorMagnetization s β t x.1 (k+2-i) x.2 l|≤2 := by
  have hb := vectorMagnetization_component_bound s β t x.1 (k+2-i) x.2 l
  exact (abs_sub _ _).trans (by rw [Paper.abs_spinSign];linarith)

theorem integral_vector_spin_covariance_pairing {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (i : ℕ) (hi : i≤k+2) (l j : Fin n)
    (g : VectorState n → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀x,|g x|≤K) :
    (∫p,g (vectorEuclideanStateLinear s β t i p.1)*
        (Paper.spinSign (p.2 l)-vectorEuclideanMagnetization s β t i p.1 l)*
        (Paper.spinSign (p.2 j)-vectorEuclideanMagnetization s β t i p.1 j)
      ∂vectorEuclideanJointLaw s β t a)=
      ∫p,g (vectorEuclideanStateLinear s β t i p.1)*
        vectorSpinCovariance s β t i (vectorEuclideanStateLinear s β t i p.1) l j
      ∂vectorEuclideanJointLaw s β t a := by
  simpa only [vectorBackwardMean_spin,vectorSpinCovariance,vectorEuclideanMagnetization] using
    integral_vector_terminal_centered_pairing s β t a
      (fun σ => Paper.spinSign (σ l)) (fun σ => Paper.spinSign (σ j)) i hi g hg K hK

end QuantitativePaper
