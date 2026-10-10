module
public import QuantitativeFollowup.FollowupCavityBinaryNodeStieltjes
public import QuantitativeFollowup.AnisotropicFiniteCovariance
public import FourPapersCommon.FiniteStateGaussianLaw
public import FourPapersCommon.FiniteStateSameMassResponses

@[expose] public section

/-! Actual positive diagonal variance replacement with the coupling disorder
held fixed, and the independent rest/coordinate Gaussian directions used
in its finite covariance interpolation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

def anisotropicReplaceVariance (D : AnisotropicSpinModel n) (i : Fin n) (b : ℝ) :
    AnisotropicSpinModel n where
  variance l:=if l=i ∧ 0<b then b else D.variance l
  variance_pos l:=by split_ifs with h;exact h.2;exact D.variance_pos l
  coupling:=D.coupling

@[simp] theorem anisotropicReplaceVariance_coupling (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) : (anisotropicReplaceVariance D i b).coupling=D.coupling := rfl

@[simp] theorem anisotropicReplaceVariance_variance (D : AnisotropicSpinModel n)
    (i l : Fin n) (b : ℝ) (hb : 0<b) :
    (anisotropicReplaceVariance D i b).variance l=if l=i then b else D.variance l := by
  simp [anisotropicReplaceVariance,hb]

theorem anisotropicReplaceVariance_self (D : AnisotropicSpinModel n) (i : Fin n) :
    anisotropicReplaceVariance D i (D.variance i)=D := by
  have hv : (anisotropicReplaceVariance D i (D.variance i)).variance=D.variance := by
    funext l
    rw [anisotropicReplaceVariance_variance D i l _ (D.variance_pos i)]
    split_ifs with h
    · exact congrArg D.variance h.symm
    · rfl
  cases D
  dsimp only [anisotropicReplaceVariance] at hv ⊢
  congr 1

@[simp] theorem anisotropicReplaceVariance_energyMap (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) :
    anisotropicEnergyMap (anisotropicReplaceVariance D i b)=anisotropicEnergyMap D := by
  ext P σ
  rfl

def cavityCoordinateFeature (i : Fin n) : FiniteStateField (Configuration n) :=
  WithLp.toLp 2 (fun σ=>Paper.spinSign (σ i))

@[simp] theorem cavityCoordinateFeature_apply (i : Fin n) (σ : Configuration n) :
    cavityCoordinateFeature i σ=Paper.spinSign (σ i) := rfl

theorem cavityCoordinateFeature_binary (i : Fin n) (σ : Configuration n) :
    cavityCoordinateFeature i σ*cavityCoordinateFeature i σ=1 := by
  simp only [cavityCoordinateFeature_apply]
  cases σ i <;> norm_num [Paper.spinSign]

def cavityCoordinateEnergyMap (i : Fin n) :
    Field n→L[ℝ]FiniteStateField (Configuration n) :=
  (EuclideanSpace.proj i).smulRight (cavityCoordinateFeature i)

@[simp] theorem cavityCoordinateEnergyMap_apply (i : Fin n) (z : Field n)
    (σ : Configuration n) : cavityCoordinateEnergyMap i z σ=z i*Paper.spinSign (σ i) := rfl

def cavityRestNoiseMap (D : AnisotropicSpinModel n) (i : Fin n) : Field n→L[ℝ]Field n :=
  LinearMap.toContinuousLinearMap
    {toFun:=fun z=>WithLp.toLp 2 (fun l=>if l=i then 0 else Real.sqrt (D.variance l)*z l)
     map_add':=by intro x y;ext l;by_cases hl:l=i <;> simp [hl,mul_add]
     map_smul':=by intro c x;ext l;by_cases hl:l=i <;> simp [hl];ring}

@[simp] theorem cavityRestNoiseMap_apply (D : AnisotropicSpinModel n) (i l : Fin n)
    (z : Field n) : cavityRestNoiseMap D i z l=if l=i then 0 else Real.sqrt (D.variance l)*z l := rfl

def cavityRestEnergyInput (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (j : ℕ) : Field n→L[ℝ]FiniteStateField (Configuration n) :=
  Real.sqrt (s.q (k+2-j)-s.q (k+1-j)) •
    (anisotropicEnergyMap D).comp ((anisotropicFieldInjection n).comp (cavityRestNoiseMap D i))

def cavityCoordinateEnergyInput (s : RSBScheme k) (i : Fin n) (j : ℕ) (b : ℝ) :
    Field n→L[ℝ]FiniteStateField (Configuration n) :=
  Real.sqrt (b*(s.q (k+2-j)-s.q (k+1-j))) • cavityCoordinateEnergyMap i

@[simp] theorem cavityCoordinateEnergyMap_single (i l : Fin n) (σ : Configuration n) :
    cavityCoordinateEnergyMap i (EuclideanSpace.single l 1) σ=
      if l=i then Paper.spinSign (σ i) else 0 := by
  simp [cavityCoordinateEnergyMap_apply,EuclideanSpace.single_apply,eq_comm]

theorem cavityFiniteEnergyInput_single (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (l : Fin n) (σ : Configuration n) :
    cavityFiniteEnergyInput D s j (EuclideanSpace.single l 1) σ=
      Real.sqrt (s.q (k+2-j)-s.q (k+1-j))*Real.sqrt (D.variance l)*Paper.spinSign (σ l) := by
  change anisotropicEnergyMap D
    (Real.sqrt (s.q (k+2-j)-s.q (k+1-j)) •
      anisotropicFieldInjection n (anisotropicNoiseMap D (EuclideanSpace.single l 1))) σ=_
  rw [map_smul]
  simp only [PiLp.smul_apply,smul_eq_mul,anisotropicEnergyMap_field,fieldDot]
  rw [Finset.sum_eq_single l]
  · simp [EuclideanSpace.single_apply];ring
  · intro b _ hbl
    simp [EuclideanSpace.single_apply,hbl]
  · simp

theorem cavityRestEnergyInput_single (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (j : ℕ) (l : Fin n) (σ : Configuration n) :
    cavityRestEnergyInput D s i j (EuclideanSpace.single l 1) σ=
      if l=i then 0 else
        Real.sqrt (s.q (k+2-j)-s.q (k+1-j))*Real.sqrt (D.variance l)*Paper.spinSign (σ l) := by
  simp only [cavityRestEnergyInput,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    PiLp.smul_apply,smul_eq_mul,anisotropicEnergyMap_field,fieldDot]
  rw [Finset.sum_eq_single l]
  · by_cases hl:l=i <;> simp [cavityRestNoiseMap_apply,hl,EuclideanSpace.single_apply];ring
  · intro b _ hbl
    by_cases hb:b=i <;> simp [cavityRestNoiseMap_apply,hb,EuclideanSpace.single_apply,hbl]
  · simp

theorem cavityCellVariance_nonneg (s : RSBScheme k) (j : ℕ) :
    0 ≤ s.q (k+2-j)-s.q (k+1-j) :=
  sub_nonneg.mpr (s.q_mono' (k+2-j) (by omega) (k+1-j) (by omega))

theorem cavityFiniteEnergyInput_spectral (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityFiniteEnergyInput D s j) σ τ=
      (s.q (k+2-j)-s.q (k+1-j))*∑l : Fin n,D.variance l*Paper.spinSign (σ l)*Paper.spinSign (τ l) := by
  simp only [finiteStateSpectralCovariance,cavityFiniteEnergyInput_single,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  calc
    _=(Real.sqrt (s.q (k+2-j)-s.q (k+1-j)))^2*(Real.sqrt (D.variance l))^2*
      Paper.spinSign (σ l)*Paper.spinSign (τ l) := by ring
    _=_ := by rw [Real.sq_sqrt (cavityCellVariance_nonneg s j),Real.sq_sqrt (D.variance_pos l).le];ring

theorem cavityRestEnergyInput_spectral (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) (j : ℕ) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityRestEnergyInput D s i j) σ τ=
      (s.q (k+2-j)-s.q (k+1-j))*∑l : Fin n,
        if l=i then 0 else D.variance l*Paper.spinSign (σ l)*Paper.spinSign (τ l) := by
  simp only [finiteStateSpectralCovariance,cavityRestEnergyInput_single,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl:l=i
  · simp [hl]
  · simp only [hl,ite_false]
    calc
      _=(Real.sqrt (s.q (k+2-j)-s.q (k+1-j)))^2*(Real.sqrt (D.variance l))^2*
        Paper.spinSign (σ l)*Paper.spinSign (τ l) := by ring
      _=_ := by rw [Real.sq_sqrt (cavityCellVariance_nonneg s j),Real.sq_sqrt (D.variance_pos l).le];ring

theorem cavityCoordinateEnergyInput_spectral (s : RSBScheme k) (i : Fin n)
    (j : ℕ) (b : ℝ) (hb : 0≤b) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityCoordinateEnergyInput s i j b) σ τ=
      b*(s.q (k+2-j)-s.q (k+1-j))*Paper.spinSign (σ i)*Paper.spinSign (τ i) := by
  simp only [finiteStateSpectralCovariance,cavityCoordinateEnergyInput,ContinuousLinearMap.smul_apply,
    PiLp.smul_apply,smul_eq_mul,cavityCoordinateEnergyMap_single]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    calc
      _=(Real.sqrt (b*(s.q (k+2-j)-s.q (k+1-j))))^2*Paper.spinSign (σ i)*Paper.spinSign (τ i) := by ring
      _=_ := by rw [Real.sq_sqrt (mul_nonneg hb (cavityCellVariance_nonneg s j))]
  · intro l _ hli;simp [hli]
  · simp


theorem cavityReplaceVariance_spectral_split (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) (b : ℝ) (hb : 0<b)
    (σ τ : Configuration n) :
    finiteStateSpectralCovariance (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s j) σ τ=
      finiteStateSpectralCovariance (cavityRestEnergyInput D s i j) σ τ+
        finiteStateSpectralCovariance (cavityCoordinateEnergyInput s i j b) σ τ := by
  rw [cavityFiniteEnergyInput_spectral,cavityRestEnergyInput_spectral,
    cavityCoordinateEnergyInput_spectral s i j b hb.le]
  simp_rw [anisotropicReplaceVariance_variance D i _ b hb]
  have he : (∑l : Fin n,(if l=i then b else D.variance l)*Paper.spinSign (σ l)*Paper.spinSign (τ l))=
      (∑l : Fin n,if l=i then 0 else D.variance l*Paper.spinSign (σ l)*Paper.spinSign (τ l))+
        b*Paper.spinSign (σ i)*Paper.spinSign (τ i) := by
    have he' : ∀l : Fin n,(if l=i then b else D.variance l)*Paper.spinSign (σ l)*Paper.spinSign (τ l)=
        (if l=i then 0 else D.variance l*Paper.spinSign (σ l)*Paper.spinSign (τ l))+
          (if l=i then b*Paper.spinSign (σ i)*Paper.spinSign (τ i) else 0) := by
      intro l
      by_cases hl:l=i <;> simp [hl]
    simp_rw [he']
    rw [Finset.sum_add_distrib]
    simp
  rw [he]
  ring

end QuantitativeFollowup
