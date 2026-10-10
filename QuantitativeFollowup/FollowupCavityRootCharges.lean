module
public import QuantitativeFollowup.FollowupCavityRecordedDensity
public import QuantitativeFollowup.AnisotropicFiniteCovariance
public import QuantitativeFollowup.ParisiFreeGrid
public import FourPapersCommon.FiniteCascadeZeroRoot

@[expose] public section

/-! The dummy zero-noise root of the actual finite cavity scheme is removed
before assigning vertex charges. The genuine spin law and its initial
Gaussian normalizer are retained. For floor-preserving grid schemes every
vertex charge is nonnegative and their total is exactly leaves minus s. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open FiniteTerminalGenealogy QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem anisotropicSchemeMass_antitone (s : RSBScheme k) :
    Antitone (anisotropicSchemeMass s) := by
  intro i j hij
  exact s.m_mono' (k+1-i) (Nat.sub_le _ _) (k+1-j) (by omega)

def anisotropicTrimmedRecordedTreeLaw (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) :=
  finiteCascadeTreeGaussianJointLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a (trimRoot T)
      (anisotropicRootEnergyMap D) 0

instance anisotropicTrimmedRecordedTreeLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) :
    IsProbabilityMeasure (anisotropicTrimmedRecordedTreeLaw D s a T) :=
  finiteCascadeTreeGaussianJointLaw_probability _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

theorem anisotropicTrimmedRecordedTreeLaw_spin_marginal (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) :
    (anisotropicTrimmedRecordedTreeLaw D s a T).map
      (fun z : FiniteStateField (Configuration n) ×
        Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T) =>
          (trimmedSpinEquiv (S:=Configuration n) T).toEquiv.toFun (spins (trimRoot T) z.2)) =
      anisotropicFiniteTreeLaw D s a (asGenealogy T) := by
  have hz : (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s (k+1))=0 := by
    rw [anisotropicSchemeInput_root_zero D s hq]
    ext x σ
    simp
  exact (finiteCascadeTreeGaussianJointLaw_trimmed_spin_marginal _ _
    (anisotropicSchemeMass_nonneg s) _ a T hz _ _).trans
      (anisotropicFiniteRecordedTreeLaw_spin_marginal D s a T)

theorem anisotropicTrimmedRecordedTreeLaw_density (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) :
    anisotropicTrimmedRecordedTreeLaw D s a T =
      (finiteCascadeTreeGaussianReferenceLaw
        (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) (trimRoot T)
        (anisotropicRootEnergyMap D) 0).withDensity (fun z=>ENNReal.ofReal
          (Real.exp (finiteCascadeTreeTerminalEnergy (fun _ : Configuration n=>0) (trimRoot T) z.1 z.2-
            ((finiteCascadeTreeCharges (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
              (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a
              (trimRoot T) z.1 z.2).map (fun c=>c.1*c.2)).sum) /
            finiteCascadeTreeGaussianNormalizer (fun _ : Configuration n=>0)
              (anisotropicSchemeMass s)
              (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j))
              a (k+2) (anisotropicRootEnergyMap D) 0)) := by
  have hz : (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s (k+1))=0 := by
    rw [anisotropicSchemeInput_root_zero D s hq]
    ext x σ
    simp
  have hn : finiteCascadeTreeGaussianNormalizer (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s)
      (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j))
      a (k+2) (anisotropicRootEnergyMap D) 0 =
    finiteCascadeTreeGaussianNormalizer (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s)
      (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j))
      a (k+1) (anisotropicRootEnergyMap D) 0 := by
    unfold finiteCascadeTreeGaussianNormalizer
    rw [show k+2=(k+1)+1 by omega,
      finiteStateGaussianTerminalCascade_zero_root_step _ _ _ (k+1) hz]
  rw [hn]
  exact finiteCascadeTreeGaussianJointLaw_density _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

theorem anisotropicTrimmedTreeCharges_nonneg (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (T : FiniteTerminalGenealogy (k+2))
    (H : FiniteStateField (Configuration n))
    (z : Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T)) :
    ∀c∈finiteCascadeTreeCharges (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a (trimRoot T) H z,
      0≤c.1 := by
  apply finiteCascadeTreeCharges_nonneg_of_root_le _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_antitone s) (anisotropicSchemeMass_le_one s 0)
  have hc := finiteCascadeTreeRootCoefficient_previous_ge (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (trimRoot T) (by omega)
  have hm : anisotropicSchemeMass s (k+2-1-1)=s.m 1 := by
    simp only [anisotropicSchemeMass]
    congr 1
    omega
  rw [hm] at hc
  exact ha.trans hc

theorem anisotropicTrimmedTreeCharges_sum (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (H : FiniteStateField (Configuration n))
    (z : Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T)) :
    ((finiteCascadeTreeCharges (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a
      (trimRoot T) H z).map Prod.fst).sum =
        (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-a := by
  rw [finiteCascadeTreeCharges_sum,leafCount_trimRoot]

theorem anisotropicGridTrimmedTreeCharges_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a) (N : ℕ)
    (T : FiniteTerminalGenealogy (N+3)) (H : FiniteStateField (Configuration n))
    (z : Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T)) :
    ∀c∈finiteCascadeTreeCharges (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (Paper.parisiGridRSBScheme μ N))
      (fun j=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (Paper.parisiGridRSBScheme μ N) j))
      a (trimRoot T) H z,0≤c.1 :=
  anisotropicTrimmedTreeCharges_nonneg D (Paper.parisiGridRSBScheme μ N) a
    (parisiGridRSBScheme_floor μ a hμ N) T H z

end QuantitativeFollowup
