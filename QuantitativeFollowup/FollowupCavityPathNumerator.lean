module
public import QuantitativeFollowup.FollowupCavityPathVarianceSmooth
public import FourPapersCommon.FiniteCascadeReferenceEnergyLinear
public import FourPapersCommon.FiniteCascadeVertexCharges

@[expose] public section

/-! The literal unnormalized marked density on fixed independent Gaussian
coordinates, before the variance scaling. Its retained fields are actual
linear maps and its potentials are actual covariance cascades. -/
noncomputable section
open Set
open scoped ContDiff Topology BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

abbrev CavityPathGaussianSpace {j : ℕ} (T : FiniteTerminalGenealogy j) (n : ℕ) :=
  FiniteStateGaussianInput (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)

def cavityPathRootStateMap (D : AnisotropicSpinModel n) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    CavityPathGaussianSpace T n→L[ℝ]
      (FiniteStateField (Configuration n)×FiniteStateGaussianInput (GaussianCoordinateIndex (Fin n) T)) :=
  ((anisotropicRootEnergyMap D).comp finiteGaussianLeft).prod finiteGaussianRight

def cavityPathVertexField (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) :
    CavityPathGaussianSpace T n→L[ℝ]FiniteStateField (Configuration n) :=
  (finiteCascadeRecordVertexCLM (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T v).comp
    (cavityPathRootStateMap D T)

def cavityPathTerminalEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T) :
    CavityPathGaussianSpace T n→L[ℝ]ℝ :=
  (finiteCascadeReferenceTerminalEnergyCLM
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T σ).comp
      (cavityPathRootStateMap D T)

def cavityPathFixedRecord (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T)
    (z : CavityPathGaussianSpace T n) :=
  finiteCascadeTreeReferenceRootFlatRecord
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T (anisotropicRootEnergyMap D) 0 (z,σ)

theorem cavityPathVertexField_eq_fixed_record (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (σ : TerminalSpins (Configuration n) T) (z : CavityPathGaussianSpace T n) :
    v.field (cavityPathFixedRecord D s i T σ z).1 (cavityPathFixedRecord D s i T σ z).2 =
      cavityPathVertexField D s i T v z := by
  simpa only [cavityPathFixedRecord,finiteCascadeTreeReferenceRootFlatRecord,zero_add,
    cavityPathVertexField,ContinuousLinearMap.comp_apply,cavityPathRootStateMap,ContinuousLinearMap.prod_apply]
    using finiteCascadeReference_vertex_field_eq_clm
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T v
        (anisotropicRootEnergyMap D (finiteGaussianLeft z)) (finiteGaussianRight z) σ

theorem cavityPathTerminalEnergy_eq_fixed_record (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins (Configuration n) T) (z : CavityPathGaussianSpace T n) :
    finiteCascadeTreeTerminalEnergy (fun _ : Configuration n=>0) T
      (cavityPathFixedRecord D s i T σ z).1 (cavityPathFixedRecord D s i T σ z).2 =
        cavityPathTerminalEnergy D s i T σ z := by
  simpa only [cavityPathFixedRecord,finiteCascadeTreeReferenceRootFlatRecord,zero_add,
    cavityPathTerminalEnergy,ContinuousLinearMap.comp_apply,cavityPathRootStateMap,ContinuousLinearMap.prod_apply]
    using finiteCascadeReference_terminalEnergy_eq_clm
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s) T σ
        (anisotropicRootEnergyMap D (finiteGaussianLeft z)) (finiteGaussianRight z)

def cavityPathVertexPotential (D : AnisotropicSpinModel n) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (w : ℝ×CavityPathGaussianSpace T n) : ℝ :=
  finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s) v.depth
      (cavityPathVertexField D s i T v w.2)

theorem exponentialSmoothOn_cavityPathVertexPotential (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    (v : FiniteCascadeRecordVertex T) (l u : ℝ) (hl : 0<l) :
    ExponentialSmoothOn (cavityPathVertexPotential D s i T v)
      ((Ioo l u)×ˢ(univ : Set (CavityPathGaussianSpace T n))) := by
  have hv : v.depth≤k+2:=v.depth_le.trans hj
  let Z := (ContinuousLinearMap.fst ℝ ℝ (CavityPathGaussianSpace T n)).prod
    ((cavityPathVertexField D s i T v).comp (ContinuousLinearMap.snd ℝ ℝ (CavityPathGaussianSpace T n)))
  exact (exponentialSmoothOn_cavityFinitePotential_variance D s i v.depth hv l u hl).precompCLM Z
    (fun w hw=>⟨hw.1,mem_univ _⟩)

theorem cavityPathVertexPotential_linear_bound (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    (v : FiniteCascadeRecordVertex T) (l u : ℝ) (hl : 0<l) :
    ∃B L : ℝ,0≤B ∧ 0≤L ∧ ∀b∈Ioo l u,∀z : CavityPathGaussianSpace T n,
      |cavityPathVertexPotential D s i T v (b,z)|≤B+L*‖z‖ := by
  obtain ⟨B,L,hB,hL,hb⟩:=cavityFinitePotential_variance_linear_bound D s i v.depth
    (v.depth_le.trans hj) l u hl
  refine ⟨B,L*‖cavityPathVertexField D s i T v‖,hB,by positivity,?_⟩
  intro b hb' z
  apply (hb b hb' _).trans
  have hh:=mul_le_mul_of_nonneg_left ((cavityPathVertexField D s i T v).le_opNorm z) hL
  dsimp only [cavityPathVertexPotential]
  nlinarith only [hh]

def cavityPathChargePotential (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (w : ℝ×CavityPathGaussianSpace T n) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map
    (fun c=>c.1*cavityPathVertexPotential D s i T c.2 w)).sum

def cavityPathLogNumerator (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T)
    (w : ℝ×CavityPathGaussianSpace T n) : ℝ :=
  cavityPathTerminalEnergy D s i T σ w.2 - cavityPathChargePotential D s a i T w

theorem cavityPathLogNumerator_eq_actual (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins (Configuration n) T) (w : ℝ×CavityPathGaussianSpace T n) :
    cavityPathLogNumerator D s a i T σ w =
      a*finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s) j
          (cavityPathFixedRecord D s i T σ w.2).1 +
      finiteCascadeTreeLogDensity (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s) T
          (cavityPathFixedRecord D s i T σ w.2).1 (cavityPathFixedRecord D s i T σ w.2).2 := by
  rw [finiteCascadeTreeLogDensity_add_root_eq,cavityPathTerminalEnergy_eq_fixed_record]
  have hc:=finiteCascadeTreeFieldSum_eq_charge_sum (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s) a T
      (cavityPathFixedRecord D s i T σ w.2).1 (cavityPathFixedRecord D s i T σ w.2).2
  rw [finiteCascadeTreeFieldSum_eq_vertex_sum] at hc
  rw [←hc]
  unfold cavityPathLogNumerator cavityPathChargePotential
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  rw [cavityPathVertexField_eq_fixed_record]
  rfl

end QuantitativeFollowup
