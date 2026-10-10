module
public import QuantitativeFollowup.FollowupCavityInterpolationCoordinates
public import QuantitativeFollowup.FollowupCavityPathRecordedScore

@[expose] public section

/-! Exact root-coordinate scaling for the complete actual tree numerator.
Coupling scales act only on the independent disorder block. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityGaussianSelectedScale_coordinate {A : Type} [Fintype A] [DecidableEq A]
    (p : A→Bool) (u : ℝ) (z : EuclideanSpace ℝ A) (e : A) :
    gaussianSelectedScale p u z e=(if p e then Real.sqrt u else 1)*z e := by
  rw [gaussianSelectedScale_apply]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp

def cavityRootCouplingMask (p : AnisotropicCouplingIndex n→Bool)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    AnisotropicCouplingIndex n⊕GaussianCoordinateIndex (Fin n) T→Bool:=
  Sum.elim p (fun _=>false)

theorem finiteGaussianLeft_cavityRootScale (p : AnisotropicCouplingIndex n→Bool)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (u : ℝ) (z : CavityPathGaussianSpace T n) :
    finiteGaussianLeft (gaussianSelectedScale (cavityRootCouplingMask p T) u z)=
      gaussianSelectedScale p u (finiteGaussianLeft z) := by
  classical
  ext e
  change gaussianSelectedScale (cavityRootCouplingMask p T) u z (Sum.inl e)=
    gaussianSelectedScale p u (finiteGaussianLeft z) e
  rw [cavityGaussianSelectedScale_coordinate,cavityGaussianSelectedScale_coordinate]
  rfl

theorem finiteGaussianRight_cavityRootScale (p : AnisotropicCouplingIndex n→Bool)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (u : ℝ) (z : CavityPathGaussianSpace T n) :
    finiteGaussianRight (gaussianSelectedScale (cavityRootCouplingMask p T) u z)=
      finiteGaussianRight z := by
  classical
  ext e
  change gaussianSelectedScale (cavityRootCouplingMask p T) u z (Sum.inr e)=z (Sum.inr e)
  simp only [cavityGaussianSelectedScale_coordinate,cavityRootCouplingMask,Sum.elim_inr,
    Bool.false_eq_true,ite_false,one_mul]

theorem cavityFiniteEnergyInput_scaleRootCouplings_variance (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (i : Fin n) (b : ℝ) (s : RSBScheme k) (j : ℕ) :
    cavityFiniteEnergyInput (anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i b) s j=
      cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s j := by
  apply finiteStateCLM_eq_of_single
  intro l
  ext σ
  simp only [cavityFiniteEnergyInput_single,anisotropicReplaceVariance,anisotropicScaleRootCouplings]

theorem cavityPathRootStateMap_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    cavityPathRootStateMap (anisotropicScaleRootCouplings D p u) T=
      (cavityPathRootStateMap D T).comp (gaussianSelectedScale (cavityRootCouplingMask p T) u) := by
  ext z <;> simp only [cavityPathRootStateMap,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,anisotropicRootEnergyMap_scaleRootCouplings,
      finiteGaussianLeft_cavityRootScale,finiteGaussianRight_cavityRootScale]

theorem cavityPathVertexField_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) :
    cavityPathVertexField (anisotropicScaleRootCouplings D p u) s i T v=
      (cavityPathVertexField D s i T v).comp (gaussianSelectedScale (cavityRootCouplingMask p T) u) := by
  have hL : cavityFiniteEnergyInput (anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i 1) s=
      cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s:=by
    funext q
    exact cavityFiniteEnergyInput_scaleRootCouplings_variance D p u i 1 s q
  unfold cavityPathVertexField
  rw [hL,cavityPathRootStateMap_scaleRootCouplings]
  rfl

theorem cavityPathTerminalEnergy_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T) :
    cavityPathTerminalEnergy (anisotropicScaleRootCouplings D p u) s i T σ=
      (cavityPathTerminalEnergy D s i T σ).comp (gaussianSelectedScale (cavityRootCouplingMask p T) u) := by
  have hL : cavityFiniteEnergyInput (anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i 1) s=
      cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s:=by
    funext q
    exact cavityFiniteEnergyInput_scaleRootCouplings_variance D p u i 1 s q
  unfold cavityPathTerminalEnergy
  rw [hL,cavityPathRootStateMap_scaleRootCouplings]
  rfl

theorem cavityPathVertexPotential_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T)
    (w : ℝ×CavityPathGaussianSpace T n) :
    cavityPathVertexPotential (anisotropicScaleRootCouplings D p u) s i T v w=
      cavityPathVertexPotential D s i T v (w.1,gaussianSelectedScale (cavityRootCouplingMask p T) u w.2) := by
  have hL : cavityFiniteEnergyInput (anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i w.1) s=
      cavityFiniteEnergyInput (anisotropicReplaceVariance D i w.1) s:=by
    funext q
    exact cavityFiniteEnergyInput_scaleRootCouplings_variance D p u i w.1 s q
  unfold cavityPathVertexPotential
  rw [hL,cavityPathVertexField_scaleRootCouplings,ContinuousLinearMap.comp_apply]

theorem cavityPathLogNumerator_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T)
    (w : ℝ×CavityPathGaussianSpace T n) :
    cavityPathLogNumerator (anisotropicScaleRootCouplings D p u) s a i T σ w=
      cavityPathLogNumerator D s a i T σ (w.1,gaussianSelectedScale (cavityRootCouplingMask p T) u w.2) := by
  unfold cavityPathLogNumerator cavityPathChargePotential
  rw [cavityPathTerminalEnergy_scaleRootCouplings,ContinuousLinearMap.comp_apply]
  simp_rw [cavityPathVertexPotential_scaleRootCouplings]

theorem cavityPathNumerator_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins (Configuration n) T)
    (w : ℝ×CavityPathGaussianSpace T n) :
    cavityPathNumerator (anisotropicScaleRootCouplings D p u) s a i T σ w=
      cavityPathNumerator D s a i T σ (w.1,gaussianSelectedScale (cavityRootCouplingMask p T) u w.2) := by
  unfold cavityPathNumerator
  rw [cavityPathLogNumerator_scaleRootCouplings]

end QuantitativeFollowup
