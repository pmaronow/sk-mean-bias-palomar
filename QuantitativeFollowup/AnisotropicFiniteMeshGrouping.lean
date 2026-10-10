module
public import QuantitativeFollowup.AnisotropicFiniteMeshNodes

@[expose] public section

/-! Uniform Gaussian cells group exactly between the upward-rounded
original nodes. Repeated original nodes produce empty blocks; every active
block retains the original right-CDF mass. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem anisotropicFiniteMesh_cell_mass (s : RSBScheme k) (N p l : ℕ)
    (hp : p≤k+1) (hl : anisotropicFiniteMeshIndices s N p≤l)
    (hu : l<anisotropicFiniteMeshIndices s N (p+1)) :
    Paper.parisiCDF (Paper.parisiSchemeMeasure s) ((l:ℝ)/(N+1 : ℕ))=s.m p := by
  have hd : (0:ℝ)<(N+1 : ℕ) := by positivity
  have hlo : Nat.ceil ((N+1 : ℕ)*(s.q p))≤l := by
    simpa only [anisotropicFiniteMeshIndices,Paper.parisiGridIndex,
      anisotropicFiniteMeshNode_coe s p (by omega)] using hl
  have hup : l<Nat.ceil ((N+1 : ℕ)*(s.q (p+1))) := by
    simpa only [anisotropicFiniteMeshIndices,Paper.parisiGridIndex,
      anisotropicFiniteMeshNode_coe s (p+1) (by omega)] using hu
  apply Paper.parisiCDF_scheme_cell s hp
  constructor
  · apply (le_div_iff₀ hd).mpr
    simpa only [mul_comm] using Nat.ceil_le.mp hlo
  · apply (div_lt_iff₀ hd).mpr
    simpa only [mul_comm] using Nat.lt_ceil.mp hup

theorem anisotropicRoundedMeshTailRecursion_eq_uniform (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (N : ℕ) (q : ℝ) {j : ℕ} (hj : j≤k+2) :
    anisotropicMeshTailRecursion D s (anisotropicRoundedMeshNodes s N) q j=
      gaussianUniformTailCascade (N+1) q (anisotropicUnitInput D)
        (Paper.parisiCDF (Paper.parisiSchemeMeasure s)) (anisotropicGridTerminalPotential D)
        (N+1-anisotropicFiniteMeshIndices s N (k+2-j)) := by
  induction j with
  | zero =>
      simp only [Nat.sub_zero,anisotropicFiniteMeshIndices_top,Nat.sub_self,
        anisotropicMeshTailRecursion,gaussianUniformTailCascade]
  | succ j ih =>
      have hj' : j≤k+1 := by omega
      let p:=k+1-j
      let lo:=anisotropicFiniteMeshIndices s N p
      let hi:=anisotropicFiniteMeshIndices s N (p+1)
      have hlh : lo≤hi := anisotropicFiniteMeshIndices_mono s N p (p+1) (by dsimp [p];omega) (by omega)
      have hhi : hi≤N+1 := anisotropicFiniteMeshIndices_le s N (p+1)
      have hlo : lo≤N+1 := hlh.trans hhi
      have hblock : ∀i<hi-lo,
          Paper.parisiCDF (Paper.parisiSchemeMeasure s)
            ((N+1-1-((N+1-hi)+i) : ℕ)/(N+1 : ℕ))=s.m p := by
        intro i hi'
        apply anisotropicFiniteMesh_cell_mass s N p _ (by dsimp [p];omega)
        · dsimp only [lo,hi] at hlh hhi ⊢
          dsimp only [lo,hi] at hi'
          omega
        · dsimp only [lo,hi] at hlh hhi ⊢
          dsimp only [lo,hi] at hi'
          omega
      have he:=gaussianUniformTailCascade_constant_block (N+1) q (anisotropicUnitInput D)
        (Paper.parisiCDF (Paper.parisiSchemeMeasure s))
        (Paper.parisiCDF_nonneg _) (anisotropicGridTerminalPotential D) ‖anisotropicEnergyMap D‖₊
        (anisotropicGridTerminalPotential_lipschitz D) (N+1-hi) (hi-lo) (by omega)
        (s.m p) (s.m_nonneg (by dsimp [p];omega)) hblock
      have hsum : N+1-hi+(hi-lo)=N+1-lo := by omega
      have hfirst : N+1-(N+1-hi)=hi := by omega
      rw [hsum,hfirst,show N+1-(N+1-lo)=lo by omega] at he
      rw [anisotropicMeshTailRecursion,ih (by omega),
        anisotropicRoundedMeshNodes_eq_index,anisotropicRoundedMeshNodes_eq_index]
      have hu : k+2-j=p+1 := by dsimp [p];omega
      have hd : k+2-(j+1)=p := by dsimp [p];omega
      rw [hu,hd]
      exact he.symm

theorem anisotropicRoundedMeshTailRecursion_full_eq_uniform (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (N : ℕ) (q : ℝ) :
    anisotropicMeshTailRecursion D s (anisotropicRoundedMeshNodes s N) q (k+2)=
      gaussianUniformTailCascade (N+1) q (anisotropicUnitInput D)
        (Paper.parisiCDF (Paper.parisiSchemeMeasure s)) (anisotropicGridTerminalPotential D) (N+1) := by
  simpa only [Nat.sub_self,anisotropicFiniteMeshIndices_zero,Nat.sub_zero] using
    anisotropicRoundedMeshTailRecursion_eq_uniform D s N q (j:=k+2) le_rfl

end QuantitativeFollowup
