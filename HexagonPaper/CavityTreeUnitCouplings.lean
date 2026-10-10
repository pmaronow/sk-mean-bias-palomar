module
public import QuantitativeFollowup.AnisotropicNodeTheta
public import QuantitativeFollowup.FollowupCavityRootNormalizerTransport

@[expose] public section

/-! The literal spin-pair parameter chart retains zero original Gaussian
couplings. Its actual arbitrary-profile potential is transported through
the genuine finite dyadic potential limits. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem cavityTree_native_tail_unitCouplings (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n):
    anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
      (anisotropicCouplingRescaling D P)=anisotropicMeasureTailPotential D μ q P := by
  have he (j : ℕ):
      anisotropicDyadicTailPotential (anisotropicUnitCouplings D) μ q j
        (anisotropicCouplingRescaling D P)=anisotropicDyadicTailPotential D μ q j P := by
    unfold anisotropicDyadicTailPotential
    rw [anisotropicTailRecursion_eq_clamped (anisotropicUnitCouplings D) _ q q.property le_rfl,
      anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
    exact anisotropicFinitePotential_unitCouplings D _ _ P
  have hu:=(tendstoUniformly_anisotropicDyadicTailPotential (anisotropicUnitCouplings D) μ).tendsto_at
    (q,anisotropicCouplingRescaling D P)
  have hd:=(tendstoUniformly_anisotropicDyadicTailPotential D μ).tendsto_at (q,P)
  simp_rw [he] at hu
  exact tendsto_nhds_unique hu hd

theorem cavityTree_pairParameter_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n):
    anisotropicPairParameterPotential D μ q P e 0=anisotropicMeasureTailPotential D μ q P := by
  simp only [anisotropicPairParameterPotential,zero_smul,add_zero]
  exact cavityTree_native_tail_unitCouplings D μ q P

end HexagonPaper
