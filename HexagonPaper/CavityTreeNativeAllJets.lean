module
public import QuantitativeFollowup.AnisotropicMeasureSpatialAllJets
public import QuantitativeFollowup.AnisotropicCouplingCoordinates
public import QuantitativeFollowup.AnisotropicTailContinuity
public import FourPapersCommon.JointDerivativeContinuity

@[expose] public section

/-! Genuine all-order spatial and deterministic coupling jets of the
actual arbitrary-profile tail. Every jet is identified from the native
dyadic finite cascade, with bounds independent of profile depth. The
unit-coupling chart gives constants independent of the row, disorder,
and positive field variances. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal ContDiff
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem cavityTree_native_tail_smooth_and_jets (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap):
    ContDiff ℝ ∞ (anisotropicMeasureTailPotential D μ q) ∧
    ∀r,TendstoUniformly (fun j=>iteratedFDeriv ℝ r (anisotropicDyadicTailPotential D μ q j))
      (iteratedFDeriv ℝ r (anisotropicMeasureTailPotential D μ q)) atTop := by
  apply contDiff_uniformLimit_of_uniform_jet_bounds
    (anisotropicDyadicTailPotential D μ q) (anisotropicMeasureTailPotential D μ q)
    (contDiff_anisotropicDyadicTailPotential D μ q) (anisotropicSpatialJetBound D)
    (anisotropicSpatialJetBound_nonneg D)
  · intro r hr j P
    unfold anisotropicDyadicTailPotential
    rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
    exact norm_anisotropicFinitePotential_jet_le_uniform D _ _ r (by omega) P
  · exact (tendstoUniformly_anisotropicDyadicTailPotential D μ).comp (fun P=>(q,P))

theorem cavityTree_native_tail_positive_jet_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (r : ℕ) (hr : 1≤r)
    (P : AnisotropicParameter n):
    ‖iteratedFDeriv ℝ r (anisotropicMeasureTailPotential D μ q) P‖≤anisotropicSpatialJetBound D r := by
  apply le_of_tendsto (((cavityTree_native_tail_smooth_and_jets D μ q).2 r).tendsto_at P).norm
  apply Eventually.of_forall
  intro j
  unfold anisotropicDyadicTailPotential
  rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
  exact norm_anisotropicFinitePotential_jet_le_uniform D _ _ r hr P

theorem cavityTree_native_tail_jet_joint_continuous (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : ℕ):
    Continuous (fun z:Paper.Overlap×AnisotropicParameter n=>
      iteratedFDeriv ℝ r (anisotropicMeasureTailPotential D μ z.1) z.2) :=
  continuous_iteratedFDeriv_family_of_uniform_jet_bounds _
    (continuous_anisotropicMeasureTailPotential_joint D μ)
    (fun q=>(cavityTree_native_tail_smooth_and_jets D μ q).1)
    (anisotropicSpatialJetBound D) (anisotropicSpatialJetBound_nonneg D)
    (fun r hr q P=>cavityTree_native_tail_positive_jet_bound D μ q r (by omega) P) r

def cavityTreeUnitModel (n : ℕ):AnisotropicSpinModel n where
  variance:=fun _=>1
  variance_pos:=fun _=>by norm_num
  coupling:=fun _=>1

theorem cavityTree_unit_energyMap (D : AnisotropicSpinModel n):
    anisotropicEnergyMap (anisotropicUnitCouplings D)=anisotropicEnergyMap (cavityTreeUnitModel n):=rfl

def cavityTreeUniformParameterJetBound (n r : ℕ):ℝ:=anisotropicSpatialJetBound (cavityTreeUnitModel n) r

theorem cavityTree_native_unit_tail_positive_jet_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (r : ℕ) (hr : 1≤r)
    (P : AnisotropicParameter n):
    ‖iteratedFDeriv ℝ r (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) P‖≤
      cavityTreeUniformParameterJetBound n r := by
  have h:=cavityTree_native_tail_positive_jet_bound (anisotropicUnitCouplings D) μ q r hr P
  unfold anisotropicSpatialJetBound at h
  rw [cavityTree_unit_energyMap] at h
  exact h

def cavityTreeParameterDirection (n : ℕ) (i : AnisotropicCouplingIndex n⊕Fin n):
    AnisotropicParameter n:=EuclideanSpace.single i 1

theorem cavityTreeParameterDirection_norm (i : AnisotropicCouplingIndex n⊕Fin n):
    ‖cavityTreeParameterDirection n i‖=1 := by
  simp [cavityTreeParameterDirection,PiLp.norm_single]

theorem cavityTree_native_mixed_coordinate_jet_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (r : ℕ) (hr : 1≤r)
    (P : AnisotropicParameter n) (i : Fin r→AnisotropicCouplingIndex n⊕Fin n):
    ‖iteratedFDeriv ℝ r (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) P
        (fun k=>cavityTreeParameterDirection n (i k))‖≤cavityTreeUniformParameterJetBound n r := by
  have h:=(iteratedFDeriv ℝ r (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q) P).le_opNorm_mul_prod_of_le
    (b:=fun _:Fin r=>(1:ℝ))
      (fun k=>(cavityTreeParameterDirection_norm (i k)).le)
  simp only [Finset.prod_const_one,mul_one] at h
  exact h.trans (cavityTree_native_unit_tail_positive_jet_bound D μ q r hr P)

end HexagonPaper
