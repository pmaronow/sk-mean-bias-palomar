module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFieldFeatures
public import QuantitativeFollowup.AnisotropicFiniteMeasureStateAgreement
public import QuantitativeFollowup.AnisotropicFiniteNodeResponse

@[expose] public section

/-! Retained field-square observables are the actual native process
squares at every original scheme node, including endpoints and repeats. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFixedRowSpinFeature_at_native_scheme_node (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (hd : d ≤ k+2) (i : Fin (n+1))
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1) => 0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d
      (WithLp.toLp 2 (fun σ : Configuration (n+1) => Paper.spinSign (σ i)))
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-d) (by omega)) sample)) =
    anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s)
      (anisotropicSchemeNode s (k+2-d) (by omega)) i sample := by
  rw [cavityFiniteEnergyFeatureMean_at_parameter,
    anisotropicProcessSpinResponse_scheme_eq_finite]
  unfold anisotropicFiniteProcessMagnetization
  rw [anisotropicFiniteTailMagnetization_node]
  have hidx : k+2-(k+2-d) = d := by omega
  rw [hidx, ←anisotropicProcessParameter_scheme_eq_finite]
  exact (anisotropicMagnetization_eq_spin_mean D s d _ i).symm

theorem cavityFixedRowLastFieldSquare_at_native_scheme_node (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (hd : d ≤ k+2)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    cavityFixedRowLastFieldSquare D s d
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-d) (by omega)) sample)) =
    (anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s)
      (anisotropicSchemeNode s (k+2-d) (by omega)) (Fin.last n) sample)^2 := by
  unfold cavityFixedRowLastFieldSquare
  rw [cavityFixedRowSpinFeature_at_native_scheme_node D s d hd]

theorem cavityFixedRow_old_selectedMeanSquare (M : QuantitativePaper.Field (n+1)) :
    anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n)) M =
      (n:ℝ)⁻¹ * ∑i : Fin n, (M i.castSucc)^2 := by
  have hs : (∑i ∈ Finset.univ.erase (Fin.last n), (M i)^2) =
      ∑i : Fin n, (M i.castSucc)^2 := by
    have he := Finset.sum_erase_add (s:=Finset.univ) (f:=fun i : Fin (n+1) => (M i)^2)
      (Finset.mem_univ (Fin.last n))
    have hu := Fin.sum_univ_castSucc (fun i : Fin (n+1) => (M i)^2)
    linarith
  rw [anisotropicSelectedMeanSquare, hs]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ (Fin.last n)), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]
  rw [div_eq_mul_inv, mul_comm]

theorem cavityFixedRowRestFieldSquare_at_native_scheme_node (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) (hd : d ≤ k+2)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    cavityFixedRowRestFieldSquare D s d
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-d) (by omega)) sample)) =
    anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
      (anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-d) (by omega)) sample) := by
  rw [cavityFixedRow_old_selectedMeanSquare]
  unfold cavityFixedRowRestFieldSquare cavityFiniteEnergyRestOverlap
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cavityFixedRowSpinFeature_at_native_scheme_node D s d hd]
  rfl

end QuantitativeFollowup
