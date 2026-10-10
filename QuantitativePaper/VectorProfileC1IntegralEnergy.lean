module
public import QuantitativePaper.VectorProfileC1EnergyFields
public import QuantitativePaper.ResponseCellIntegralCauchySchwarz
public import QuantitativePaper.VectorProfileSecondVariationEnergy

@[expose] public section

/-! Actual finite-cell integral response energy bound. All endpoint
integrability and pointwise matrix inequalities are proved model inputs. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfileC1Cell_pointwise_energy_bound (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseC1Test) (i : ℕ) (hi : i≤k+1)
    (q : ℝ) (hq : q∈Ioo (s₀.q i) (s₀.q (i+1))) :
    let e:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) q.toNNReal/(1-t)
    let p:=vectorProfileC1CellPairing (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ w i q
    let x:=vectorProfileC1CellXiEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ w i q
    0≤e ∧ 0≤x ∧ p^2≤e*x := by
  have hq0 : 0≤q:=(s₀.q_nonneg (by omega)).trans hq.1.le
  have hqn : (q.toNNReal:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1)):=by
    simpa only [Real.coe_toNNReal _ hq0] using hq
  have hpos:=vectorProfile_expected_Xi_energy_nonneg hn s₀ s₁ β t outer θ hβ ht i hi hθ
    q.toNNReal hqn (w.value q) (w.slope q)
  have hcs:=vectorProfile_expected_Xi_cauchy_schwarz hn s₀ s₁ β t outer θ hβ ht i hi hθ
    q.toNNReal hqn (w.value q) (w.slope q)
  refine ⟨div_nonneg ?_ (by linarith),?_,?_⟩
  · exact integral_nonneg (fun sample=>mul_nonneg (by linarith : 0≤1-t)
      (responseMatrixFrobeniusSquare_nonneg _))
  · simpa only [vectorProfileC1CellXiEnergy,Real.coe_toNNReal _ hq0] using hpos
  · simpa only [vectorProfileC1CellXiEnergy,vectorProfileC1CellPairing,Real.coe_toNNReal _ hq0] using hcs

theorem vectorProfile_C1_integral_energy_bound (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (w : ResponseC1Test) :
    (∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),
      vectorProfileC1CellPairing (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ w i q)^2≤
      (vectorProfileSecondVariationTotalEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩/(1-t))*
      (∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),
        vectorProfileC1CellXiEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ w i q) := by
  let e:=fun (i : ℕ) (q : ℝ)=>vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) q.toNNReal/(1-t)
  have he (i : ℕ) (hi : i<k+2) : IntervalIntegrable (e i) volume (s₀.q i) (s₀.q (i+1)):=by
    have hab:=s₀.q_mono i (by omega)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (vectorProfile_second_variation_closed_source hn s₀ s₁ β t outer θ hβ ht i (by omega) hθ).1).div_const (1-t)
  have hh:=response_cell_integral_cauchy_schwarz (k+2) s₀.q e
    (vectorProfileC1CellPairing (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ w)
    (vectorProfileC1CellXiEnergy (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ w)
    (fun i hi=>s₀.q_mono i (by omega)) he
    (fun i hi=>intervalIntegrable_vectorProfileC1CellPairing hn s₀ s₁ β t outer θ hβ ht hθ w i (by omega))
    (fun i hi=>intervalIntegrable_vectorProfileC1CellXiEnergy hn s₀ s₁ β t outer θ hβ ht hθ w i (by omega))
    (fun i hi q hq=>vectorProfileC1Cell_pointwise_energy_bound hn s₀ s₁ β t outer θ hβ ht hθ w i (by omega) q hq)
  unfold e at hh
  simp_rw [intervalIntegral.integral_div] at hh
  rw [←Finset.sum_div] at hh
  exact hh

end QuantitativePaper
