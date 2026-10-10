module
public import HexagonPaper.CavityFixedRowHeatDataObservable
public import HexagonPaper.CavityTreeNativeVarianceJets

@[expose] public section

/-! Actual retained last and rest squared magnetizations and all their
incident-row jets vary jointly continuously with the positive coefficient. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem continuous_cavityMovingVarianceCoordinate
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i k : Fin n)
    (p : Paper.Overlap) :
    Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter n =>
      fderiv ℝ (anisotropicMeasureTailPotential
        (anisotropicUnitCouplings (anisotropicReplaceVariance D i z.1.val)) μ p)
        z.2 (anisotropicCoordinateDirection n k)) := by
  have hc : Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter n => ((z.1,p),z.2)) :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hj := (cavityTree_native_tail_variance_jet_joint_continuous
    (anisotropicUnitCouplings D) μ i 1).comp hc
  have he := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => AnisotropicParameter n) ℝ
    (fun _ => anisotropicCoordinateDirection n k)).continuous.comp hj
  change Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter n =>
      fderiv ℝ (anisotropicMeasureTailPotential
        (anisotropicReplaceVariance (anisotropicUnitCouplings D) i z.1.val) μ p)
        z.2 (anisotropicCoordinateDirection n k))
  simpa only [Function.comp_def,ContinuousMultilinearMap.apply_apply,iteratedFDeriv_one_apply] using he

theorem continuous_cavityMovingVarianceLastSquare
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) :
    Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter (n+1) =>
      cavityFixedRowNativeLastFieldSquare (anisotropicReplaceVariance D i z.1.val) μ p z.2) :=
  (continuous_cavityMovingVarianceCoordinate D μ i (Fin.last n) p).pow 2

theorem continuous_cavityMovingVarianceRestSquare
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) :
    Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter (n+1) =>
      cavityFixedRowNativeRestFieldSquare (anisotropicReplaceVariance D i z.1.val) μ p z.2) := by
  exact continuous_const.mul (continuous_finsetSum Finset.univ fun (k : Fin n) _ =>
    (continuous_cavityMovingVarianceCoordinate D μ i k.castSucc p).pow 2)

theorem cavityMovingAffineObservable_jet_joint_continuous
    (G : {b : ℝ // 0<b}→AnisotropicParameter n→ℝ)
    (hG : Continuous (Function.uncurry G))
    (hs : ∀b,ContDiff ℝ ∞ (G b))
    (B : ℕ→ℝ) (hB : ∀r,0≤B r)
    (hb : ∀r b P,‖iteratedFDeriv ℝ r (G b) P‖≤B r)
    (P : {b : ℝ // 0<b}→AnisotropicParameter n) (hP : Continuous P)
    (L : Field m→L[ℝ]AnisotropicParameter n) (r : ℕ) :
    Continuous (fun z : {b : ℝ // 0<b}×Field m =>
      iteratedFDeriv ℝ r (fun y=>G z.1 (P z.1+L y)) z.2) := by
  let f := fun z : {b : ℝ // 0<b}×Field m => G z.1 (P z.1+L z.2)
  have hf : Continuous f := by
    have h := hG.comp (continuous_fst.prodMk
      ((hP.comp continuous_fst).add (L.continuous.comp continuous_snd)))
    exact h.congr fun z=>rfl
  have hss (b : {b : ℝ // 0<b}) : ContDiff ℝ ∞ (fun x=>f (b,x)) := by
    change ContDiff ℝ ∞ (fun x=>G b (P b+L x))
    have hi : ContDiff ℝ ∞ (fun x : Field m=>P b+L x) := contDiff_const.add L.contDiff
    exact (hs b).comp hi
  apply continuous_iteratedFDeriv_family_of_uniform_jet_bounds f hf
    hss
    (fun k=>B k*‖L‖^k) (fun k=>mul_nonneg (hB k) (pow_nonneg (norm_nonneg _) _)) _ r
  intro k hk b θ
  let g := fun x : AnisotropicParameter n => G b (P b+x)
  have hg : ContDiff ℝ ∞ g := (hs b).comp (contDiff_const.add contDiff_id)
  have he := L.iteratedFDeriv_comp_right hg θ (by simp : (k : WithTop ℕ∞)≤∞)
  change ‖iteratedFDeriv ℝ k (g ∘ L) θ‖≤_
  rw [he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [iteratedFDeriv_comp_add_left]
  exact mul_le_mul_of_nonneg_right (hb k b _) (pow_nonneg (norm_nonneg _) _)

theorem cavityMovingVarianceLastSquare_row_jet_joint_continuous
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) (P : {b : ℝ // 0<b}→AnisotropicParameter (n+1)) (hP : Continuous P)
    (r : ℕ) :
    Continuous (fun z : {b : ℝ // 0<b}×Field n => iteratedFDeriv ℝ r
      (fun y=>cavityFixedRowNativeLastFieldSquare (anisotropicReplaceVariance D i z.1.val)
        μ p (P z.1+cavityNativeFixedRowParameterChart n y)) z.2) := by
  let G := fun b : {b : ℝ // 0<b} =>
    cavityFixedRowNativeLastFieldSquare (anisotropicReplaceVariance D i b.val) μ p
  change Continuous (fun z : {b : ℝ // 0<b}×Field n =>
    iteratedFDeriv ℝ r (fun y=>G z.1 (P z.1+cavityNativeFixedRowParameterChart n y)) z.2)
  exact cavityMovingAffineObservable_jet_joint_continuous (n:=n+1) (m:=n) G
    (continuous_cavityMovingVarianceLastSquare D μ i p)
    (fun b=>(boundedJets_cavityFixedRowNativeLastFieldSquare (anisotropicReplaceVariance D i b.val) μ p).1)
    (cavityFixedRowSquareJetBound (n+1)) (cavityFixedRowSquareJetBound_nonneg (n+1))
    (fun k b Q=>cavityFixedRow_native_square_jet_uniform (anisotropicReplaceVariance D i b.val) μ p (Fin.last n) k Q)
    P hP (cavityNativeFixedRowParameterChart n) r

theorem cavityMovingVarianceRestSquare_row_jet_joint_continuous
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) (P : {b : ℝ // 0<b}→AnisotropicParameter (n+1)) (hP : Continuous P)
    (r : ℕ) :
    Continuous (fun z : {b : ℝ // 0<b}×Field n => iteratedFDeriv ℝ r
      (fun y=>cavityFixedRowNativeRestFieldSquare (anisotropicReplaceVariance D i z.1.val)
        μ p (P z.1+cavityNativeFixedRowParameterChart n y)) z.2) := by
  let G := fun b : {b : ℝ // 0<b} =>
    cavityFixedRowNativeRestFieldSquare (anisotropicReplaceVariance D i b.val) μ p
  change Continuous (fun z : {b : ℝ // 0<b}×Field n =>
    iteratedFDeriv ℝ r (fun y=>G z.1 (P z.1+cavityNativeFixedRowParameterChart n y)) z.2)
  exact cavityMovingAffineObservable_jet_joint_continuous (n:=n+1) (m:=n) G
    (continuous_cavityMovingVarianceRestSquare D μ i p)
    (fun b=>(boundedJets_cavityFixedRowNativeRestFieldSquare (anisotropicReplaceVariance D i b.val) μ p).1)
    (fun k=>|(n : ℝ)⁻¹| * (n : ℝ)*cavityFixedRowSquareJetBound (n+1) k)
    (fun k=>mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (cavityFixedRowSquareJetBound_nonneg (n+1) k))
    (fun k b Q=>cavityFixedRow_native_restSquare_jet_uniform (anisotropicReplaceVariance D i b.val) μ p k Q)
    P hP (cavityNativeFixedRowParameterChart n) r

end HexagonPaper
