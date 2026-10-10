module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral

@[expose] public section

/-! Separate genuine edge integrals from inherited fork charges.  The
incoming root mass remains explicit; no mark coherence is required for
this algebraic identity.  Equal-time and atom regrouping are subsequent
identities for the actual conditional mark laws. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 900000

@[reducible] def nativeStreamingOriginEdgeWeightIntegral
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      (NativeStreamingOrigin T → ℝ) → ℝ
  | _, .leaf, Φ => (1-Paper.parisiCDF μ (q 0))*Φ (.vertex (.root .leaf))
  | _, @FiniteTerminalGenealogy.advance j T, Φ =>
      nativeStreamingOriginEdgeWeightIntegral μ a q T
        (fun o => Φ (nativeStreamingOriginChild o)) +
      (∫r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a)
  | _, .fork T U, Φ =>
      nativeStreamingOriginEdgeWeightIntegral μ a q T
        (fun o => Φ (nativeStreamingOriginLeft o)) +
      nativeStreamingOriginEdgeWeightIntegral μ a q U
        (fun o => Φ (nativeStreamingOriginRight o))

@[reducible] def nativeStreamingOriginBranchWeightSum
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      (NativeStreamingOrigin T → ℝ) → ℝ
  | _, .leaf, _ => 0
  | _, .advance T, Φ => nativeStreamingOriginBranchWeightSum μ q T
      (fun o => Φ (nativeStreamingOriginChild o))
  | j, .fork T U, Φ =>
      nativeStreamingOriginBranchWeightSum μ q T
        (fun o => Φ (nativeStreamingOriginLeft o)) +
      nativeStreamingOriginBranchWeightSum μ q U
        (fun o => Φ (nativeStreamingOriginRight o)) +
      Paper.parisiCDF μ (q j)*Φ (.vertex (.root (.fork T U)))

theorem nativeStreamingOriginWeightIntegral_eq_edges_branches_root
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (Φ : NativeStreamingOrigin T → ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T s Φ =
      nativeStreamingOriginEdgeWeightIntegral μ a q T Φ +
      nativeStreamingOriginBranchWeightSum μ q T Φ +
      (Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root T)) := by
  induction T generalizing s with
  | leaf =>
      simp only [nativeStreamingOriginWeightIntegral,
        nativeStreamingOriginEdgeWeightIntegral, nativeStreamingOriginBranchWeightSum]
      ring
  | @advance j T ih =>
      simp only [nativeStreamingOriginWeightIntegral,
        nativeStreamingOriginEdgeWeightIntegral, nativeStreamingOriginBranchWeightSum]
      rw [ih]
      simp only [sub_self, zero_mul, add_zero]
      ring
  | @fork j T U ihT ihU =>
      simp only [nativeStreamingOriginWeightIntegral,
        nativeStreamingOriginEdgeWeightIntegral, nativeStreamingOriginBranchWeightSum]
      rw [ihT, ihU]
      simp only [sub_self, zero_mul, add_zero]
      ring

theorem nativeStreamingOriginWeightIntegral_eq_edges_branches
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Φ : NativeStreamingOrigin T → ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T (Paper.parisiCDF μ (q j)) Φ =
      nativeStreamingOriginEdgeWeightIntegral μ a q T Φ +
      nativeStreamingOriginBranchWeightSum μ q T Φ := by
  rw [nativeStreamingOriginWeightIntegral_eq_edges_branches_root]
  simp only [sub_self, zero_mul, add_zero]

theorem nativeStreamingOriginBranchWeightSum_leaf
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    (Φ : NativeStreamingOrigin (.leaf : FiniteTerminalGenealogy 0) → ℝ) :
    nativeStreamingOriginBranchWeightSum μ q .leaf Φ = 0 := rfl

end QuantitativeFollowup
