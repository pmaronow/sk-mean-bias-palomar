module
public import QuantitativeFollowup.FollowupCavityThreeEndpointKernel
public import QuantitativeFollowup.FollowupCavityThreeNativeComparison
public import QuantitativeFollowup.FollowupCavityStandardEndpointModel
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! Genuine three-independent-continuation transport at the SK endpoint.
The old terminal spin and every new conditional terminal spin are retained;
the independent common diagonal disorder is removed exactly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def cavityVectorEndpointFreshKernel (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) : Kernel (VectorMarkedSample n) (Configuration n) :=
  (cavityVectorEndpointSpinKernel μ β t ht q).comap
    (fun p=>(p.1.1,vectorMeasureState μ β t ht (q:ℝ).toNNReal p.1))
    (measurable_fst.fst.prodMk
      ((measurable_vectorMeasureJointState μ β t ht (q:ℝ).toNNReal).snd.comp measurable_fst))

instance cavityVectorEndpointFreshKernel_markov (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    IsMarkovKernel (cavityVectorEndpointFreshKernel (n:=n) μ β t ht q) := by
  unfold cavityVectorEndpointFreshKernel
  infer_instance

def cavityVectorThreeDescendantLaw (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) : Measure (VectorMarkedSample n×CavityThreeTerminalSpins n) :=
  (vectorMeasureSpinPathLaw μ β t a ht) ⊗ₘ
    (((vectorConditionalTerminalSpinKernel μ β t a ht q) ×ₖ
      (vectorConditionalTerminalSpinKernel μ β t a ht q)) ×ₖ
      (vectorConditionalTerminalSpinKernel μ β t a ht q))

instance cavityVectorThreeDescendantLaw_probability (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    IsProbabilityMeasure (cavityVectorThreeDescendantLaw (n:=n) μ β t a ht q) := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  unfold cavityVectorThreeDescendantLaw
  infer_instance

theorem cavityVectorThreeDescendantLaw_eq_endpoint (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    cavityVectorThreeDescendantLaw (n:=n) μ β t a ht q=
      (vectorMeasureSpinPathLaw μ β t a ht) ⊗ₘ
        (((cavityVectorEndpointFreshKernel μ β t ht q) ×ₖ
          (cavityVectorEndpointFreshKernel μ β t ht q)) ×ₖ
          (cavityVectorEndpointFreshKernel μ β t ht q)) := by
  apply Measure.compProd_congr
  filter_upwards [vectorConditionalTerminalSpinKernel_eq_endpoint (n:=n) μ β t a ht q] with p hp
  simp only [Kernel.prod_apply,cavityVectorEndpointFreshKernel,Kernel.comap_apply]
  rw [hp]

theorem cavityVectorEndpointFreshKernel_removeDiagonal (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    (cavityVectorEndpointFreshKernel (n:=n) μ β t ht q).comap
      vectorRemoveDiagonalMarked measurable_vectorRemoveDiagonalMarked=
        cavityVectorEndpointFreshKernel μ β t ht q := by
  ext p A hA
  simp only [Kernel.comap_apply,cavityVectorEndpointFreshKernel,vectorRemoveDiagonalMarked]
  rw [←vectorMeasureState_diagonal_shift μ β t ht (q:ℝ).toNNReal
    (by simpa using Real.toNNReal_le_toNNReal q.property.2) p.1]
  exact congrArg (fun P:Measure (Configuration n)=>P A)
    (cavityVectorEndpointSpinKernel_removeDiagonal μ β t ht q p.1.1 _).symm

theorem standardSKOffDiagonalFreshTerminalSpinKernel (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    anisotropicFreshTerminalSpinKernel (standardSKOffDiagonalModel n β t hβ ht) μ a q=ᵐ[
      anisotropicMeasureSpinPathLaw (standardSKOffDiagonalModel n β t hβ ht) μ a]
      fun p=>cavityVectorEndpointFreshKernel μ β t ht.le q (standardSKOffDiagonalMarkedCompression p) := by
  filter_upwards [anisotropicFreshTerminalSpinKernel_eq_native_continuation
    (standardSKOffDiagonalModel n β t hβ ht) μ a q] with p hp
  rw [hp,standardSKOffDiagonalEndpointSpinKernel]
  have hnoise:=standardSKOffDiagonalNoiseMap β t hβ ht
    (anisotropicInverseNoiseMap (standardSKOffDiagonalModel n β t hβ ht)
      (anisotropicMeasureState (standardSKOffDiagonalModel n β t hβ ht) μ q p.1))
  rw [anisotropicNoiseMap_inverseNoise] at hnoise
  simp only [anisotropicNativeObservation]
  rw [←hnoise,standardSKOffDiagonalMeasureState μ β t hβ ht q q.property p.1]
  rfl

def cavityThreeEndpointCompression
    (z : (AnisotropicDisorderBrownianSample n×Configuration n)×CavityThreeTerminalSpins n) :
    VectorMarkedSample n×CavityThreeTerminalSpins n :=
  (standardSKOffDiagonalMarkedCompression z.1,z.2)

theorem measurable_cavityThreeEndpointCompression :
    Measurable (cavityThreeEndpointCompression (n:=n)) :=
  (measurable_standardSKOffDiagonalMarkedCompression.comp measurable_fst).prodMk measurable_snd

def cavityVectorThreeRemoveDiagonal (z : VectorMarkedSample n×CavityThreeTerminalSpins n) :
    VectorMarkedSample n×CavityThreeTerminalSpins n := (vectorRemoveDiagonalMarked z.1,z.2)

theorem measurable_cavityVectorThreeRemoveDiagonal :
    Measurable (cavityVectorThreeRemoveDiagonal (n:=n)) :=
  (measurable_vectorRemoveDiagonalMarked.comp measurable_fst).prodMk measurable_snd

theorem standardSKOffDiagonalThreeDescendantLaw (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    (cavityThreeDescendantLaw (standardSKOffDiagonalModel n β t hβ ht) μ a q).map
      cavityThreeEndpointCompression=
      (cavityVectorThreeDescendantLaw μ β t a ht.le q).map cavityVectorThreeRemoveDiagonal := by
  haveI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  let κ:=((cavityVectorEndpointFreshKernel (n:=n) μ β t ht.le q) ×ₖ
    (cavityVectorEndpointFreshKernel μ β t ht.le q)) ×ₖ
      (cavityVectorEndpointFreshKernel μ β t ht.le q)
  have he : cavityThreeDescendantLaw (standardSKOffDiagonalModel n β t hβ ht) μ a q=
      (anisotropicMeasureSpinPathLaw (standardSKOffDiagonalModel n β t hβ ht) μ a) ⊗ₘ
        κ.comap standardSKOffDiagonalMarkedCompression measurable_standardSKOffDiagonalMarkedCompression := by
    apply Measure.compProd_congr
    filter_upwards [standardSKOffDiagonalFreshTerminalSpinKernel μ β t a hβ ht q] with p hp
    simp only [Kernel.prod_apply,Kernel.comap_apply,κ]
    rw [hp]
  have hk : κ.comap vectorRemoveDiagonalMarked measurable_vectorRemoveDiagonalMarked=κ := by
    ext p A hA
    simp only [Kernel.comap_apply,Kernel.prod_apply,κ]
    have h:=congrArg (fun K:Kernel (VectorMarkedSample n) (Configuration n)=>K p)
      (cavityVectorEndpointFreshKernel_removeDiagonal μ β t ht.le q)
    simp only [Kernel.comap_apply] at h
    rw [h]
  rw [he,cavityVectorThreeDescendantLaw_eq_endpoint]
  change ((anisotropicMeasureSpinPathLaw _ μ a) ⊗ₘ κ.comap _ _).map
    (fun z=>(standardSKOffDiagonalMarkedCompression z.1,z.2))=
    ((vectorMeasureSpinPathLaw μ β t a ht.le) ⊗ₘ κ).map
      (fun z=>(vectorRemoveDiagonalMarked z.1,z.2))
  rw [compProd_comap_map_history _ _ measurable_standardSKOffDiagonalMarkedCompression,
    standardSKOffDiagonalMarkedLaw μ β t a hβ ht]
  have hv:=compProd_comap_map_history (vectorMeasureSpinPathLaw μ β t a ht.le)
    vectorRemoveDiagonalMarked measurable_vectorRemoveDiagonalMarked κ
  rw [hk] at hv
  exact hv.symm

end QuantitativeFollowup
