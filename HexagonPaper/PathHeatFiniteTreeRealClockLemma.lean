module
public import HexagonPaper.PathHeatFiniteTreeFactoryLemma
public import HexagonPaper.PathHeatFiniteTreeModelRealClock

@[expose] public section

/-! The normalized Gaussian path heat lemma on the genuine reference law.
The source derivative measures retain their original index and atoms.
Auxiliary signed jets need only fixed-auxiliary TV continuity. Actual
Gaussian observations, finite Price differentiation, raw auxiliary/count
integration, Bernstein limits and common Fernique domination are proved
inside the imported chain. No density, response, normalizer positivity,
finite derivative or limiting derivative is an input hypothesis. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {A J : ℕ} {a b : ℝ}

theorem lem_fnd_path_heat_arbitrary_real_clocks
    (μ : Measure E) [IsGaussian μ] (hab : a<b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (pathHeatFiniteTreeIndex A J))
    (C : ℝ≥0) (hs : PathHeatFiniteTreeSourceHypotheses a b hab.le d C)
    (v dv : Icc a b→Fin A→ℝ) (hv : ∀z a,0≤v z a)
    (hvc : ∀a,Continuous (fun z=>v z a)) (hdvc : ∀a,Continuous (fun z=>dv z a))
    (hvp : ∀z : Icc a b,z.val∈Ioo a b→∀a,0<v z a)
    (hdv : ∀z∈Ioo a b,∀α,HasDerivAt (fun u=>v (projIcc a b hab.le u) α)
      (dv (projIcc a b hab.le z) α) z)
    (cr : Icc a b→Fin J→C(I,ℝ)) (dcr : Icc a b→Fin J→C(I,ℝ))
    (δr : Fin J→ℝ) (Wr : Fin J→Fin J→ℝ)
    (hc : ∀j,Continuous (fun z=>cr z j)) (hdcc : ∀j,Continuous (fun z=>dcr z j))
    (hm : ∀z j,Monotone (cr z j))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀j,StrictMono (cr z j))
    (hroot : ∀z j,cr z j 0=0)
    (hdc : ∀z∈Ioo a b,∀j t,
      HasDerivAt (fun u=>cr (projIcc a b hab.le u) j t)
        (dcr (projIcc a b hab.le z) j t) z) :
    let hclockScale := exists_pathHeatRealClock_uniform_scale cr hc
    let R := Classical.choose hclockScale
    let hR := (Classical.choose_spec hclockScale).1
    let hrBound := (Classical.choose_spec hclockScale).2
    let hrNonneg := fun z j=>pathHeatRealClock_nonneg (cr z j) (hm z j) (hroot z j)
    let ct := fun z j=>pathHeatRealClockNormalize (cr z j) R hR (hrNonneg z j) (hrBound z j)
    let dct := fun z j=>pathHeatRealClockNormalizeDerivative (dcr z j) R
    let δt := fun j=>δr j*Real.sqrt R
    let Wt := fun j k=>Wr j k*Real.sqrt R
    let hscale := exists_pathHeatFiniteVariance_uniform_scale v hvc
    let V := Classical.choose hscale
    let hV := (Classical.choose_spec hscale).1
    let hvV := (Classical.choose_spec hscale).2
    let c := pathHeatFiniteTreeClocks v V hV hv hvV ct
    let dc := pathHeatFiniteTreeClockDerivatives dv V dct
    let δ := pathHeatFiniteTreeDiagonal (A:=A) δt
    let W := pathHeatFiniteTreeAncestor (A:=A) V Wt
    let ι := pathHeatFiniteTreeIndexEmbedding A J
    let f := fun u=>pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W (projIcc a b hab.le u)
    let r := fun u=>pathHeatSourcePrintedResponse μ d ι c dc δ W (projIcc a b hab.le u)
    let g := fun u=>Real.log (pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab.le u))
    let s := fun u=>pathHeatSourcePrintedLogNormalizerResponse μ d ι c dc δ W (projIcc a b hab.le u)
    (∀z,0<pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W z) ∧
    (∀x∈Ioo a b,HasDerivAt f (r x) x ∧ HasDerivAt g (s x) x) ∧
    ContDiffOn ℝ 1 f (Ioo a b) ∧ ContDiffOn ℝ 1 g (Ioo a b) ∧
    HasDerivWithinAt f (r a) (Ici a) a ∧ HasDerivWithinAt f (r b) (Iic b) b ∧
    HasDerivWithinAt g (s a) (Ici a) a ∧ HasDerivWithinAt g (s b) (Iic b) b := by
  dsimp only
  let hclockScale := exists_pathHeatRealClock_uniform_scale cr hc
  let R := Classical.choose hclockScale
  have hR : 0<R := (Classical.choose_spec hclockScale).1
  have hrBound : ∀z j q,cr z j q≤R := (Classical.choose_spec hclockScale).2
  have hrNonneg : ∀z j q,0≤cr z j q :=
    fun z j=>pathHeatRealClock_nonneg (cr z j) (hm z j) (hroot z j)
  let ct := fun z j=>pathHeatRealClockNormalize (cr z j) R hR (hrNonneg z j) (hrBound z j)
  let dct := fun z j=>pathHeatRealClockNormalizeDerivative (dcr z j) R
  let δt := fun j=>δr j*Real.sqrt R
  let Wt := fun j k=>Wr j k*Real.sqrt R
  apply lem_fnd_path_heat_variances_and_tree μ hab d C hs v dv hv hvc hdvc hvp hdv ct dct δt Wt
  · intro j
    exact continuous_pathHeatRealClockNormalize_family (fun z=>cr z j) R hR
      (fun z=>hrNonneg z j) (fun z=>hrBound z j) (hc j)
  · intro j
    exact continuous_pathHeatRealClockNormalizeDerivative_family (fun z=>dcr z j) R (hdcc j)
  · intro z hz j
    exact pathHeatRealClockNormalize_strictMono (cr z j) R hR (hrNonneg z j)
      (hrBound z j) (hstrict z hz j)
  · intro z j
    exact pathHeatRealClockNormalize_root (cr z j) R hR (hrNonneg z j) (hrBound z j) (hroot z j)
  · intro z hz j t
    exact hasDerivAt_pathHeatRealClockNormalize
      (fun u=>cr (projIcc a b hab.le u) j) (dcr (projIcc a b hab.le z) j) R z hR
      (fun u=>hrNonneg (projIcc a b hab.le u) j) (fun u=>hrBound (projIcc a b hab.le u) j)
      (hdc z hz j) t

end HexagonPaper
