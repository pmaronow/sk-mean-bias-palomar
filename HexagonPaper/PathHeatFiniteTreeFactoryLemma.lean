module
public import HexagonPaper.PathHeatFiniteTreeLemma
public import HexagonPaper.PathHeatFiniteTreeModelEvaluation

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

theorem lem_fnd_path_heat_variances_and_tree
    (μ : Measure E) [IsGaussian μ] (hab : a<b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (pathHeatFiniteTreeIndex A J))
    (C : ℝ≥0) (hs : PathHeatFiniteTreeSourceHypotheses a b hab.le d C)
    (v dv : Icc a b→Fin A→ℝ) (hv : ∀z a,0≤v z a)
    (hvc : ∀a,Continuous (fun z=>v z a)) (hdvc : ∀a,Continuous (fun z=>dv z a))
    (hvp : ∀z : Icc a b,z.val∈Ioo a b→∀a,0<v z a)
    (hdv : ∀z∈Ioo a b,∀α,HasDerivAt (fun u=>v (projIcc a b hab.le u) α)
      (dv (projIcc a b hab.le z) α) z)
    (ct : Icc a b→Fin J→C(I,I)) (dct : Icc a b→Fin J→C(I,ℝ))
    (δt : Fin J→ℝ) (Wt : Fin J→Fin J→ℝ)
    (hc : ∀j,Continuous (fun z=>ct z j)) (hdcc : ∀j,Continuous (fun z=>dct z j))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀j,StrictMono (ct z j))
    (hroot : ∀z j,ct z j 0=0)
    (hdc : ∀z∈Ioo a b,∀j t,
      HasDerivAt (fun u=>(ct (projIcc a b hab.le u) j t:ℝ))
        (dct (projIcc a b hab.le z) j t) z) :
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
  let hscale := exists_pathHeatFiniteVariance_uniform_scale v hvc
  let V := Classical.choose hscale
  have hV : 0<V := (Classical.choose_spec hscale).1
  have hvV : ∀z a,v z a≤V := (Classical.choose_spec hscale).2
  let c := pathHeatFiniteTreeClocks v V hV hv hvV ct
  let dc := pathHeatFiniteTreeClockDerivatives dv V dct
  let δ := pathHeatFiniteTreeDiagonal (A:=A) δt
  let W := pathHeatFiniteTreeAncestor (A:=A) V Wt
  apply lem_fnd_path_heat_finite_tree μ hab d C hs c dc δ W
  · exact continuous_pathHeatFiniteTreeClocks v V hV hv hvV ct hvc hc
  · exact continuous_pathHeatFiniteTreeClockDerivatives dv V dct hdvc hdcc
  · intro z hz
    exact pathHeatFiniteTreeClocks_strictMono v V hV hv hvV ct z (hvp z hz) (hstrict z hz)
  · exact pathHeatFiniteTreeClocks_root v V hV hv hvV ct hroot
  · intro z hz
    exact hasDerivAt_pathHeatFiniteTreeClocks
      (fun u=>v (projIcc a b hab.le u)) (fun u=>dv (projIcc a b hab.le u)) V hV
      (fun u=>hv (projIcc a b hab.le u)) (fun u=>hvV (projIcc a b hab.le u))
      (fun u=>ct (projIcc a b hab.le u)) (fun u=>dct (projIcc a b hab.le u))
      z (hdv z hz) (hdc z hz)

end HexagonPaper
