module
public import HexagonPaper.PathHeatFiniteVarianceClockLaw
public import HexagonPaper.PathHeatNativeFieldCovariance
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! A concrete factory for the manuscript's independent active finite
coordinates and fixed tree rows. Finite coordinates are constant terminal
rows, not fictitious active paths; cross blocks of the reconstruction vanish. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A J : ℕ} {Z : Type*}

def pathHeatFiniteTreeClocks
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (z : Z) (l : Fin (A+J)) : C(I,I) :=
  Sum.elim (fun a=>pathHeatFiniteVarianceClock (v z a) V hV (hv z a) (hvV z a))
    (c z) (finSumFinEquiv.symm l)

def pathHeatFiniteTreeClockDerivatives (dv : Z→Fin A→ℝ) (V : ℝ)
    (dc : Z→Fin J→C(I,ℝ)) (z : Z) (l : Fin (A+J)) : C(I,ℝ) :=
  Sum.elim (fun a=>pathHeatFiniteVarianceClockDerivative (dv z a) V)
    (dc z) (finSumFinEquiv.symm l)

def pathHeatFiniteTreeDiagonal (δ : Fin J→ℝ) (l : Fin (A+J)) : ℝ :=
  Sum.elim (fun _=>0) δ (finSumFinEquiv.symm l)

def pathHeatFiniteTreeAncestor (V : ℝ) (W : Fin J→Fin J→ℝ)
    (l k : Fin (A+J)) : ℝ :=
  match finSumFinEquiv.symm l,finSumFinEquiv.symm k with
  | Sum.inl a,Sum.inl b => if a=b then Real.sqrt V else 0
  | Sum.inr j,Sum.inr k => W j k
  | _,_ => 0

theorem pathHeatFiniteTreeClocks_finite
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (z : Z) (a : Fin A) :
    pathHeatFiniteTreeClocks v V hV hv hvV c z (finSumFinEquiv (Sum.inl a))=
      pathHeatFiniteVarianceClock (v z a) V hV (hv z a) (hvV z a) := by
  simp [pathHeatFiniteTreeClocks]

theorem pathHeatFiniteTreeClocks_tree
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (z : Z) (j : Fin J) :
    pathHeatFiniteTreeClocks v V hV hv hvV c z (finSumFinEquiv (Sum.inr j))=c z j := by
  simp [pathHeatFiniteTreeClocks]

theorem continuous_pathHeatFiniteTreeClocks [TopologicalSpace Z]
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (hvc : ∀a,Continuous (fun z=>v z a)) (hc : ∀j,Continuous (fun z=>c z j))
    (l : Fin (A+J)) : Continuous (fun z=>pathHeatFiniteTreeClocks v V hV hv hvV c z l) := by
  rcases he : finSumFinEquiv.symm l with a|j
  · simp only [pathHeatFiniteTreeClocks,he,Sum.elim_inl]
    exact continuous_pathHeatFiniteVarianceClock_family (fun z=>v z a) V hV
      (fun z=>hv z a) (fun z=>hvV z a) (hvc a)
  · simpa only [pathHeatFiniteTreeClocks,he,Sum.elim_inr] using hc j

theorem continuous_pathHeatFiniteTreeClockDerivatives [TopologicalSpace Z]
    (dv : Z→Fin A→ℝ) (V : ℝ) (dc : Z→Fin J→C(I,ℝ))
    (hdvc : ∀a,Continuous (fun z=>dv z a)) (hdc : ∀j,Continuous (fun z=>dc z j))
    (l : Fin (A+J)) : Continuous (fun z=>pathHeatFiniteTreeClockDerivatives dv V dc z l) := by
  rcases he : finSumFinEquiv.symm l with a|j
  · simp only [pathHeatFiniteTreeClockDerivatives,he,Sum.elim_inl]
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_snd.subtype_val.mul ((hdvc a).comp continuous_fst)).div_const V
  · simpa only [pathHeatFiniteTreeClockDerivatives,he,Sum.elim_inr] using hdc j

theorem pathHeatFiniteTreeClocks_root
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (hr : ∀z j,c z j 0=0) (z : Z) (l : Fin (A+J)) :
    pathHeatFiniteTreeClocks v V hV hv hvV c z l 0=0 := by
  rcases he : finSumFinEquiv.symm l with a|j
  · simp [pathHeatFiniteTreeClocks,he]
  · simpa only [pathHeatFiniteTreeClocks,he,Sum.elim_inr] using hr z j

theorem pathHeatFiniteTreeClocks_strictMono
    (v : Z→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V) (c : Z→Fin J→C(I,I))
    (z : Z) (hvp : ∀a,0<v z a) (hc : ∀j,StrictMono (c z j)) (l : Fin (A+J)) :
    StrictMono (pathHeatFiniteTreeClocks v V hV hv hvV c z l) := by
  rcases he : finSumFinEquiv.symm l with a|j
  · simp only [pathHeatFiniteTreeClocks,he,Sum.elim_inl]
    exact pathHeatFiniteVarianceClock_strictMono (v z a) V hV (hvp a) (hvV z a)
  · simpa only [pathHeatFiniteTreeClocks,he,Sum.elim_inr] using hc j

theorem hasDerivAt_pathHeatFiniteTreeClocks
    (v dv : ℝ→Fin A→ℝ) (V : ℝ) (hV : 0<V)
    (hv : ∀z a,0≤v z a) (hvV : ∀z a,v z a≤V)
    (c : ℝ→Fin J→C(I,I)) (dc : ℝ→Fin J→C(I,ℝ)) (z : ℝ)
    (hdv : ∀a,HasDerivAt (fun u=>v u a) (dv z a) z)
    (hdc : ∀j t,HasDerivAt (fun u=>(c u j t:ℝ)) (dc z j t) z)
    (l : Fin (A+J)) (t : I) :
    HasDerivAt (fun u=>(pathHeatFiniteTreeClocks v V hV hv hvV c u l t:ℝ))
      (pathHeatFiniteTreeClockDerivatives dv V dc z l t) z := by
  rcases he : finSumFinEquiv.symm l with a|j
  · simp only [pathHeatFiniteTreeClocks,pathHeatFiniteTreeClockDerivatives,he,Sum.elim_inl]
    exact hasDerivAt_pathHeatFiniteVarianceClock (fun u=>v u a) (dv z a) V z hV
      (fun u=>hv u a) (fun u=>hvV u a) (hdv a) t
  · simpa only [pathHeatFiniteTreeClocks,pathHeatFiniteTreeClockDerivatives,he,Sum.elim_inr] using hdc j t

theorem exists_pathHeatFiniteVariance_uniform_scale [TopologicalSpace Z] [CompactSpace Z]
    (v : Z→Fin A→ℝ) (hv : ∀a,Continuous (fun z=>v z a)) :
    ∃V : ℝ,0<V ∧ ∀z a,v z a≤V := by
  have hc : Continuous (fun z=>∑a : Fin A,|v z a|) :=
    continuous_finset_sum _ (fun a _=>(hv a).abs)
  obtain ⟨B,hB⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  refine ⟨max B 0+1,by positivity,?_⟩
  intro z a
  have hsum : |v z a|≤∑b : Fin A,|v z b| :=
    Finset.single_le_sum (fun b _=>abs_nonneg (v z b)) (Finset.mem_univ a)
  have hb : (∑b : Fin A,|v z b|)≤B := hB ⟨z,mem_univ _,rfl⟩
  exact (le_abs_self _).trans (hsum.trans (hb.trans (by linarith [le_max_left B (0:ℝ)])))

end HexagonPaper
