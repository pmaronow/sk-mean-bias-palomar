module
public import QuantitativeFollowup.ScalarTransportGradientVariation
public import QuantitativeFollowup.ScalarTransportResponseOfPartials

@[expose] public section

/-! Genuine parameter partials of the literal Gaussian density and square
observable. These use the moved-node potential variation and its proved
spatial derivative, with bounds independent of the finite profile. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportExponentPartial (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (x : QuantitativePaper.Field (k+3)) : ℝ :=
  -∑i : Fin (k+1),(s.m (i+1)-s.m i)*
    scalarTransportPotentialVariation β (Paper.parisiSchemeMeasure s) φ u
      (scalarSchemeTransportNode s (i+1)) (x ⟨i+1,by omega⟩)

def scalarTransportSquarePartial (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (u : ℝ)
    (x : QuantitativePaper.Field (k+3)) : ℝ :=
  2*scalarTransportNodeGradient s β φ p u (x p)*
    scalarTransportPotentialVariationSpatial β (Paper.parisiSchemeMeasure s) φ u
      (scalarSchemeTransportNode s p) (x p)

theorem hasDerivAt_scalarTransportNodeGradient_parameter (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (hu : |u|<δ)
    (i : ℕ) (hi : i ≤ k+2) :
    HasDerivAt (fun v=>scalarTransportNodeGradient s β φ i v x)
      (scalarTransportPotentialVariationSpatial β (Paper.parisiSchemeMeasure s) φ u
        (scalarSchemeTransportNode s i) x) u := by
  have hd := hasDerivAt_scalarTransportBoundaryGradient_variation s β hβ φ L hφ h0 h1
    δ u x hδ hsmall hu (k+2-i) (by omega)
  simpa only [Nat.sub_sub_self hi,scalarTransportBoundaryGradient,scalarTransportNodeGradient] using hd

theorem hasDerivAt_scalarTransportEuclideanExponent_parameter (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (hu : |u|<δ)
    (e : Bool) (x : QuantitativePaper.Field (k+3)) :
    HasDerivAt (fun v=>scalarTransportEuclideanExponent s β φ e v x)
      (scalarTransportExponentPartial s β φ u x) u := by
  have hs : HasDerivAt (fun v=>∑i : Fin (k+1),(s.m (i+1)-s.m i)*
      scalarTransportNodePotential s β φ (i+1) v (x ⟨i+1,by omega⟩))
      (∑i : Fin (k+1),(s.m (i+1)-s.m i)*scalarTransportPotentialVariation β
        (Paper.parisiSchemeMeasure s) φ u (scalarSchemeTransportNode s (i+1)) (x ⟨i+1,by omega⟩)) u := by
    apply HasDerivAt.fun_sum
    intro i _
    have hi : (i:ℕ)+1 ≤ k+2 := by omega
    have hd := hasDerivAt_scalarTransportNodePotential_variation s β hβ φ L hφ h0 h1
      δ u (x ⟨i+1,by omega⟩) hδ hsmall hu (k+2-(i+1)) (by omega)
    simpa only [Nat.sub_sub_self hi] using hd.const_mul (s.m (i+1)-s.m i)
  convert! (hasDerivAt_const u (Paper.spinSign e*x (Fin.last (k+2)))).sub hs using 1 <;>
    dsimp only [scalarTransportEuclideanExponent,scalarTransportExponentPartial,Pi.sub_apply] <;>
    first | rfl | ring

theorem hasDerivAt_scalarTransportGradientSquare_parameter (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (hu : |u|<δ)
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    HasDerivAt (fun v=>scalarTransportGradientSquare s β φ p v x)
      (scalarTransportSquarePartial s β φ p u x) u := by
  have hd := (hasDerivAt_scalarTransportNodeGradient_parameter s β hβ φ L hφ h0 h1
    δ u (x p) hδ hsmall hu p (by omega)).pow 2
  convert! hd using 1 <;> dsimp only [scalarTransportGradientSquare,scalarTransportSquarePartial] <;>
    first | rfl | ring

theorem continuous_scalarTransportExponentPartial (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) :
    Continuous (Function.uncurry (scalarTransportExponentPartial s β φ)) := by
  unfold scalarTransportExponentPartial Function.uncurry
  apply Continuous.neg
  apply continuous_finsetSum
  intro i _
  have ha : Continuous (fun z : ℝ×QuantitativePaper.Field (k+3)=>
      (z.1,z.2 ⟨i+1,by omega⟩)) := continuous_fst.prodMk
    ((EuclideanSpace.proj (⟨i+1,by omega⟩ : Fin (k+3))).continuous.comp continuous_snd)
  exact ((continuous_scalarTransportPotentialVariation β hβ (Paper.parisiSchemeMeasure s)
    φ (scalarSchemeTransportNode s (i+1))).comp ha).const_mul _

theorem continuous_scalarTransportSquarePartial (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) :
    Continuous (Function.uncurry (scalarTransportSquarePartial s β φ p)) := by
  have ha : Continuous (fun z : ℝ×QuantitativePaper.Field (k+3)=>(z.1,z.2 p)) :=
    continuous_fst.prodMk ((EuclideanSpace.proj p).continuous.comp continuous_snd)
  have hg := (continuous_scalarTransportNodeGradient s β φ p).comp ha
  have he := (continuous_scalarTransportPotentialVariationSpatial β hβ
    (Paper.parisiSchemeMeasure s) φ (scalarSchemeTransportNode s p)).comp ha
  convert! (hg.const_mul 2).mul he using 1

theorem norm_scalarTransportExponentPartial_le (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (x : QuantitativePaper.Field (k+3)) :
    ‖scalarTransportExponentPartial s β φ u x‖ ≤ 3*β^2/2*‖φ‖ := by
  unfold scalarTransportExponentPartial
  rw [norm_neg]
  calc
    _  ≤  ∑i : Fin (k+1),‖(s.m (i+1)-s.m i)*scalarTransportPotentialVariation β
      (Paper.parisiSchemeMeasure s) φ u (scalarSchemeTransportNode s (i+1)) (x ⟨i+1,by omega⟩)‖ := norm_sum_le _ _
    _  ≤  ∑i : Fin (k+1),(s.m (i+1)-s.m i)*(3*β^2/2*‖φ‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Real.norm_of_nonneg (sub_nonneg.mpr (s.m_mono i (by omega)))]
      exact mul_le_mul_of_nonneg_left (norm_scalarTransportPotentialVariation_le β _ φ u _ _)
        (sub_nonneg.mpr (s.m_mono i (by omega)))
    _ = _ := by rw [←Finset.sum_mul,scalarScheme_mass_sum,one_mul]

theorem norm_scalarTransportSquarePartial_le (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (u : ℝ)
    (x : QuantitativePaper.Field (k+3)) :
    ‖scalarTransportSquarePartial s β φ p u x‖ ≤ 2*scalarTransportVariationSpatialBound β φ := by
  unfold scalarTransportSquarePartial
  rw [norm_mul,norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
  have hm : ‖scalarTransportNodeGradient s β φ p u (x p)‖ ≤ 1 :=
    Paper.norm_parisiGradient_le_one β _ _
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num))
    (norm_scalarTransportPotentialVariationSpatial_le β _ φ u _ _)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring)

end QuantitativeFollowup
