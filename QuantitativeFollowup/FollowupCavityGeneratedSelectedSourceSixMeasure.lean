module
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayload
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Genuine finite-measure calculus for the selected payloads. The
supporting hypotheses below are measurability and a common value bound;
the model producer discharges them from the actual marked laws. No
sampling, Fubini or source-equality conclusion is a hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem abs_cavityGeneratedOriginCellMask_le
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (Φ : NativeStreamingOrigin T → ℝ) (C : ℝ) (hC : 0≤C)
    (hΦ : ∀o,|Φ o|≤C) (o : NativeStreamingOrigin T) :
    |cavityGeneratedOriginCellMask q T Φ o|≤C := by
  cases o with
  | vertex v => exact hΦ _
  | edge e r =>
      by_cases hr : r∈Ioc (q (e.depth+1)) (q e.depth)
      · simpa only [cavityGeneratedOriginCellMask,if_pos hr] using hΦ (.edge e r)
      · simpa only [cavityGeneratedOriginCellMask,if_neg hr,abs_zero] using hC

theorem integral_cavityGeneratedSelectedOriginPayload
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq0 : q 0=1)
    (T : FiniteTerminalGenealogy J) (s : ℝ) (hs : s≤Paper.parisiCDF μ (q J))
    (Φ : NativeStreamingOrigin T → ℝ)
    (hΦ : Measurable (cavityGeneratedSelectedOriginPayload q T Φ))
    (C : ℝ) (hC : 0≤C) (hbound : ∀o,|Φ o|≤C) :
    (∫g,cavityGeneratedSelectedOriginPayload q T Φ g
      ∂cavityGeneratedOriginSelectionMeasure μ a q T s)=
      nativeStreamingOriginWeightIntegral μ a q T s Φ := by
  have he := integral_cavityGeneratedOriginSelectionMeasure μ a q hq0 T s hs
    (cavityGeneratedOriginCellMask q T Φ) hΦ C
    (abs_cavityGeneratedOriginCellMask_le q T Φ C hC hbound)
  exact he.trans (nativeStreamingOriginWeightIntegral_cellMask μ a q T s Φ)

private theorem originCellMask_integral
    {X : Type*} [MeasurableSpace X] (M : Measure X)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (Φ : X → NativeStreamingOrigin T → ℝ) (o : NativeStreamingOrigin T) :
    (∫x,cavityGeneratedOriginCellMask q T (Φ x) o ∂M)=
      cavityGeneratedOriginCellMask q T (fun p => ∫x,Φ x p ∂M) o := by
  cases o with
  | vertex v => rfl
  | edge e r =>
      by_cases hr : r∈Ioc (q (e.depth+1)) (q e.depth) <;>
        simp only [cavityGeneratedOriginCellMask,hr,ite_true,ite_false,integral_zero]

theorem integral_cavityGeneratedSelectedOriginPayload_parameter
    {X : Type*} [MeasurableSpace X] (N : Measure X) [IsFiniteMeasure N]
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (hq0 : q 0=1)
    (T : FiniteTerminalGenealogy J) (s : ℝ) (hs : s≤Paper.parisiCDF μ (q J))
    (Φ : X → NativeStreamingOrigin T → ℝ)
    (hΦ : Measurable (fun z : CavityGeneratedOriginSelection T × X =>
      cavityGeneratedSelectedOriginPayload q T (Φ z.2) z.1))
    (C : ℝ) (hC : 0≤C) (hbound : ∀x o,|Φ x o|≤C) :
    (∫z,cavityGeneratedSelectedOriginPayload q T (Φ z.2) z.1
      ∂(cavityGeneratedOriginSelectionMeasure μ a q T s).prod N)=
      nativeStreamingOriginWeightIntegral μ a q T s (fun o => ∫x,Φ x o ∂N) := by
  let M := cavityGeneratedOriginSelectionMeasure μ a q T s
  let K := fun z : CavityGeneratedOriginSelection T × X =>
    cavityGeneratedSelectedOriginPayload q T (Φ z.2) z.1
  have hb z : |K z|≤C := abs_cavityGeneratedOriginCellMask_le q T (Φ z.2)
    C hC (hbound z.2) _
  have hi : Integrable K (M.prod N) := (integrable_const C).mono'
    hΦ.aestronglyMeasurable (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z)
  let H := fun o => ∫x,Φ x o ∂N
  have he (g : CavityGeneratedOriginSelection T) :
      (∫x,K (g,x) ∂N)=cavityGeneratedSelectedOriginPayload q T H g := by
    change (∫x,cavityGeneratedOriginCellMask q T (Φ x)
      (cavityGeneratedOriginSelectionOrigin T g) ∂N)=
        cavityGeneratedOriginCellMask q T (fun p=>∫x,Φ x p ∂N)
          (cavityGeneratedOriginSelectionOrigin T g)
    exact originCellMask_integral N q T Φ _
  have hm : Measurable (cavityGeneratedSelectedOriginPayload q T H) := by
    have hh := hΦ.stronglyMeasurable.integral_prod_right' (ν := N)
    convert hh.measurable using 1
    funext g
    exact (he g).symm
  have hH o : |H o|≤N.real univ*C := by
    simpa only [H,Real.norm_eq_abs,mul_comm] using
      norm_integral_le_of_norm_le_const (μ := N) (f := fun x => Φ x o) (C := C)
        (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x o)
  have hNC : 0≤N.real univ*C := mul_nonneg (measureReal_nonneg) hC
  calc
    (∫z,K z ∂M.prod N)=(∫g,∫x,K (g,x) ∂N ∂M) := integral_prod K hi
    _ = ∫g,cavityGeneratedSelectedOriginPayload q T H g ∂M :=
      integral_congr_ae (.of_forall he)
    _ = nativeStreamingOriginWeightIntegral μ a q T s H :=
      integral_cavityGeneratedSelectedOriginPayload μ a q hq0 T s hs H hm
        (N.real univ*C) hNC hH

private theorem origin_doubleCellMask_weight
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (s : ℝ)
    (Φ : NativeStreamingOrigin T → NativeStreamingOrigin T → ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T s (fun o =>
      nativeStreamingOriginWeightIntegral μ a q T s (fun p =>
        cavityGeneratedOriginCellMask q T
          (fun x => cavityGeneratedOriginCellMask q T (Φ x) p) o))=
      nativeStreamingOriginWeightIntegral μ a q T s (fun o =>
        nativeStreamingOriginWeightIntegral μ a q T s (Φ o)) := by
  apply nativeStreamingOriginWeightIntegral_congr_ae_edges μ a q T s
  · intro v
    exact nativeStreamingOriginWeightIntegral_cellMask μ a q T s (Φ (.vertex v))
  · intro e
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change nativeStreamingOriginWeightIntegral μ a q T s
      (fun p => if r∈Ioc (q (e.depth+1)) (q e.depth) then
        cavityGeneratedOriginCellMask q T (Φ (.edge e r)) p else 0)=_
    simp only [if_pos hr]
    exact nativeStreamingOriginWeightIntegral_cellMask μ a q T s (Φ (.edge e r))

theorem integral_cavityGeneratedSelectedOriginPayload_double
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (hq0 : q 0=1) (T : FiniteTerminalGenealogy J)
    (s : ℝ) (hs : s≤Paper.parisiCDF μ (q J))
    (Φ : NativeStreamingOrigin T → NativeStreamingOrigin T → ℝ)
    (hΦ : Measurable (fun z : CavityGeneratedOriginSelection T × CavityGeneratedOriginSelection T =>
      cavityGeneratedSelectedOriginPayload q T (fun o =>
        cavityGeneratedSelectedOriginPayload q T (Φ o) z.2) z.1))
    (C : ℝ) (hC : 0≤C) (hbound : ∀o p,|Φ o p|≤C) :
    (∫z,cavityGeneratedSelectedOriginPayload q T (fun o =>
      cavityGeneratedSelectedOriginPayload q T (Φ o) z.2) z.1
      ∂(cavityGeneratedOriginSelectionMeasure μ a q T s).prod
        (cavityGeneratedOriginSelectionMeasure μ a q T s))=
      nativeStreamingOriginWeightIntegral μ a q T s (fun o =>
        nativeStreamingOriginWeightIntegral μ a q T s (Φ o)) := by
  let M := cavityGeneratedOriginSelectionMeasure μ a q T s
  let A := fun o p => cavityGeneratedOriginCellMask q T
    (fun x => cavityGeneratedOriginCellMask q T (Φ x) p) o
  let K := fun z : CavityGeneratedOriginSelection T × CavityGeneratedOriginSelection T =>
    A (cavityGeneratedOriginSelectionOrigin T z.1) (cavityGeneratedOriginSelectionOrigin T z.2)
  have hb o p : |A o p|≤C := abs_cavityGeneratedOriginCellMask_le q T _ C hC
    (fun x => abs_cavityGeneratedOriginCellMask_le q T (Φ x) C hC (hbound x) p) o
  have hi : Integrable K (M.prod M) := (integrable_const C).mono'
    hΦ.aestronglyMeasurable (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb _ _)
  let H := fun o => nativeStreamingOriginWeightIntegral μ a q T s (A o)
  have he (g : CavityGeneratedOriginSelection T) :
      (∫k,K (g,k) ∂M)=H (cavityGeneratedOriginSelectionOrigin T g) := by
    change (∫k,A (cavityGeneratedOriginSelectionOrigin T g)
      (cavityGeneratedOriginSelectionOrigin T k) ∂cavityGeneratedOriginSelectionMeasure μ a q T s)=
        nativeStreamingOriginWeightIntegral μ a q T s
          (A (cavityGeneratedOriginSelectionOrigin T g))
    exact integral_cavityGeneratedOriginSelectionMeasure μ a q hq0 T s hs
      (A (cavityGeneratedOriginSelectionOrigin T g))
      (hΦ.comp measurable_prodMk_left) C (hb _)
  have hm : Measurable (fun g => H (cavityGeneratedOriginSelectionOrigin T g)) := by
    have hh := hΦ.stronglyMeasurable.integral_prod_right' (ν := M)
    convert hh.measurable using 1
    funext g
    exact (he g).symm
  have hH o : |H o|≤C*((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s) :=
    nativeStreamingOriginWeightIntegral_abs_le μ a ha hμ q hq T s hs C hC (A o) (hb o)
  calc
    (∫z,K z ∂M.prod M)=(∫g,∫k,K (g,k) ∂M ∂M) := integral_prod K hi
    _ = ∫g,H (cavityGeneratedOriginSelectionOrigin T g) ∂M :=
      integral_congr_ae (.of_forall he)
    _ = nativeStreamingOriginWeightIntegral μ a q T s H :=
      integral_cavityGeneratedOriginSelectionMeasure μ a q hq0 T s hs H hm
        (C*((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)) hH
    _ = nativeStreamingOriginWeightIntegral μ a q T s (fun o =>
        nativeStreamingOriginWeightIntegral μ a q T s (Φ o)) :=
      origin_doubleCellMask_weight μ a q T s Φ

end QuantitativeFollowup
