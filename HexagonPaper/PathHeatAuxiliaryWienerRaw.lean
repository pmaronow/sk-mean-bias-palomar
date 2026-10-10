module
public import HexagonPaper.PathHeatAuxiliaryDifferentiation
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Integrating genuine conditional raw derivatives on a product reference.
The concrete source theorem discharges these intermediate conditional data.
There is one normalizer after auxiliary integration. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem pathHeat_auxiliary_Wiener_raw_derivatives
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (U : Set ℝ) (z : ℝ) (hU : U∈𝓝 z)
    (W F H J : ℝ→A×B→ℝ) (e : A×B→ℝ) (BF BH BJ : ℝ)
    (hBF : 0≤BF) (hBH : 0≤BH) (hBJ : 0≤BJ)
    (he : Integrable e (μ.prod ν)) (hes : ∀a,Integrable (fun b=>e (a,b)) ν)
    (hepos : ∀ω,0≤e ω)
    (hWmeas : ∀u∈U,StronglyMeasurable (W u))
    (hNmeas : ∀u∈U,StronglyMeasurable (fun ω=>W u ω*F u ω))
    (hZmeas : ∀u∈U,StronglyMeasurable (fun ω=>W u ω*H u ω))
    (hDmeas : ∀u∈U,StronglyMeasurable (fun ω=>W u ω*(J u ω+F u ω*H u ω)))
    (hbound : ∀u∈U,∀ω,0≤W u ω ∧ W u ω≤e ω ∧
      |F u ω|≤BF ∧ |H u ω|≤BH ∧ |J u ω|≤BJ)
    (hconditionalZ : ∀a,∀u∈U,HasDerivAt (fun v=>∫b,W v (a,b)∂ν)
      (∫b,W u (a,b)*H u (a,b)∂ν) u)
    (hconditionalN : ∀a,∀u∈U,HasDerivAt (fun v=>∫b,W v (a,b)*F v (a,b)∂ν)
      (∫b,W u (a,b)*(J u (a,b)+F u (a,b)*H u (a,b))∂ν) u) :
    HasDerivAt (fun u=>∫ω,W u ω∂μ.prod ν) (∫ω,W z ω*H z ω∂μ.prod ν) z ∧
    HasDerivAt (fun u=>∫ω,W u ω*F u ω∂μ.prod ν)
      (∫ω,W z ω*(J z ω+F z ω*H z ω)∂μ.prod ν) z := by
  have hz : z∈U := mem_of_mem_nhds hU
  have bounds (u : ℝ) (hu : u∈U) (ω : A×B) :
      ‖W u ω‖≤e ω ∧ ‖W u ω*F u ω‖≤BF*e ω ∧
      ‖W u ω*H u ω‖≤BH*e ω ∧
      ‖W u ω*(J u ω+F u ω*H u ω)‖≤(BJ+BF*BH)*e ω := by
    rcases hbound u hu ω with ⟨h0,hw,hf,hh,hj⟩
    have hn : ‖W u ω‖=W u ω := Real.norm_of_nonneg h0
    have hnF : ‖F u ω‖≤BF := hf
    have hnH : ‖H u ω‖≤BH := hh
    have hnJ : ‖J u ω‖≤BJ := hj
    have hmF := mul_le_mul hw hnF (norm_nonneg _) (hepos ω)
    have hmH := mul_le_mul hw hnH (norm_nonneg _) (hepos ω)
    have hsum : ‖J u ω+F u ω*H u ω‖≤BJ+BF*BH :=
      (norm_add_le _ _).trans (add_le_add hnJ (by
        rw [norm_mul]
        exact mul_le_mul hnF hnH (norm_nonneg _) hBF))
    refine ⟨by rwa [hn],?_,?_,?_⟩
    · simpa only [norm_mul,hn,mul_comm] using hmF
    · simpa only [norm_mul,hn,mul_comm] using hmH
    · rw [norm_mul,hn]
      exact (mul_le_mul hw hsum (norm_nonneg _) (hepos ω)).trans_eq (mul_comm _ _)
  have iW (u : ℝ) (hu : u∈U) : Integrable (W u) (μ.prod ν) :=
    he.mono' (hWmeas u hu).aestronglyMeasurable (.of_forall fun ω=>(bounds u hu ω).1)
  have iN (u : ℝ) (hu : u∈U) : Integrable (fun ω=>W u ω*F u ω) (μ.prod ν) :=
    (he.const_mul BF).mono' (hNmeas u hu).aestronglyMeasurable
      (.of_forall fun ω=>(bounds u hu ω).2.1)
  have iZ (u : ℝ) (hu : u∈U) : Integrable (fun ω=>W u ω*H u ω) (μ.prod ν) :=
    (he.const_mul BH).mono' (hZmeas u hu).aestronglyMeasurable
      (.of_forall fun ω=>(bounds u hu ω).2.2.1)
  have iD (u : ℝ) (hu : u∈U) : Integrable (fun ω=>W u ω*(J u ω+F u ω*H u ω)) (μ.prod ν) :=
    (he.const_mul (BJ+BF*BH)).mono' (hDmeas u hu).aestronglyMeasurable
      (.of_forall fun ω=>(bounds u hu ω).2.2.2)
  have auxZ : PathHeatAuxiliaryRawData μ
      (fun u a=>∫b,W u (a,b)∂ν) (fun u a=>∫b,W u (a,b)*H u (a,b)∂ν)
      U z (fun a=>BH*(∫b,e (a,b)∂ν)) := by
    constructor
    · intro u hu
      exact (hWmeas u hu).integral_prod_right'.aestronglyMeasurable
    · exact (iW z hz).integral_prod_left
    · exact (hZmeas z hz).integral_prod_right'.aestronglyMeasurable
    · intro a u hu
      have hi := (hes a).const_mul BH
      calc
        _ ≤ ∫b,BH*e (a,b)∂ν := norm_integral_le_of_norm_le hi
          (.of_forall fun b=>(bounds u hu (a,b)).2.2.1)
        _ = _ := integral_const_mul _ _
    · exact he.integral_prod_left.const_mul BH
    · exact hconditionalZ
  have auxN : PathHeatAuxiliaryRawData μ
      (fun u a=>∫b,W u (a,b)*F u (a,b)∂ν)
      (fun u a=>∫b,W u (a,b)*(J u (a,b)+F u (a,b)*H u (a,b))∂ν)
      U z (fun a=>(BJ+BF*BH)*(∫b,e (a,b)∂ν)) := by
    constructor
    · intro u hu
      exact (hNmeas u hu).integral_prod_right'.aestronglyMeasurable
    · exact (iN z hz).integral_prod_left
    · exact (hDmeas z hz).integral_prod_right'.aestronglyMeasurable
    · intro a u hu
      have hi := (hes a).const_mul (BJ+BF*BH)
      calc
        _ ≤ ∫b,(BJ+BF*BH)*e (a,b)∂ν := norm_integral_le_of_norm_le hi
          (.of_forall fun b=>(bounds u hu (a,b)).2.2.2)
        _ = _ := integral_const_mul _ _
    · exact he.integral_prod_left.const_mul (BJ+BF*BH)
    · exact hconditionalN
  have hzD := (hasDerivAt_pathHeat_auxiliary_raw_integral _ _ _ _ _ _ hU auxZ).2
  have hnD := (hasDerivAt_pathHeat_auxiliary_raw_integral _ _ _ _ _ _ hU auxN).2
  have eqZ : (fun u=>∫ω,W u ω∂μ.prod ν)=ᶠ[𝓝 z]
      (fun u=>∫a,∫b,W u (a,b)∂ν∂μ) := by
    filter_upwards [hU] with u hu
    exact integral_prod _ (iW u hu)
  have eqN : (fun u=>∫ω,W u ω*F u ω∂μ.prod ν)=ᶠ[𝓝 z]
      (fun u=>∫a,∫b,W u (a,b)*F u (a,b)∂ν∂μ) := by
    filter_upwards [hU] with u hu
    exact integral_prod _ (iN u hu)
  constructor
  · rw [integral_prod _ (iZ z hz)]
    exact hzD.congr_of_eventuallyEq eqZ
  · rw [integral_prod _ (iD z hz)]
    exact hnD.congr_of_eventuallyEq eqN

end HexagonPaper
