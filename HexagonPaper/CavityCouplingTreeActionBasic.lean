module
public import HexagonPaper.CavityCouplingTreeTransport
public import HexagonPaper.CavityTreePointAction

@[expose] public section

/-! Actual tagged full tree fields translate by the deterministic coupling
injection, including terminal placeholders and every branch mark. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped Topology ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem treeNativePointData_coupling_translation (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) (h : AnisotropicDisorder n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (x : AnisotropicObservationState n)
    (Z : Records (NativeTreePath n) (Configuration n) T) (v : treePathWeightPoint T) :
    treeNativePointData D q T (cavityCouplingStartTranslation h x)
      (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z) v=
      ((treeNativePointData D q T x Z v).1,
        (treeNativePointData D q T x Z v).2+anisotropicDisorderInjection n h) := by
  induction T generalizing x with
  | leaf=>
    simp only [treeNativePointData,cavityCouplingStartTranslation_parameter]
  | @advance j T ih=>
    rcases v with r|v
    · rfl
    · simpa only [treeNativePointData,cavityTreeRecordPathMap,Prod.map_fst,Prod.map_snd,
        Sum.elim_inr,cavityCouplingPathTranslation_endpoint] using
        ih (edgePathEndpoint D (q j) Z.1) Z.2 v
  | fork T U ihT ihU=>
    rcases v with u|v
    · simp only [treeNativePointData,Sum.elim_inl,cavityCouplingStartTranslation_parameter]
    · rcases v with v|v
      · simpa only [treeNativePointData,cavityTreeRecordPathMap,Prod.map_fst,
          Sum.elim_inr,Sum.elim_inl] using ihT x Z.1 v
      · simpa only [treeNativePointData,cavityTreeRecordPathMap,Prod.map_snd,
          Sum.elim_inr] using ihU x Z.2 v

theorem treeNativeFullPointData_coupling_translation (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) (h : AnisotropicDisorder n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (x : AnisotropicObservationState n)
    (Z : Records (NativeTreePath n) (Configuration n) T) (v : Unit⊕treePathWeightPoint T) :
    treeNativeFullPointData D q T (cavityCouplingStartTranslation h x)
      (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z) v=
      ((treeNativeFullPointData D q T x Z v).1,
        (treeNativeFullPointData D q T x Z v).2+anisotropicDisorderInjection n h) := by
  rcases v with u|v
  · simp only [treeNativeFullPointData,ContinuousMap.coe_mk,Sum.elim_inl,
      cavityCouplingStartTranslation_parameter]
  · exact treeNativePointData_coupling_translation D q h T x Z v

def treeNativeCouplingTerminalIncrement (D : AnisotropicSpinModel n)
    (h : AnisotropicDisorder n) : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
      Records (NativeTreePath n) (Configuration n) T→ℝ
  | _,.leaf=>fun σ=>anisotropicTerminalLinear D σ (anisotropicDisorderInjection n h)
  | _,.advance T=>fun Z=>treeNativeCouplingTerminalIncrement D h T Z.2
  | _,.fork T U=>fun Z=>treeNativeCouplingTerminalIncrement D h T Z.1+
      treeNativeCouplingTerminalIncrement D h U Z.2

theorem treeNativeTerminalEnergy_coupling_translation (D : AnisotropicSpinModel n)
    (q : ℕ→Paper.Overlap) (h : AnisotropicDisorder n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (x : AnisotropicObservationState n)
    (Z : Records (NativeTreePath n) (Configuration n) T) :
    treeNativeTerminalEnergy D q T (cavityCouplingStartTranslation h x)
      (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)-
      treeNativeTerminalEnergy D q T x Z=treeNativeCouplingTerminalIncrement D h T Z := by
  induction T generalizing x with
  | leaf=>
    simp only [treeNativeTerminalEnergy,cavityTreeRecordPathMap,id_eq,
      cavityCouplingStartTranslation_parameter,map_add,add_sub_cancel_left,
      treeNativeCouplingTerminalIncrement]
  | @advance j T ih=>
    simpa only [treeNativeTerminalEnergy,cavityTreeRecordPathMap,Prod.map_fst,Prod.map_snd,
      cavityCouplingPathTranslation_endpoint,treeNativeCouplingTerminalIncrement] using
      ih (edgePathEndpoint D (q j) Z.1) Z.2
  | fork T U ihT ihU=>
    simp only [treeNativeTerminalEnergy,cavityTreeRecordPathMap,Prod.map_fst,Prod.map_snd,
      treeNativeCouplingTerminalIncrement]
    linear_combination ihT x Z.1+ihU x Z.2

end HexagonPaper
