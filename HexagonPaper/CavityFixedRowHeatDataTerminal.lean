module
public import HexagonPaper.CavityCouplingTreeActionBasic
public import HexagonPaper.CavityFixedRowMixtureNative

@[expose] public section

/-! Genuine terminal linear maps of the retained finite path tree, with
uniform bounds over all leaf spin configurations. -/
noncomputable section
open Set MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped Topology BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n m : ℕ}

def cavityTreeTerminalIncrementLinear (D : AnisotropicSpinModel n)
    (L : Field m→L[ℝ]AnisotropicParameter n) : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
      Records (NativeTreePath n) (Configuration n) T→Field m→L[ℝ]ℝ
  | _,.leaf=>fun σ=>(anisotropicTerminalLinear D σ).comp L
  | _,.advance T=>fun Z=>cavityTreeTerminalIncrementLinear D L T Z.2
  | _,.fork T U=>fun Z=>cavityTreeTerminalIncrementLinear D L T Z.1+
      cavityTreeTerminalIncrementLinear D L U Z.2

def cavityTreeTerminalIncrementBound (D : AnisotropicSpinModel n)
    (L : Field m→L[ℝ]AnisotropicParameter n) {j : ℕ} (T : FiniteTerminalGenealogy j) : ℝ :=
  (FiniteCascadeGenealogy.leafCount T.asGenealogy : ℝ)*
    ∑σ:Configuration n,‖(anisotropicTerminalLinear D σ).comp L‖

 theorem cavityTreeTerminalIncrementBound_nonneg (D : AnisotropicSpinModel n)
    (L : Field m→L[ℝ]AnisotropicParameter n) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    0≤cavityTreeTerminalIncrementBound D L T := by
  unfold cavityTreeTerminalIncrementBound
  positivity

 theorem cavityTreeTerminalIncrementLinear_norm_le (D : AnisotropicSpinModel n)
    (L : Field m→L[ℝ]AnisotropicParameter n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Z : Records (NativeTreePath n) (Configuration n) T) :
    ‖cavityTreeTerminalIncrementLinear D L T Z‖≤cavityTreeTerminalIncrementBound D L T := by
  classical
  induction T with
  | leaf=>
    simp only [cavityTreeTerminalIncrementLinear,cavityTreeTerminalIncrementBound,asGenealogy,
      FiniteCascadeGenealogy.leafCount,Nat.cast_one,one_mul]
    exact Finset.single_le_sum
      (f:=fun σ : Configuration n=>‖(anisotropicTerminalLinear D σ).comp L‖)
      (fun σ _=>norm_nonneg ((anisotropicTerminalLinear D σ).comp L)) (Finset.mem_univ Z)
  | advance T ih=>exact ih Z.2
  | fork T U ihT ihU=>
    apply (cavityTreeTerminalIncrementLinear D L (.fork T U) Z).opNorm_le_bound
      (cavityTreeTerminalIncrementBound_nonneg D L _)
    intro θ
    change ‖cavityTreeTerminalIncrementLinear D L T Z.1 θ+cavityTreeTerminalIncrementLinear D L U Z.2 θ‖≤_
    apply (norm_add_le _ _).trans
    have hT:=((cavityTreeTerminalIncrementLinear D L T Z.1).le_opNorm θ).trans
      (mul_le_mul_of_nonneg_right (ihT Z.1) (norm_nonneg θ))
    have hU:=((cavityTreeTerminalIncrementLinear D L U Z.2).le_opNorm θ).trans
      (mul_le_mul_of_nonneg_right (ihU Z.2) (norm_nonneg θ))
    have he : cavityTreeTerminalIncrementBound D L (.fork T U)=
        cavityTreeTerminalIncrementBound D L T+cavityTreeTerminalIncrementBound D L U:=by
      simp only [cavityTreeTerminalIncrementBound,asGenealogy,FiniteCascadeGenealogy.leafCount,Nat.cast_add]
      ring
    rw [he,add_mul]
    exact add_le_add hT hU

 theorem cavityTreeTerminalIncrementLinear_eq_native (D : AnisotropicSpinModel n)
    (H : Field m→L[ℝ]AnisotropicDisorder n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Z : Records (NativeTreePath n) (Configuration n) T) (θ : Field m) :
    cavityTreeTerminalIncrementLinear D ((anisotropicDisorderInjection n).comp H) T Z θ=
      treeNativeCouplingTerminalIncrement D (H θ) T Z := by
  induction T with
  | leaf=>rfl
  | advance T ih=>exact ih Z.2
  | fork T U ihT ihU=>exact congrArg₂ (·+·) (ihT Z.1) (ihU Z.2)

end HexagonPaper
