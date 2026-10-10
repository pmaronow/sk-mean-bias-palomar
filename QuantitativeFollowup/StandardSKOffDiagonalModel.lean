module
public import QuantitativeFollowup.StandardSKAnisotropicModel

@[expose] public section

/-! The physical SK interpolation with no common diagonal completion
noise. Its independent upper-triangular diagonal coordinates are retained
in the sample space but have zero Hamiltonian coefficient. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 600000
variable {n : ℕ}

def standardSKOffDiagonalModel (n : ℕ) (β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) :
    AnisotropicSpinModel n where
  variance _ := (1-t)*β^2
  variance_pos _ := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  coupling e := if e.1.1=e.1.2 then 0 else β*Real.sqrt t/Real.sqrt (n:ℝ)

def standardSKOffDiagonalDisorder (ω : AnisotropicDisorder n) : Couplings n :=
  (standardSKRawDisorder ω).1

def standardSKOffDiagonalCompression (ω : AnisotropicDisorder n) : Couplings n × ℝ :=
  (standardSKOffDiagonalDisorder ω,0)

theorem measurable_standardSKOffDiagonalDisorder :
    Measurable (standardSKOffDiagonalDisorder (n:=n)) :=
  measurable_fst.comp measurable_standardSKRawDisorder

theorem measurable_standardSKOffDiagonalCompression :
    Measurable (standardSKOffDiagonalCompression (n:=n)) :=
  measurable_standardSKOffDiagonalDisorder.prodMk measurable_const

theorem anisotropicDisorderLaw_standardSKOffDiagonalDisorder (n : ℕ) :
    (anisotropicDisorderLaw n).map standardSKOffDiagonalDisorder = couplingLaw n := by
  change (anisotropicDisorderLaw n).map (Prod.fst ∘ standardSKRawDisorder) = _
  rw [←Measure.map_map measurable_fst measurable_standardSKRawDisorder,
    anisotropicDisorderLaw_standardSKRawDisorder,goeRawLaw]
  exact measurePreserving_fst.map_eq

theorem standardSKOffDiagonalHamiltonian (β t : ℝ) (hβ : β ≠ 0) (ht : t<1)
    (ω : AnisotropicDisorder n) (x : Field n) (σ : Configuration n) :
    anisotropicHamiltonian (standardSKOffDiagonalModel n β t hβ ht) ω x σ =
      vectorTerminalExponent n β t (standardSKOffDiagonalCompression ω) x σ := by
  classical
  have hs : (∑e : AnisotropicCouplingIndex n,
      (standardSKOffDiagonalModel n β t hβ ht).coupling e*ω e*
        Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)) =
      ∑e : Edge n, β*Real.sqrt t/Real.sqrt (n:ℝ)*ω ⟨e.1,e.2.le⟩*
        Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2) := by
    rw [←(standardSKCouplingEquiv n).symm.sum_comp,Fintype.sum_sum_type]
    have he : (∑i : Fin n,
        (standardSKOffDiagonalModel n β t hβ ht).coupling
          ((standardSKCouplingEquiv n).symm (Sum.inr i))*
          ω ((standardSKCouplingEquiv n).symm (Sum.inr i))*
          Paper.spinSign (σ ((standardSKCouplingEquiv n).symm (Sum.inr i)).1.1)*
          Paper.spinSign (σ ((standardSKCouplingEquiv n).symm (Sum.inr i)).1.2))=0 := by
      simp [standardSKCouplingEquiv,standardSKOffDiagonalModel]
    rw [he,add_zero]
    apply Finset.sum_congr rfl
    intro e _
    simp only [standardSKCouplingEquiv,Equiv.coe_fn_symm_mk,standardSKOffDiagonalModel,
      ne_of_lt e.2,ite_false]
  rw [anisotropicHamiltonian,hs]
  simp only [vectorTerminalExponent,standardSKOffDiagonalCompression,
    standardSKOffDiagonalDisorder,standardSKRawDisorder,energy,Paper.skHamiltonian,
    mul_zero,zero_mul,Finset.sum_const_zero,add_zero,mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

end QuantitativeFollowup
