module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterStieltjes
public import QuantitativePaper.VectorProfileMeasure
public import QuantitativeFollowup.AnisotropicFiniteCascade
public import FRSB.FiniteForwardAction

@[expose] public section

/-! The complete outer posterior's raw charges integrate against the actual
finite free overlap measure. Its dummy zero-root charge is negative when the
outer mass is positive; it is merged with the true atom at q1=0 here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def cavityOuterSchemeChargeNode (s : RSBScheme k) : Option (Option (Fin (k+1)))→Paper.Overlap
  | none=>(1:Paper.Overlap)
  | some none=>(0:Paper.Overlap)
  | some (some i)=>Paper.parisiSchemeAtom s i

theorem cavityOuterSchemeWeight_atom (s : RSBScheme k) (a : ℝ) (i : Fin (k+1)) :
    cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) (some (some i))=
      s.m (i+1)-s.m i :=by
  dsimp only [cavityOuterStieltjesWeight,anisotropicSchemeMass]
  rw [show k+1-(k+1-(i+1))=i+1 by have hi:=i.isLt;omega,
    show k+1-(k+1-i)=i by have hi:=i.isLt;omega]

theorem cavityOuterSchemeCharge_sum_eq_scheme_minus_root (s : RSBScheme k) (a : ℝ)
    (F : Paper.Overlap→ℝ) :
    (∑i,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i*
      F (cavityOuterSchemeChargeNode s i))=
      (∫r,F r ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))-a*F (0:Paper.Overlap) :=by
  rw [Fintype.sum_option,Fintype.sum_option]
  simp only [cavityOuterStieltjesWeight,anisotropicSchemeMass,cavityOuterSchemeChargeNode,
    Nat.sub_zero,Nat.sub_self,s.m_top,s.m_zero,sub_self,zero_mul,zero_add,zero_sub]
  rw [FRSB.integral_parisiSchemeMeasure]
  have hw : (∑i : Fin (k+1),
      (s.m (k+1-(k+1-(i+1)))-s.m (k+1-(k+1-i)))*F (Paper.parisiSchemeAtom s i))=
      ∑i : Fin (k+1),(s.m (i+1)-s.m i)*F (Paper.parisiSchemeAtom s i) :=by
    apply Finset.sum_congr rfl
    intro i _
    rw [show k+1-(k+1-(i+1))=i+1 by have hi:=i.isLt;omega,
      show k+1-(k+1-i)=i by have hi:=i.isLt;omega]
  rw [hw]
  ring

theorem cavityOuterSchemeCharge_sum_eq_actual_free (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (F : Paper.Overlap→ℝ) :
    (∑i,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i*
      F (cavityOuterSchemeChargeNode s i))=
      ∫r,F r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  rw [cavityOuterSchemeCharge_sum_eq_scheme_minus_root]
  have hI : Integrable F (ENNReal.ofReal a • Measure.dirac zeroOverlap):=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have hF:=integrable_vectorProfileFreeMeasure s a F
  rw [←vectorProfile_free_root_decomposition s a ha has hq,
    integral_add_measure hI hF,integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal ha,
    smul_eq_mul,vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
  have hz : zeroOverlap=(0:Paper.Overlap):=by apply Subtype.ext;rfl
  rw [hz]
  ring

end QuantitativeFollowup
