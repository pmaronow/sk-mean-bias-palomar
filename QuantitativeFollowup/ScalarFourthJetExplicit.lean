module
public import QuantitativeFollowup.ScalarFourthJetBound

@[expose] public section

/-! An explicit, measure-uniform fourth jet bound. -/
noncomputable section
open Set Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FRSB
set_option maxHeartbeats 1000000

theorem weightedFourthJet_contraction (beta : ℝ) (hb : beta≠0)
    (μ : Paper.ParisiMeasure) :
    weightedFourthJet beta μ (8*beta^2)≤10+588*beta^2+
      weightedFourthJet beta μ (8*beta^2)/2 := by
  let K := 8*beta^2
  let S := weightedFourthJet beta μ K
  have hb2 : 0<beta^2 := sq_pos_of_ne_zero hb
  have hK : 0<K := by dsimp only [K];positivity
  change S≤10+588*beta^2+S/2
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p,rfl⟩
  let a : ℝ := p.1
  have ha : a∈Icc (0 : ℝ) 1 := p.1.property
  have hh := fourthJet_weighted_restart_bound beta hb μ K hK a p.2 ha
  have hw := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-K*(1-a))).le
  have he : Real.exp (-K*(1-a))*Real.exp (K*(1-a))=1 := by
    rw [←Real.exp_add];simp
  have hratio : 4*beta^2/K=(1/2:ℝ) := by
    dsimp only [K]
    field_simp
    norm_num
  have hident : Real.exp (-K*(1-a))*(10+588*beta^2+(4*beta^2/K)*S*Real.exp (K*(1-a)))=
      (10+588*beta^2)*Real.exp (-K*(1-a))+S/2 := by
    rw [hratio]
    calc
      _=(10+588*beta^2)*Real.exp (-K*(1-a))+S/2*
        (Real.exp (-K*(1-a))*Real.exp (K*(1-a))) := by ring
      _=_ := by rw [he,mul_one]
  have he1 : Real.exp (-K*(1-a))≤1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hK.le,ha.2])
  change Real.exp (-K*(1-a))*‖parisiSpatialJet beta μ 4 a p.2‖≤_
  exact hw.trans (hident.le.trans (add_le_add
    (mul_le_of_le_one_right (by positivity) he1) le_rfl))

def scalarFourthJetBound (beta : ℝ) : ℝ := (20+1176*beta^2)*Real.exp (8*beta^2)

theorem scalarFourthJetBound_pos (beta : ℝ) : 0<scalarFourthJetBound beta := by
  unfold scalarFourthJetBound
  positivity

theorem norm_parisiSpatialJet_four_le (beta : ℝ) (hb : beta≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiSpatialJet beta μ 4 a x‖≤ scalarFourthJetBound beta := by
  let K := 8*beta^2
  have hK : 0≤K := by dsimp only [K];positivity
  have hs := weightedFourthJet_contraction beta hb μ
  have hS : weightedFourthJet beta μ K≤20+1176*beta^2 := by
    change weightedFourthJet beta μ K≤10+588*beta^2+weightedFourthJet beta μ K/2 at hs
    linarith
  have he : Real.exp (K*(1-a))≤Real.exp K := Real.exp_le_exp.mpr (by nlinarith [ha.1])
  exact (fourthJet_le_weightedFourthJet beta μ K hK a ha x).trans
    (by simpa only [scalarFourthJetBound,K] using mul_le_mul hS he (Real.exp_pos _).le (by positivity))

theorem scalarFourthJetBound_le_of_sq_le (beta gamma : ℝ) (h : gamma^2≤beta^2) :
    scalarFourthJetBound gamma≤ scalarFourthJetBound beta := by
  apply mul_le_mul
  · nlinarith
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · exact (Real.exp_pos _).le
  · positivity

end QuantitativeFollowup
