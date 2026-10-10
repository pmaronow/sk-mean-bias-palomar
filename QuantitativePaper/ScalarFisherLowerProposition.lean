module
public import QuantitativePaper.ScalarFisherUniformReduction
public import QuantitativePaper.UniformScalarRootTrialLemma
public import QuantitativePaper.UniformScalarSmoothingHessian

@[expose] public section

/-! Literal main Proposition 5.3. The window and upper-cost constant are
the same witnesses as the actual full uniform root/trial lemma; the
Fisher lower bound is applied without choosing a smaller window. -/
noncomputable section
open Set MeasureTheory Paper FRSB
namespace QuantitativePaper
set_option maxHeartbeats 1800000

def ScalarFisherLowerTarget : Prop :=
  ∀β0 : ℝ,1<β0→∃c0 C1 lamstar : ℝ,
    0<c0 ∧ 1≤C1 ∧ 0<lamstar ∧ lamstar≤1 ∧ lamstar≤β0/2 ∧
      ∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) lamstar→
        c0*lam^5≤ scalarEnergyValue β lam-scalarEnergyValue β 0 ∧
        scalarEnergyValue β lam-scalarEnergyValue β 0≤C1*lam^5

theorem scalar_fisher_lower : ScalarFisherLowerTarget := by
  intro β0 hβ0
  obtain ⟨T,k,Cs,C1,L,hT,hk,hCs,hC1,hL,hL1,hLβ,hLk,hdata⟩:=
    uniform_scalar_root_trial β0 hβ0
  obtain ⟨C2,hC2,huniform⟩:=scalarEnergy_hessian_uniform_early
  have hCspos : 0<Cs:=zero_lt_one.trans_le hCs
  have hC2pos : 0<C2:=zero_lt_one.trans_le hC2
  have hkCs : k≤Cs := by
    have hh:=(hdata β0 le_rfl (parisiMinimizer β0 0)
      (isParisiMinimizer_selected β0 0)).2.1 T ⟨hT.1.le,le_rfl⟩
    nlinarith [hh.1,hh.2,hT.1]
  have hLT : L≤Cs*T:=hLk.trans (mul_le_mul_of_nonneg_right hkCs hT.1.le)
  obtain ⟨c0,hc0,hlower⟩:=scalar_floor_fisher_lower_of_uniform_smoothing
    β0 Cs C2 T L hβ0 hCspos hC2pos hT hL hL1 hLβ hLT
    (fun β hb q hq=>((hdata β hb (parisiMinimizer β 0)
      (isParisiMinimizer_selected β 0)).2.1 q hq).2)
    (fun β hb μ hc=>huniform β (zero_lt_one.trans (hβ0.trans_le hb)) μ hc)
  refine ⟨c0,C1,L,hc0,hC1,hL,hL1,hLβ,?_⟩
  intro β hb lam hlam
  have hmin:=isParisiMinimizer_selected β 0
  obtain ⟨hs,hmem,hCDF,hroot,hdom,h0,htrial,hbound⟩:=
    (hdata β hb (parisiMinimizer β 0) hmin).2.2.2.2 lam ⟨hlam.1.le,hlam.2⟩
  exact ⟨hlower β hb lam hlam,htrial.trans hbound⟩

end QuantitativePaper
