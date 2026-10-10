module
public import QuantitativePaper.LocalExponentialJetClosure

@[expose] public section

/-! Common finite-order exponential envelopes for actual scalar kernels,
including their zeroth derivative and exponential transform. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_common_exponential_jet_envelope (N : ℕ) (f : E→ℝ) (U : Set E)
    (B L K D : ℝ) (hB : 0≤B) (hL : 0≤L) (hK : 1≤K) (hD : 0≤D)
    (hvalue : ∀ x∈U,|f x|≤B+L*‖x‖)
    (hjets : ∀ j,1≤j→j≤N→∀ x∈U,‖iteratedFDeriv ℝ j f x‖≤(K*Real.exp (D*‖x‖))^j) :
    ∃ C R : ℝ,1≤C ∧ 0≤R ∧ ∀ j,j≤N→∀ x∈U,
      ‖iteratedFDeriv ℝ j f x‖≤C*Real.exp (R*‖x‖) := by
  obtain ⟨C,R,hC,hR,hj⟩:=exists_all_order_power_envelope N f U B L K D hB hL hK hD hvalue hjets
  refine ⟨C^(N+1),(N+1:ℕ)*R,one_le_pow₀ hC,by positivity,?_⟩
  intro j hjN x hx
  apply (hj j hjN x hx).trans
  have hp : 1≤C*Real.exp (R*‖x‖):=one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_exp_iff.mpr (by positivity))
  have hh:=pow_le_pow_right₀ hp (by omega : j+1≤N+1)
  apply hh.trans_eq
  rw [mul_pow,←Real.exp_nat_mul]
  congr 1
  ring

theorem exists_exp_common_exponential_jet_envelope (N : ℕ) (f : E→ℝ)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (B L K D : ℝ) (hL : 0≤L) (hK : 0≤K) (hD : 0≤D)
    (hvalue : ∀ x∈U,f x≤B+L*‖x‖)
    (hjets : ∀ j,1≤j→j≤N→∀ x∈U,‖iteratedFDeriv ℝ j f x‖≤(K*Real.exp (D*‖x‖))^j) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ j,j≤N→∀ x∈U,
      ‖iteratedFDeriv ℝ j (fun y=>Real.exp (f y)) x‖≤C*Real.exp (R*‖x‖) := by
  let C:=∑ j∈Finset.range (N+1),(j.factorial:ℝ)*K^j*Real.exp B
  refine ⟨C,L+(N:ℝ)*D,by dsimp only [C]; positivity,by positivity,?_⟩
  intro j hjN x hx
  have hh:=norm_iteratedFDeriv_exp_le_on_open f U hU hf hjN
    (K*Real.exp (D*‖x‖)) x hx (fun i hi hij=>hjets i hi (hij.trans hjN) x hx)
  have hc:(j.factorial:ℝ)*K^j*Real.exp B≤C:=
    Finset.single_le_sum (f:=fun j=>(j.factorial:ℝ)*K^j*Real.exp B)
      (fun _ _=>by positivity) (Finset.mem_range.mpr (by omega))
  have he:f x+(j:ℝ)*D*‖x‖≤B+(L+(N:ℝ)*D)*‖x‖:=by
    have hjR:(j:ℝ)≤N:=by exact_mod_cast hjN
    have hmul:=mul_le_mul_of_nonneg_right hjR (mul_nonneg hD (norm_nonneg x))
    nlinarith [hvalue x hx]
  calc
    _≤(j.factorial:ℝ)*K^j*Real.exp (f x+(j:ℝ)*D*‖x‖):=by
      apply hh.trans_eq
      rw [mul_pow,←Real.exp_nat_mul]
      rw [show (j:ℝ)*(D*‖x‖)=(j:ℝ)*D*‖x‖ by ring,Real.exp_add]
      ring
    _≤(j.factorial:ℝ)*K^j*Real.exp (B+(L+(N:ℝ)*D)*‖x‖):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _=((j.factorial:ℝ)*K^j*Real.exp B)*Real.exp ((L+(N:ℝ)*D)*‖x‖):=by rw [Real.exp_add]; ring
    _≤C*Real.exp ((L+(N:ℝ)*D)*‖x‖):=mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

end QuantitativePaper
