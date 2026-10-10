module
public import QuantitativeFollowup.FollowupCavitySelectedPathMask
public import QuantitativeFollowup.FollowupCavityIncidentRow
public import QuantitativeFollowup.FollowupCavityParameters

@[expose] public section

/-! The incident row is a distinct block of the actual root Gaussian
coordinates. Scaling that block leaves every auxiliary increment unchanged.
The physical row interpolation is identified with these concrete scales. -/
noncomputable section
open Set
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def anisotropicScaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) : AnisotropicSpinModel n where
  variance:=D.variance
  variance_pos:=D.variance_pos
  coupling e:=if p e then Real.sqrt u*D.coupling e else D.coupling e

theorem cavityFiniteEnergyInput_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (j : ℕ) :
    cavityFiniteEnergyInput (anisotropicScaleRootCouplings D p u) s j=cavityFiniteEnergyInput D s j := by
  apply finiteStateCLM_eq_of_single
  intro i
  ext σ
  simp only [cavityFiniteEnergyInput_single,anisotropicScaleRootCouplings]

theorem anisotropicRootEnergyMap_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) :
    anisotropicRootEnergyMap (anisotropicScaleRootCouplings D p u)=
      (anisotropicRootEnergyMap D).comp (gaussianSelectedScale p u) := by
  apply finiteStateCLM_eq_of_single
  intro e
  ext σ
  rw [ContinuousLinearMap.comp_apply]
  have hs : gaussianSelectedScale p u (EuclideanSpace.single e 1)=
      (if p e then Real.sqrt u else 1) • EuclideanSpace.single e 1 := by
    ext f
    by_cases hf:f=e
    · subst f
      by_cases hp:p e=true <;> simp [gaussianSelectedScale_apply,PiLp.smul_apply,smul_eq_mul,PiLp.single_apply,hp]
    · by_cases hp:p e=true <;> simp [gaussianSelectedScale_apply,PiLp.smul_apply,smul_eq_mul,PiLp.single_apply,hp,hf]
  rw [hs,map_smul]
  simp only [PiLp.smul_apply,smul_eq_mul,anisotropicRootEnergyMap_single,anisotropicScaleRootCouplings]
  split <;> simp_all only [mul_assoc,one_mul]

def cavityIncidentRootMask (n : ℕ) (e : AnisotropicCouplingIndex (n+1)) : Bool:=
  decide (e.1.2=Fin.last n)

def cavityIncidentGaussianMask (n : ℕ) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    AnisotropicCouplingIndex (n+1)⊕GaussianCoordinateIndex (Fin (n+1)) T→Bool:=
  Sum.elim (cavityIncidentRootMask n) (fun _=>false)

theorem cavityIncidentGaussianMask_disjoint_path (n : ℕ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (e : AnisotropicCouplingIndex (n+1)⊕GaussianCoordinateIndex (Fin (n+1)) T) :
    ¬(cavityIncidentGaussianMask n T e=true ∧ cavitySelectedRootPathMask (Fin.last n) T e=true) := by
  cases e <;> simp [cavityIncidentGaussianMask,cavitySelectedRootPathMask]

theorem followupCavityRowCoupling_scale (n : ℕ) (β ρ u : ℝ) (hρ : ρ≤1) :
    followupCavityRowCoupling n β ρ u=Real.sqrt u*followupCavityRowCoupling n β ρ 1 := by
  have hα : 0≤followupCavityAlpha n β ρ/(n:ℝ):=
    div_nonneg (followupCavityAlpha_nonneg n β ρ hρ) (Nat.cast_nonneg n)
  unfold followupCavityRowCoupling
  rw [show followupCavityAlpha n β ρ*u/(n:ℝ)=(followupCavityAlpha n β ρ/(n:ℝ))*u by ring,
    Real.sqrt_mul hα]
  simp only [mul_one]
  ring

private theorem model_eq_of_parameters {m : ℕ} (D E : AnisotropicSpinModel m)
    (hv : D.variance=E.variance) (hc : D.coupling=E.coupling) : D=E := by
  cases D
  cases E
  cases hv
  cases hc
  rfl

theorem followupCavitySpinModel_eq_scaled_root_and_path (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc 0 1) (u : ℝ) (hu : u∈Icc 0 1) :
    followupCavitySpinModel n β ρ hβ hρ u hu=
      anisotropicReplaceVariance
        (anisotropicScaleRootCouplings
          (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
          (cavityIncidentRootMask n) u)
        (Fin.last n) (followupCavityB n β ρ u) := by
  have hb : 0<followupCavityB n β ρ u:=
    (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le (followupCavityB_window n β ρ u hρ.2 hu).1
  apply model_eq_of_parameters
  · funext i
    rw [anisotropicReplaceVariance_variance _ _ i _ hb]
    by_cases hi:i=Fin.last n
    · simp [followupCavitySpinModel,hi]
    · simp [followupCavitySpinModel,anisotropicScaleRootCouplings,hi]
  · funext e
    change (if e.1.1=e.1.2 then 0 else if e.1.2=Fin.last n then
      followupCavityRowCoupling n β ρ u else followupCavityRestCoupling n β ρ)=
        if cavityIncidentRootMask n e then Real.sqrt u*
          (if e.1.1=e.1.2 then 0 else if e.1.2=Fin.last n then
            followupCavityRowCoupling n β ρ 1 else followupCavityRestCoupling n β ρ)
        else if e.1.1=e.1.2 then 0 else if e.1.2=Fin.last n then
          followupCavityRowCoupling n β ρ 1 else followupCavityRestCoupling n β ρ
    by_cases hd:e.1.1=e.1.2
    · simp [hd,cavityIncidentRootMask]
    · by_cases he:e.1.2=Fin.last n
      · have hfirst:e.1.1≠Fin.last n:=by simpa only [he] using hd
        simp only [he,hfirst,ite_false,ite_true,cavityIncidentRootMask,decide_true]
        exact followupCavityRowCoupling_scale n β ρ u hρ.2
      · simp [hd,he,cavityIncidentRootMask]

end QuantitativeFollowup
