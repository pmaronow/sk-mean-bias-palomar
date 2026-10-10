module
public import QuantitativeFollowup.LocalizationFamilyCoercivity

@[expose] public section

/-! Genuine four-case layer-cake coercivity with explicit smooth test
families. This deterministic lemma is instantiated by actual diffusion
signal and denominator estimates in the model-facing result. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
namespace QuantitativeFollowup
set_option maxHeartbeats 3200000

theorem localization_coercivity_of_smooth_families (psi : ℝ→ℝ) (hpsi : Measurable psi)
    (q beta L k rho h D F : ℝ) (hq : q∈Ioo (0 : ℝ) 1)
    (hb : 0<beta) (hL : 1≤L) (hk : 0<k) (hr : 0<rho) (hh : 0<h)
    (hD : 0≤D) (hF : 0≤F) (hroot : psi 0≤0)
    (hslope : ∀z x : ℝ,0≤z→z≤x→x<q→psi x-psi z≤L*(x-z))
    (hanti : AntitoneOn psi (Icc q 1))
    (hpost : ∀x∈Icc q 1,0≤psi x)
    (hbound : ∀x∈Icc (0 : ℝ) 1,|psi x|≤beta)
    (hbudget : D/2≤∫x in (0 : ℝ)..1,|psi x|)
    (hfamilies : ∀A : ℝ,0<A→∀S : Finset ℕ,S.Nonempty→∀a : ℕ→ℝ,∀ell : ℝ,0<ell→
      (S:Set ℕ).PairwiseDisjoint (fun i=>Ioo (a i) (a i+ell))→
      (∀i∈S,Icc (a i) (a i+ell)⊆Ioo (0 : ℝ) q ∨
        Icc (a i) (a i+ell)⊆Ioo q 1)→
      ∀sigma : ℝ,sigma^2=1→
      (∀i∈S,∀x∈Icc (a i) (a i+ell),A/2 ≤ sigma*psi x)→
      smoothFamilyCoefficient beta rho h k A (S.card : ℝ) ell≤F) :
    smoothLocalizationConstant beta L k*(1/8 : ℝ)^4*localizationCaseConstant beta L*
      rho^2*min (rho*D^4) (h*D^2) ≤ F := by
  let c := smoothLocalizationConstant beta L k
  let K := F/(c*rho^2)
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hc : 0<c := smoothLocalizationConstant_pos beta L k hb hLp hk
  have hK : 0≤K := div_nonneg hF (by positivity)
  have hInterior (j : Fin 4) (hj : j=0 ∨ j=1) :
      ∀A : ℝ,0<A→A^2*localizationLevelMass psi q L A j*min (rho*A^2) h≤K := by
    intro A hA
    let ell := A/(4*L)
    have hell : 0<ell := by dsimp only [ell]; positivity
    obtain ⟨S,a,hm,hdisj,hinside,sigma,hsigma,hSign⟩ :
        ∃S : Finset ℕ,∃a : ℕ→ℝ,
          localizationLevelMass psi q L A j≤(S.card : ℝ)*ell ∧
          (S:Set ℕ).PairwiseDisjoint (fun i=>Ioo (a i) (a i+ell)) ∧
          (∀i∈S,Icc (a i) (a i+ell)⊆Ioo (0 : ℝ) q) ∧
          ∃sigma : ℝ,sigma^2=1 ∧
            ∀i∈S,∀x∈Icc (a i) (a i+ell),A/2 ≤ sigma*psi x := by
      rcases hj with rfl|rfl
      · obtain ⟨hm,hd,hi,hs,hc,ht⟩ := positive_localization_family psi q L A hLp hA hroot hslope
        exact ⟨_,_,hm,hd,hi,1,by norm_num,by simpa only [one_mul] using hs⟩
      · obtain ⟨hm,hd,hi,hs,hc,ht⟩ := negative_localization_family psi q L A hLp hA hslope
        exact ⟨_,_,hm,hd,hi,-1,by norm_num,by intro i hi x hx; linarith [hs i hi x hx]⟩
    by_cases hS : S.Nonempty
    · have hNb : (0 : ℝ)<S.card := by exact_mod_cast Finset.card_pos.mpr hS
      have hfamily := hfamilies A hA S hS a ell hell hdisj
        (fun i hi=>Or.inl (hinside i hi)) sigma hsigma hSign
      have hlo := smoothFamilyCoefficient_interior_lower beta L k rho h A (S.card : ℝ)
        hb hLp hk.le hr hh hA hNb
      have hmul := mul_le_mul_of_nonneg_left hm
        (by positivity : 0≤c*rho^2*A^2*min (rho*A^2) h)
      apply (le_div_iff₀ (by positivity : 0<c*rho^2)).mpr
      have hlo' : c*rho^2*A^2*((S.card : ℝ)*ell)*min (rho*A^2) h ≤ F := by
        convert hlo.trans hfamily using 1
        dsimp only [c,ell]
        ring
      nlinarith only [hmul,hlo']
    · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hm0 : localizationLevelMass psi q L A j=0 := by
        have hmN := (localizationLevelMass_nonneg_le_one psi q L A hq hLp hA j).1
        simp only [he,Finset.card_empty,Nat.cast_zero,zero_mul] at hm
        linarith
      rw [hm0,mul_zero,zero_mul]
      exact hK
  have hBoundary (j : Fin 4) (hj : j=2 ∨ j=3) :
      ∀A : ℝ,0<A→∃w : ℝ,0≤w ∧ localizationLevelMass psi q L A j≤w ∧
        w≤(if j=2 then A/(2*L) else 1) ∧ A^2*w*min (rho*w^2) h≤K := by
    intro A hA
    by_cases hm : 0<localizationLevelMass psi q L A j
    · have hExists :
        ∃a b : ℝ,a<b ∧ 0≤a ∧ b≤1 ∧ localizationLevelMass psi q L A j≤b-a ∧
          b-a≤(if j=2 then A/(2*L) else 1) ∧
          ∃sigma : ℝ,sigma^2=1 ∧
            (Ioo a b⊆Ioo (0 : ℝ) q ∨ Ioo a b⊆Ioo q 1) ∧
            ∀x∈Ioo a b,A/2 ≤ sigma*psi x := by
        rcases hj with rfl|rfl
        · have hne : {x : ℝ|x∈Ioo (0 : ℝ) q ∧ q-A/(2*L)≤x ∧ psi x< -A}.Nonempty := by
            by_contra hn
            have hz := Set.not_nonempty_iff_eq_empty.mp hn
            change 0<volume.real {x : ℝ|x∈Ioo (0 : ℝ) q ∧ q-A/(2*L)≤x ∧ psi x< -A} at hm
            rw [hz,measureReal_empty] at hm
            exact (lt_irrefl (0 : ℝ)) hm
          obtain ⟨a,ha,hsub,hwidth,hcap,hsign⟩ := one_sided_negative_boundary_interval psi q L A hLp hA hslope hne
          refine ⟨a,q,ha.2,ha.1,hq.2.le,?_,by simpa using hcap,-1,by norm_num,Or.inl ?_,?_⟩
          · simpa [localizationLevelMass,localizationLevelSet] using hwidth
          · intro x hx; exact ⟨ha.1.trans_lt hx.1,hx.2⟩
          · intro x hx; linarith [hsign x hx]
        · have hne : {x : ℝ|x∈Icc q 1 ∧ A<psi x}.Nonempty := by
            by_contra hn
            have hz := Set.not_nonempty_iff_eq_empty.mp hn
            change 0<volume.real {x : ℝ|x∈Icc q 1 ∧ A<psi x} at hm
            rw [hz,measureReal_empty] at hm
            exact (lt_irrefl (0 : ℝ)) hm
          obtain ⟨b,hb,hsub,hwidth,hsign⟩ := antitone_positive_boundary_interval psi q A hanti hne
          have hqb : q<b := by
            have he : localizationLevelMass psi q L A 3=b-q := by
              simpa [localizationLevelMass,localizationLevelSet] using hwidth
            linarith only [hm,he]
          refine ⟨q,b,hqb,hq.1.le,hb.2,?_,?_,1,by norm_num,Or.inr ?_,?_⟩
          · simpa [localizationLevelMass,localizationLevelSet] using hwidth.le
          · simpa using (by linarith [hb.2,hq.1] : b-q≤1)
          · intro x hx; exact ⟨hx.1,hx.2.trans_le hb.2⟩
          · intro x hx; simpa only [one_mul] using (by linarith [hsign x hx] : A/2≤psi x)
      obtain ⟨a,b,hab,ha,hb1,hmw,hwcap,sigma,hsigma,hSign⟩ := hExists
      let S : Finset ℕ := {0}
      let start : ℕ→ℝ := fun _=>a+(b-a)/4
      let ell := (b-a)/2
      have hell : 0<ell := half_pos (sub_pos.mpr hab)
      have hdisj : (S:Set ℕ).PairwiseDisjoint (fun i=>Ioo (start i) (start i+ell)) := by
        simp only [S,Finset.coe_singleton]
        exact Set.pairwiseDisjoint_singleton _ _
      have hinside : ∀i∈S,Icc (start i) (start i+ell)⊆Ioo (0 : ℝ) q ∨
          Icc (start i) (start i+ell)⊆Ioo q 1 := by
        intro i hi
        have hsub : Icc (start i) (start i+ell)⊆Ioo a b := by
          intro x hx
          dsimp only [start,ell] at hx
          constructor <;> linarith [hx.1,hx.2]
        rcases hSign.1 with hs|hs
        · exact Or.inl (hsub.trans hs)
        · exact Or.inr (hsub.trans hs)
      have hfamily := hfamilies A hA S (by simp [S]) start ell hell hdisj hinside sigma hsigma (by
        intro i hi x hx
        apply hSign.2 x
        dsimp only [start,ell] at hx
        constructor <;> linarith [hx.1,hx.2])
      have hlo := smoothFamilyCoefficient_boundary_lower beta L k rho h A (b-a)
        hb hL hk.le hr hh hA (sub_pos.mpr hab)
      have hcurv : A^2*(b-a)*min (rho*(b-a)^2) h≤K := by
        apply (le_div_iff₀ (by positivity : 0<c*rho^2)).mpr
        have hhF : c*rho^2*A^2*(b-a)*min (rho*(b-a)^2) h≤F := by
          refine hlo.trans ?_
          simpa only [S,Finset.card_singleton,Nat.cast_one,start,ell] using hfamily
        nlinarith only [hhF]
      exact ⟨b-a,(sub_pos.mpr hab).le,hmw,hwcap,hcurv⟩
    · have hm0 : localizationLevelMass psi q L A j=0 :=
        le_antisymm (le_of_not_gt hm) (localizationLevelMass_nonneg_le_one psi q L A hq hLp hA j).1
      refine ⟨0,le_rfl,hm0.le,?_,?_⟩
      · split_ifs <;> positivity
      · simpa only [mul_zero,zero_mul] using hK
  have hCases (j : Fin 4) := localization_interior_integral_bound_of_curvature psi hpsi q L beta
    hq hLp hb hbound j K rho h hK hr hh
  have hLower := localization_curvature_bound_of_piece_cases psi hpsi q L beta D K rho h
    hq hLp hb hD hK hr hh hbound hpost hbudget (by
      intro j
      fin_cases j
      · exact Or.inl (hCases 0 (hInterior 0 (Or.inl rfl)))
      · exact Or.inl (hCases 1 (hInterior 1 (Or.inr rfl)))
      · exact Or.inr (Or.inl (localization_negative_boundary_integral_bound_of_width_curvature psi hpsi
          q L beta hq hLp hb hbound K rho h hK hr hh (by
            intro A hA
            simpa only [Fin.isValue,ite_true] using hBoundary 2 (Or.inl rfl) A hA)))
      · exact Or.inr (Or.inr (localization_post_boundary_integral_bound_of_width_curvature psi hpsi
          q L beta hq hLp hb hbound K rho h hK hr hh (by
            intro A hA
            simpa using hBoundary 3 (Or.inr rfl) A hA))))
  have hhFinal := (le_div_iff₀ (by positivity : 0<c*rho^2)).mp hLower
  convert hhFinal using 1
  dsimp only [c]
  ring

end QuantitativeFollowup
