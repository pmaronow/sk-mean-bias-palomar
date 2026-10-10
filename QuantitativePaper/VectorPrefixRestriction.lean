module
public import QuantitativePaper.VectorIncidentEnergy

@[expose] public section

/-! Genuine restriction of the independent Gaussian prefix. Its site block
is a contraction, and each earlier actual state equals the terminal state
of the corresponding restricted prefix. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

theorem independentHistory_at_prefix {State Noise : Type*}
    (u : ℕ → State → Noise → State) (N : ℕ) (p : State × (Fin N → Noise))
    (M : ℕ) (hM : M ≤ N) :
    independentHistory u N p ⟨M,by omega⟩ =
      independentHistory u M (p.1,fun j => p.2 (Fin.castLE hM j)) (Fin.last M) := by
  induction N generalizing M with
  | zero =>
    have he : M=0 := by omega
    subst M
    rfl
  | succ N ih =>
    by_cases he : M=N+1
    · subst M
      congr 2
    · have hMN : M≤N := by omega
      have hi : (⟨M,by omega⟩ : Fin (N+2)) = (⟨M,by omega⟩ : Fin (N+1)).castSucc :=
        Fin.ext rfl
      rw [hi]
      simp only [independentHistory,Fin.snoc_castSucc]
      rw [ih (p.1,fun j => p.2 j.castSucc) M hMN]
      congr 2

def siteGaussianPrefixEmbedding {n N M : ℕ} (i : Fin n) (hM : M ≤ N) :
    SiteGaussianIndex (N:=M) i ↪ SiteGaussianIndex (N:=N) i where
  toFun a := by
    rcases a with ⟨a,ha⟩
    rcases a with a | j
    · refine ⟨.inl a,?_⟩
      cases a <;> exact ha
    · exact ⟨.inr (Fin.castLE hM j.1,j.2),ha⟩
  inj' a b := by
    rcases a with ⟨a,ha⟩
    rcases b with ⟨b,hb⟩
    intro he
    apply Subtype.ext
    rcases a with a | j <;> rcases b with b | l
    · have hh := congrArg (fun z : SiteGaussianIndex (N:=N) i => z.val) he
      exact congrArg Sum.inl (Sum.inl.inj hh)
    · have hh : (Sum.inl a : VectorPrefixGaussianIndex n N) =
          Sum.inr (Fin.castLE hM l.1,l.2) :=
        congrArg (fun z : SiteGaussianIndex (N:=N) i => z.val) he
      cases hh
    · have hh : (Sum.inr (Fin.castLE hM j.1,j.2) : VectorPrefixGaussianIndex n N) =
          Sum.inl b := congrArg (fun z : SiteGaussianIndex (N:=N) i => z.val) he
      cases hh
    · have hj := Sum.inr.inj (congrArg (fun z : SiteGaussianIndex (N:=N) i => z.val) he)
      have h1 : j.1=l.1 := Fin.ext (congrArg (fun z : Fin N × Fin n => z.1.val) hj)
      have h2 := congrArg Prod.snd hj
      exact congrArg Sum.inr (Prod.ext h1 h2)

def siteGaussianPrefixRestriction {n N M : ℕ} (i : Fin n) (hM : M ≤ N) :
    EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i) →L[ℝ]
      EuclideanSpace ℝ (SiteGaussianIndex (N:=M) i) :=
  LinearMap.toContinuousLinearMap
    {toFun := fun g => WithLp.toLp 2 (fun a => g (siteGaussianPrefixEmbedding i hM a))
     map_add' := by intro g h;ext a;rfl
     map_smul' := by intro c g;ext a;rfl}

theorem norm_siteGaussianPrefixRestriction_le {n N M : ℕ} (i : Fin n) (hM : M ≤ N)
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    ‖siteGaussianPrefixRestriction i hM g‖ ≤ ‖g‖ := by
  have hs : ‖siteGaussianPrefixRestriction i hM g‖^2 ≤ ‖g‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    change (∑ a : SiteGaussianIndex (N:=M) i, (g (siteGaussianPrefixEmbedding i hM a))^2) ≤ _
    calc
      _ = ∑ a ∈ Finset.univ.map (siteGaussianPrefixEmbedding i hM), (g a)^2 := by
        rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => sq_nonneg (g a))
  nlinarith [norm_nonneg g,norm_nonneg (siteGaussianPrefixRestriction i hM g)]

theorem sitePrefixGaussianState_at_prefix {n k N M : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : Fin n) (hM : M ≤ N)
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    sitePrefixGaussianState s β t i 0 ⟨M,by omega⟩ g =
      sitePrefixGaussianState s β t i 0 (Fin.last M)
        (siteGaussianPrefixRestriction i hM g) := by
  simp only [sitePrefixGaussianState,vectorPrefixEuclideanHistory_apply,vectorPrefixHistory]
  rw [independentHistory_at_prefix _ N _ M hM]
  apply congrArg (fun p => independentHistory (vectorCoordinateUpdate s β t) M p (Fin.last M))
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · funext e
        rfl
      · rfl
    · rfl
  · funext j
    ext l
    rfl

theorem siteTerminalEnergy_at_prefix_bound {n k N M : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 ≤ β) (ht : t ∈ Icc 0 1) (hN : N ≤ k+2)
    (i : Fin n) (hM : M ≤ N) (σ : Configuration n)
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    |vectorTerminalExponent n β t
      (sitePrefixGaussianState s β t i 0 ⟨M,by omega⟩ g).1
      (sitePrefixGaussianState s β t i 0 ⟨M,by omega⟩ g).2 σ| ≤ β*‖g‖ := by
  rw [sitePrefixGaussianState_at_prefix s β t i hM]
  exact (siteTerminalEnergy_bound s β t hβ ht (hM.trans hN) i σ _).trans
    (mul_le_mul_of_nonneg_left (norm_siteGaussianPrefixRestriction_le i hM g) hβ)

end QuantitativePaper
