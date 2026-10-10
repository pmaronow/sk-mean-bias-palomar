module
public import HexagonPaper.PathHeatSignedGenerators
public import HexagonPaper.PathHeatTreeMovingLimits
public import HexagonPaper.PathHeatTreeBernsteinContraction

@[expose] public section

/-! Total-variation continuity of the actual signed generators. The
covariance kernel may move simultaneously with the parameter and path;
the derivative measures and every atom are kept unchanged. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]

theorem tendsto_signedTV_add {A : Type*} {l : Filter A}
    (S T : A→SignedMeasure X) (U V : SignedMeasure X)
    (hS : Tendsto (fun i=>signedTV (S i-U)) l (𝓝 0))
    (hT : Tendsto (fun i=>signedTV (T i-V)) l (𝓝 0)) :
    Tendsto (fun i=>signedTV (S i+T i-(U+V))) l (𝓝 0) := by
  apply squeeze_zero (fun _=>ENNReal.toReal_nonneg) (fun i=>?_) (by
    simpa only [zero_add] using hS.add hT)
  have he : S i+T i-(U+V)=(S i-U)+(T i-V) := by abel
  rw [he]
  exact signedTV_add_le _ _

theorem pathHeatDensityDerivativeMeasure_TV_bound
    (S : SignedMeasure X) (M : SignedMeasure (X×X))
    (s m : ℝ) (hs : 0 ≤ s) (hS : signedTV S≤ s) (hM : signedTV M≤ m) :
    signedTV (pathHeatDensityDerivativeMeasure S M)≤ m+s*s := by
  exact (signedTV_add_le _ _).trans (add_le_add hM
    ((signedTV_pathHeatSignedTensor_le S S).trans
      (mul_le_mul hS hS ENNReal.toReal_nonneg hs)))

theorem pathHeatObservableDerivativeMeasure_TV_bound
    (S P : SignedMeasure X) (Q : SignedMeasure (X×X))
    (s p q : ℝ) (hs : 0 ≤ s) (hp : 0 ≤ p)
    (hS : signedTV S≤ s) (hP : signedTV P≤ p) (hQ : signedTV Q≤ q) :
    signedTV (pathHeatObservableDerivativeMeasure S P Q)≤ q+2*s*p := by
  have hSP := (signedTV_pathHeatSignedTensor_le S P).trans
    (mul_le_mul hS hP ENNReal.toReal_nonneg hs)
  have hPS := (signedTV_pathHeatSignedTensor_le P S).trans
    (mul_le_mul hP hS ENNReal.toReal_nonneg hp)
  have h := (signedTV_add_le (Q+pathHeatSignedTensor S P) (pathHeatSignedTensor P S)).trans
    (add_le_add ((signedTV_add_le Q (pathHeatSignedTensor S P)).trans (add_le_add hQ hSP)) hPS)
  change signedTV (pathHeatObservableDerivativeMeasure S P Q)≤_ at h
  nlinarith

theorem tendsto_pathHeatDensityDerivativeMeasure_TV {A : Type*} {l : Filter A}
    (S : A→SignedMeasure X) (M : A→SignedMeasure (X×X))
    (S₀ : SignedMeasure X) (M₀ : SignedMeasure (X×X)) (s : ℝ)
    (hbound : ∀i,signedTV (S i)≤ s)
    (hS : Tendsto (fun i=>signedTV (S i-S₀)) l (𝓝 0))
    (hM : Tendsto (fun i=>signedTV (M i-M₀)) l (𝓝 0)) :
    Tendsto (fun i=>signedTV (pathHeatDensityDerivativeMeasure (S i) (M i)-
      pathHeatDensityDerivativeMeasure S₀ M₀)) l (𝓝 0) :=
  tendsto_signedTV_add M (fun i=>pathHeatSignedTensor (S i) (S i)) M₀
    (pathHeatSignedTensor S₀ S₀) hM (tendsto_pathHeatSignedTensor_TV S S₀ S S₀ s hbound hS hS)

theorem tendsto_pathHeatObservableDerivativeMeasure_TV {A : Type*} {l : Filter A}
    (S P : A→SignedMeasure X) (Q : A→SignedMeasure (X×X))
    (S₀ P₀ : SignedMeasure X) (Q₀ : SignedMeasure (X×X)) (s p : ℝ)
    (hboundS : ∀i,signedTV (S i)≤ s) (hboundP : ∀i,signedTV (P i)≤ p)
    (hS : Tendsto (fun i=>signedTV (S i-S₀)) l (𝓝 0))
    (hP : Tendsto (fun i=>signedTV (P i-P₀)) l (𝓝 0))
    (hQ : Tendsto (fun i=>signedTV (Q i-Q₀)) l (𝓝 0)) :
    Tendsto (fun i=>signedTV (pathHeatObservableDerivativeMeasure (S i) (P i) (Q i)-
      pathHeatObservableDerivativeMeasure S₀ P₀ Q₀)) l (𝓝 0) :=
  tendsto_signedTV_add (fun i=>Q i+pathHeatSignedTensor (S i) (P i))
    (fun i=>pathHeatSignedTensor (P i) (S i))
    (Q₀+pathHeatSignedTensor S₀ P₀) (pathHeatSignedTensor P₀ S₀)
    (tendsto_signedTV_add Q (fun i=>pathHeatSignedTensor (S i) (P i)) Q₀
      (pathHeatSignedTensor S₀ P₀) hQ
      (tendsto_pathHeatSignedTensor_TV S S₀ P P₀ s hboundS hS hP))
    (tendsto_pathHeatSignedTensor_TV P P₀ S S₀ p hboundP hP hS)

theorem tendsto_pathHeatDensityGenerator {A : Type*} {l : Filter A}
    (K : A→X×X→ᵇℝ) (K₀ : X×X→ᵇℝ)
    (S : A→SignedMeasure X) (M : A→SignedMeasure (X×X))
    (S₀ : SignedMeasure X) (M₀ : SignedMeasure (X×X))
    (dotell : A→ℝ) (dotell₀ s m : ℝ) (hs : 0 ≤ s) (hm : 0 ≤ m)
    (hboundS : ∀i,signedTV (S i)≤ s) (hboundM : ∀i,signedTV (M i)≤ m)
    (hK : Tendsto K l (𝓝 K₀)) (hS : Tendsto (fun i=>signedTV (S i-S₀)) l (𝓝 0))
    (hM : Tendsto (fun i=>signedTV (M i-M₀)) l (𝓝 0))
    (hdot : Tendsto dotell l (𝓝 dotell₀)) :
    Tendsto (fun i=>pathHeatDensityGenerator (K i) (S i) (M i) (dotell i)) l
      (𝓝 (pathHeatDensityGenerator K₀ S₀ M₀ dotell₀)) :=
  hdot.add ((tendsto_signedContraction K K₀
    (fun i=>pathHeatDensityDerivativeMeasure (S i) (M i))
    (pathHeatDensityDerivativeMeasure S₀ M₀) (m+s*s) (by positivity)
    (fun i=>pathHeatDensityDerivativeMeasure_TV_bound _ _ s m hs (hboundS i) (hboundM i)) hK
    (tendsto_pathHeatDensityDerivativeMeasure_TV S M S₀ M₀ s hboundS hS hM)).const_mul (1/2))

theorem tendsto_pathHeatObservableGenerator {A : Type*} {l : Filter A}
    (K : A→X×X→ᵇℝ) (K₀ : X×X→ᵇℝ)
    (S P : A→SignedMeasure X) (Q : A→SignedMeasure (X×X))
    (S₀ P₀ : SignedMeasure X) (Q₀ : SignedMeasure (X×X))
    (dotphi : A→ℝ) (dotphi₀ s p q : ℝ) (hs : 0 ≤ s) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hboundS : ∀i,signedTV (S i)≤ s) (hboundP : ∀i,signedTV (P i)≤ p)
    (hboundQ : ∀i,signedTV (Q i)≤ q)
    (hK : Tendsto K l (𝓝 K₀)) (hS : Tendsto (fun i=>signedTV (S i-S₀)) l (𝓝 0))
    (hP : Tendsto (fun i=>signedTV (P i-P₀)) l (𝓝 0))
    (hQ : Tendsto (fun i=>signedTV (Q i-Q₀)) l (𝓝 0))
    (hdot : Tendsto dotphi l (𝓝 dotphi₀)) :
    Tendsto (fun i=>pathHeatObservableGenerator (K i) (S i) (P i) (Q i) (dotphi i)) l
      (𝓝 (pathHeatObservableGenerator K₀ S₀ P₀ Q₀ dotphi₀)) :=
  hdot.add ((tendsto_signedContraction K K₀
    (fun i=>pathHeatObservableDerivativeMeasure (S i) (P i) (Q i))
    (pathHeatObservableDerivativeMeasure S₀ P₀ Q₀) (q+2*s*p) (by positivity)
    (fun i=>pathHeatObservableDerivativeMeasure_TV_bound _ _ _ s p q hs hp
      (hboundS i) (hboundP i) (hboundQ i)) hK
    (tendsto_pathHeatObservableDerivativeMeasure_TV S P Q S₀ P₀ Q₀ s p
      hboundS hboundP hS hP hQ)).const_mul (1/2))

theorem tendsto_pathHeatTreeKernelBCF_moving (L : ℕ)
    (K : ℕ→C(Fin L×I,C(Fin L×I,ℝ))) (G : C(Fin L×I,C(Fin L×I,ℝ)))
    (hK : Tendsto K atTop (𝓝 G)) :
    Tendsto (fun n=>BoundedContinuousFunction.mkOfCompact (pathHeatTreeKernelSample n L (K n)).uncurry)
      atTop (𝓝 (BoundedContinuousFunction.mkOfCompact G.uncurry)) := by
  have hn := pathHeatTreeKernel_norm_sub_tendsto_zero_of_tendsto L _ G
    (tendsto_pathHeatTreeKernelSample_moving L K G hK)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) (fun n=>?_) hn
  rw [←BoundedContinuousFunction.mkOfCompact_sub,BoundedContinuousFunction.norm_mkOfCompact]
  have he : (pathHeatTreeKernelSample n L (K n)).uncurry-G.uncurry=
      (pathHeatTreeKernelSample n L (K n)-G).uncurry := by ext x;rfl
  rw [he]
  exact norm_pathHeatTreeKernel_uncurry_le L _

def pathHeatTreeKernelBCF (L : ℕ) :
    C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]((Fin L×I)×(Fin L×I)→ᵇℝ) :=
  LinearMap.mkContinuous
    { toFun := fun (K : C(Fin L×I,C(Fin L×I,ℝ)))=>BoundedContinuousFunction.mkOfCompact K.uncurry
      map_add' := by
        intro K G
        ext x
        change (K+G) x.1 x.2=K x.1 x.2+G x.1 x.2
        simp only [ContinuousMap.add_apply]
      map_smul' := by
        intro c K
        ext x
        change (c•K) x.1 x.2=c*K x.1 x.2
        simp only [ContinuousMap.smul_apply,smul_eq_mul] }
    1 (fun K=>by
      change ‖BoundedContinuousFunction.mkOfCompact K.uncurry‖≤1*‖K‖
      rw [one_mul,BoundedContinuousFunction.norm_mkOfCompact]
      exact norm_pathHeatTreeKernel_uncurry_le L K)

@[simp] theorem pathHeatTreeKernelBCF_apply (L : ℕ)
    (K : C(Fin L×I,C(Fin L×I,ℝ))) :
    pathHeatTreeKernelBCF L K=BoundedContinuousFunction.mkOfCompact K.uncurry := rfl

theorem norm_pathHeatTreeKernelBCF_le (L : ℕ)
    (K : C(Fin L×I,C(Fin L×I,ℝ))) : ‖pathHeatTreeKernelBCF L K‖≤‖K‖ := by
  rw [pathHeatTreeKernelBCF_apply,BoundedContinuousFunction.norm_mkOfCompact]
  exact norm_pathHeatTreeKernel_uncurry_le L K

end HexagonPaper
