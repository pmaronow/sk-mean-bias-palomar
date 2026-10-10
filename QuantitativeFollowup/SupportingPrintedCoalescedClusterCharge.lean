module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral
public import QuantitativeFollowup.SupportingPrintedFreeQuantile

@[expose] public section

/-! The actual connected equal-clock component at the root of a retained
genealogy. Positive edges are exits; zero-time advances are contracted.
Retained leaves keep their multiplicity. Its literal original-origin
charge is computed before substituting the genuine incoming free mass. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeRootClusterExits (q : ℕ→Paper.Overlap) :
    {j : ℕ}→FiniteTerminalGenealogy j→ℕ
  | _,.leaf=>1
  | _,@FiniteTerminalGenealogy.advance j T=>
      if q (j+1)=q j then nativeRootClusterExits q T else 1
  | _,.fork T U=>nativeRootClusterExits q T+nativeRootClusterExits q U

@[reducible] def nativeRootClusterForks (q : ℕ→Paper.Overlap) :
    {j : ℕ}→FiniteTerminalGenealogy j→ℕ
  | _,.leaf=>0
  | _,@FiniteTerminalGenealogy.advance j T=>
      if q (j+1)=q j then nativeRootClusterForks q T else 0
  | _,.fork T U=>1+nativeRootClusterForks q T+nativeRootClusterForks q U

theorem nativeRootCluster_exits_eq_forks_add_one (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    nativeRootClusterExits q T=nativeRootClusterForks q T+1 := by
  induction T with
  | leaf=>rfl
  | @advance j T ih=>simp only [nativeRootClusterExits,nativeRootClusterForks];split <;> simp_all
  | fork T U ihT ihU=>simp only [nativeRootClusterExits,nativeRootClusterForks,ihT,ihU];omega

@[reducible] def nativeRootClusterContains (q : ℕ→Paper.Overlap) :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→FiniteCascadeRecordVertex T→Prop
  | _,.leaf,.root _=>True
  | _,.advance _,.root _=>True
  | _,@FiniteTerminalGenealogy.advance j T,.child v=>q (j+1)=q j ∧ nativeRootClusterContains q T v
  | _,.fork _ _,.root _=>True
  | _,.fork T _,.left v=>nativeRootClusterContains q T v
  | _,.fork _ U,.right v=>nativeRootClusterContains q U v

def nativeRootClusterOriginValue (q : ℕ→Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (C : ℝ) : NativeStreamingOrigin T→ℝ := by
  classical
  exact fun o=>match o with
    | .vertex v=>if nativeRootClusterContains q T v then C else 0
    | .edge _ _=>0

private theorem nativeRootClusterContains_root (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) : nativeRootClusterContains q T (.root T) := by
  cases T <;> trivial

private theorem nativeRootClusterContains_advance_child (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) :
    nativeRootClusterContains q T.advance (.child v) ↔
      q (j+1) = q j ∧ nativeRootClusterContains q T v := by
  cases T <;> cases v <;> rfl

private theorem nativeRootClusterOriginValue_root (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (C : ℝ) :
    nativeRootClusterOriginValue q T C (.vertex (.root T)) = C := by
  classical
  simp only [nativeRootClusterOriginValue, if_pos (nativeRootClusterContains_root q T)]

private theorem nativeRootClusterOriginValue_edge (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (C : ℝ) (e : NativeStreamingEdge T) (r : Paper.Overlap) :
    nativeRootClusterOriginValue q T C (.edge e r) = 0 := rfl

private theorem nativeOriginWeightIntegral_zero (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T s (fun _=>0)=0 := by
  induction T generalizing s with
  | leaf=>simp [nativeStreamingOriginWeightIntegral]
  | advance T ih=>simp only [nativeStreamingOriginWeightIntegral,ih,integral_zero,mul_zero,add_zero]
  | fork T U ihT ihU=>simp only [nativeStreamingOriginWeightIntegral,ihT,ihU,mul_zero,add_zero]

theorem nativeRootCluster_original_origin_charge (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (s C : ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T s (nativeRootClusterOriginValue q T C)=
      ((nativeRootClusterExits q T : ℝ)*Paper.parisiCDF μ (q j)-s)*C := by
  classical
  induction T generalizing s with
  | leaf=>
      simp only [nativeStreamingOriginWeightIntegral,nativeRootClusterOriginValue,
        nativeRootClusterContains,ite_true,nativeRootClusterExits,Nat.cast_one,hq0]
      rw [Paper.parisiCDF_eq_one_of_one_le μ (by norm_num)]
      ring
  | @advance j T ih=>
      by_cases hq : q (j+1)=q j
      · have hc : (fun o=>nativeRootClusterOriginValue q T.advance C (nativeStreamingOriginChild o))=
            nativeRootClusterOriginValue q T C := by
          funext o;cases o <;> simp [nativeRootClusterOriginValue,nativeStreamingOriginChild,
            nativeRootClusterContains_advance_child,hq]
        simp only [nativeStreamingOriginWeightIntegral, nativeRootClusterOriginValue_root,
          nativeRootClusterOriginValue_edge]
        rw [hc,ih,integral_zero]
        simp only [nativeRootClusterExits,if_pos hq,hq,ite_true]
        ring
      · have hc : (fun o=>nativeRootClusterOriginValue q T.advance C (nativeStreamingOriginChild o))=
            fun _=>0 := by
          funext o;cases o <;> simp [nativeRootClusterOriginValue,nativeStreamingOriginChild,
            nativeRootClusterContains_advance_child,hq]
        simp only [nativeStreamingOriginWeightIntegral, nativeRootClusterOriginValue_root,
          nativeRootClusterOriginValue_edge]
        rw [hc,nativeOriginWeightIntegral_zero,integral_zero]
        simp only [nativeRootClusterExits,if_neg hq,Nat.cast_one,one_mul,zero_add]
  | @fork j T U ihT ihU=>
      have hl : (fun o=>nativeRootClusterOriginValue q (.fork T U) C (nativeStreamingOriginLeft o))=
          nativeRootClusterOriginValue q T C := by
        funext o;cases o <;> rfl
      have hr : (fun o=>nativeRootClusterOriginValue q (.fork T U) C (nativeStreamingOriginRight o))=
          nativeRootClusterOriginValue q U C := by
        funext o;cases o <;> rfl
      simp only [nativeStreamingOriginWeightIntegral, nativeRootClusterOriginValue_root]
      rw [hl,hr,ihT,ihU]
      simp only [nativeRootClusterExits,Nat.cast_add]
      ring

def nativeCoalescedIncomingMass (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) : ℝ :=
  a+(parisiFreeMeasure μ a).real (Iio q)

theorem nativeCoalescedIncomingMass_atom (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor a) (q : Paper.Overlap) :
    Paper.parisiCDF μ q-nativeCoalescedIncomingMass μ a q=(parisiFreeMeasure μ a).real {q} := by
  have hc:=parisiFreeMeasure_real_cdf μ a q ha hμ q.property
  change (parisiFreeMeasure μ a).real (Iic q)=Paper.parisiCDF μ q-a at hc
  have he : Iic q=Iio q ∪ {q} := by
    ext r;simp only [mem_Iic,mem_union,mem_Iio,mem_singleton_iff];exact le_iff_lt_or_eq
  have hd : Disjoint (Iio q) {q} := by
    apply disjoint_left.mpr
    intro r hr hs
    simpa only [mem_singleton_iff.mp hs,mem_Iio,lt_self_iff_false] using hr
  rw [he,measureReal_union hd (measurableSet_singleton q)] at hc
  unfold nativeCoalescedIncomingMass
  linarith

theorem nativeRootCluster_printed_charge (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j) (C : ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T (nativeCoalescedIncomingMass μ a (q j))
      (nativeRootClusterOriginValue q T C)=
      ((parisiFreeMeasure μ a).real {q j}+
        ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j))*C := by
  rw [nativeRootCluster_original_origin_charge μ a q hq0 T]
  have h:=nativeCoalescedIncomingMass_atom μ a ha hμ (q j)
  calc
    _=(Paper.parisiCDF μ (q j)-nativeCoalescedIncomingMass μ a (q j)+
        ((nativeRootClusterExits q T : ℝ)-1)*Paper.parisiCDF μ (q j))*C := by ring
    _=_ := by rw [h]

end QuantitativeFollowup
