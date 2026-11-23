module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weightedHomogeneousComponent_mem_span_of_isMultiHomog {R : Type*} [CommRing R] {K : Type*}
    [DecidableEq K] {ι : K → Type*} {s : MRing ι R} {c : K → ℕ} (hs : IsMultiHomog s c)
    {t : MRing ι R} (ht : t ∈ Ideal.span {s}) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) b t ∈ Ideal.span {s} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  set_option synthInstance.maxHeartbeats 100000 in
    rw [a.as_sum, Finset.sum_mul, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  have hd : IsWeightedHomogeneous (blockWeight ι) (monomial d (AddMonoidAlgebra.coeff a d) * s)
      (Finsupp.weight (blockWeight ι) d + c) :=
    (isWeightedHomogeneous_monomial _ d _ rfl).mul hs
  by_cases hb : b = Finsupp.weight (blockWeight ι) d + c
  · subst hb
    rw [hd.weightedHomogeneousComponent_same]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [hd.weightedHomogeneousComponent_ne b hb]
    exact Ideal.zero_mem _

theorem isMultiHomogIdeal_sup_span_of_form {R : Type*} [CommRing R] {K : Type*} [DecidableEq K]
    {ι : K → Type*} {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) {s : MRing ι R}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  intro f hf b
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add (f := _)]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hI y hy b))
    (Ideal.mem_sup_right (weightedHomogeneousComponent_mem_span_of_isMultiHomog hs hz b))

theorem withBot_lt_of_add_one_lt {d : WithBot ℕ∞} {N : ℕ}
    (h : d + 1 < ((N + 1 : ℕ) : WithBot ℕ∞)) : d < ((N : ℕ) : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at h
      exact absurd h (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe k =>
      have h' : ((k + 1 : ℕ) : WithBot ℕ∞) < ((N + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast h
      have h'' : k + 1 < N + 1 := by exact_mod_cast h'
      have : k < N := by omega
      exact_mod_cast this

theorem CutByForm.proof (h1 : IntNumAssoc.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : MixedDiffLinear.Statement) : CutByForm.Statement.{u} := by
  intro F _ K _ _ ι _ n G hGp hG hdim s c hs hsG bs
  have : G.IsPrime := hGp
  set J : Ideal (MRing ι F) := G ⊔ Ideal.span {s} with hJdef
  set c' : K → ℤ := fun k => (c k : ℤ) with hc'

  have hnzd : ∀ y, s * y ∈ G → y ∈ G := fun y hy => (hGp.mem_or_mem hy).resolve_left hsG
  have hH : hilbFn J = diffStep c' (hilbFn G) := by
    funext m
    exact h2 F K ι G s c hG hs hnzd m

  have hnum : intNum F G (Matrix.vecCons c' bs) = intNum F J bs := by
    obtain ⟨-, -, -, h4, h5⟩ := h3 K n bs (hilbFn G) (hilbFn G) 0 0 c'
    unfold intNum
    rw [h5, ← h4, hH]

  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hG hs

  have hle : G ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk G s ∈ nonZeroDivisors (MRing ι F ⧸ G) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hsG (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ G) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hdimJ : ringKrullDim (MRing ι F ⧸ J) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    apply withBot_lt_of_add_one_lt
    have he : n + 1 + Fintype.card K + 1 = n + 2 + Fintype.card K := by omega
    rw [he]
    exact lt_of_le_of_lt hsucc hdim

  rw [hnum, h1 F K ι n J hJ hdimJ bs, divCycle_eq_idealCycle]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTClosure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type}

theorem tendsto_sub_const_atTop (s : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
  simpa [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id

theorem diffStep_eventuallyEq (b : K → ℤ) {F G : (K → ℤ) → ℤ} (h : F =ᶠ[Filter.atTop] G) :
    diffStep b F =ᶠ[Filter.atTop] diffStep b G := by
  have h' : ∀ᶠ m in Filter.atTop, F (m - b) = G (m - b) := (tendsto_sub_const_atTop b).eventually h
  filter_upwards [h, h'] with m hm hm'
  simp only [diffStep, hm, hm']

theorem foldr_diffStep_eventuallyEq (l : List (K → ℤ)) {F G : (K → ℤ) → ℤ}
    (h : F =ᶠ[Filter.atTop] G) :
    l.foldr diffStep F =ᶠ[Filter.atTop] l.foldr diffStep G := by
  induction l with
  | nil => simpa using h
  | cons b l ih =>
    simp only [List.foldr_cons]
    exact diffStep_eventuallyEq b ih

theorem DegLTClosure.proof (h1 : MixedDiffLinear.Statement) : DegLTClosure.Statement := by
  intro K n f g c s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf hg bs
    filter_upwards [hf bs, hg bs] with m hm hm'
    rw [(h1 K n bs f g c s 0).1, Pi.add_apply, hm, hm', add_zero]
  · intro hf bs
    filter_upwards [hf bs] with m hm
    rw [(h1 K n bs f g c s 0).2.1, Pi.smul_apply, hm, smul_zero]
  · intro hf bs
    have h' := (tendsto_sub_const_atTop s).eventually (hf bs)
    filter_upwards [h'] with m hm
    rw [(h1 K n bs f g c s 0).2.2.1]
    exact hm
  · intro hf bs
    have hz : ∀ᶠ m in Filter.atTop, mixedDiff (fun i : Fin n => bs i.succ) f m = 0 :=
      hf (fun i => bs i.succ)
    have hz' := (tendsto_sub_const_atTop (bs 0)).eventually hz
    filter_upwards [hz, hz'] with m hm hm'
    have e : mixedDiff bs f = diffStep (bs 0) (mixedDiff (fun i : Fin n => bs i.succ) f) := by
      unfold mixedDiff
      rw [List.ofFn_succ, List.foldr_cons]
    rw [e]
    simp only [diffStep, hm, hm', sub_zero]
  · intro hfg hf bs
    have e : mixedDiff bs f =ᶠ[Filter.atTop] mixedDiff bs g :=
      foldr_diffStep_eventuallyEq (List.ofFn bs) hfg
    filter_upwards [e, hf bs] with m hm hm'
    rw [← hm, hm']

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTEventuallyConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

namespace DegLTEventuallyConst

theorem eq_of_unitSteps_eq_zero {K : Type} [Fintype K] [DecidableEq K] (g : (K → ℤ) → ℤ)
    (N : K → ℤ) (h : ∀ m, N ≤ m → ∀ k, g m - g (m - Pi.single k 1) = 0) :
    ∀ d : ℕ, ∀ m, N ≤ m → ∑ k, (m k - N k).toNat = d → g m = g N := by
  intro d
  induction d with
  | zero =>
    intro m hm hs
    have hmN : m = N := by
      funext k
      have hk : (m k - N k).toNat = 0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have hle : N k ≤ m k := hm k
      omega
    rw [hmN]
  | succ d ih =>
    intro m hm hs
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, (m k - N k).toNat ≠ 0 := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero hne] at hs
      omega
    obtain ⟨m', hm'⟩ : ∃ m' : K → ℤ, m' = m - Pi.single k (1 : ℤ) := ⟨_, rfl⟩
    have hm'k : m' k = m k - 1 := by simp [hm']
    have hm'j : ∀ j, j ≠ k → m' j = m j := by
      intro j hj
      simp [hm', hj]
    have hkk : N k + 1 ≤ m k := by omega
    have hNm' : N ≤ m' := by
      intro j
      show N j ≤ m' j
      by_cases hj : j = k
      · rw [hj, hm'k]
        omega
      · rw [hm'j j hj]
        exact hm j
    have hs' : ∑ j, (m' j - N j).toNat = d := by
      have e1 := Finset.add_sum_erase Finset.univ (fun j => (m j - N j).toNat) (Finset.mem_univ k)
      have e2 := Finset.add_sum_erase Finset.univ
        (fun j => (m' j - N j).toNat) (Finset.mem_univ k)
      have e3 : ∑ j ∈ Finset.univ.erase k, (m' j - N j).toNat =
          ∑ j ∈ Finset.univ.erase k, (m j - N j).toNat :=
        Finset.sum_congr rfl fun j hj => by rw [hm'j j (Finset.ne_of_mem_erase hj)]
      simp only [hm'k] at e2
      omega
    have step : g m - g m' = 0 := by rw [hm']; exact h m hm k
    rw [← ih _ hNm' hs']
    omega

theorem proof (h1 : MixedDiffLinear.Statement) : DegLTEventuallyConst.Statement := by
  intro K _ _ n f hf bs
  have hev : ∀ k : K, ∀ᶠ m in Filter.atTop,
      mixedDiff bs f m - mixedDiff bs f (m - Pi.single k 1) = 0 := by
    intro k
    have hk := hf (Matrix.vecCons (Pi.single k 1) bs)
    rw [(h1 K n bs f 0 0 0 (Pi.single k 1)).2.2.2.2] at hk
    exact hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr hev)
  exact ⟨mixedDiff bs f N, Filter.eventually_atTop.mpr ⟨N, fun m hm =>
    eq_of_unitSteps_eq_zero (mixedDiff bs f) N (fun m hm => hN m hm) _ m hm rfl⟩⟩

end DegLTEventuallyConst

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTOfUnitSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem DegLTOfUnitSteps.degLT_diffStep (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement)
    (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ)
    (hf : ∀ k, DegLT (diffStep (Pi.single k 1) f) n) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  obtain ⟨l, hl⟩ := h1 K b
  rw [hl f]
  clear hl
  induction l with
  | nil =>
    intro cs
    refine Filter.Eventually.of_forall fun m => ?_
    have h0 := (h2 K n cs f f 0 0 0).2.1
    rw [zero_smul, zero_smul] at h0
    simp only [List.map_nil, List.sum_nil]
    rw [h0]
    rfl
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs : DegLT (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (diffStep (Pi.single t.1.1 1) f) f 0 t.1.2).2.2.1 (hf t.1.1)
    have hc : DegLT (t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) f t.2 0).2.1 hs
    exact (h3 K n _ (List.map (fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) l).sum
      0 0).1 hc ih

theorem DegLTOfUnitSteps.proof (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement) :
    DegLTOfUnitSteps.Statement := by
  intro K _ _ n f hf bs
  have key : mixedDiff bs f = mixedDiff (Fin.tail bs) (diffStep (bs 0) f) := by
    rw [(h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.1,
      ← (h2 K n (Fin.tail bs) f f 0 0 (bs 0)).2.2.2.2]
    congr 1
    exact (Fin.cons_self_tail bs).symm
  rw [key]
  exact DegLTOfUnitSteps.degLT_diffStep h1 h2 h3 K n f hf (bs 0) _

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDiffStepExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace DiffStepExpansion

variable {K : Type}

lemma listSum_apply {α : Type} (l : List α) (F : α → (K → ℤ) → ℤ) (m : K → ℤ) :
    (l.map F).sum m = (l.map fun t => F t m).sum := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih]

def expand [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  (l.map fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)).sum

lemma expand_apply [DecidableEq K] (l : List ((K × (K → ℤ)) × ℤ)) (f : (K → ℤ) → ℤ)
    (m : K → ℤ) :
    expand l f m = (l.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)).sum := by
  unfold expand
  rw [listSum_apply]
  rfl

def expandable (K : Type) [DecidableEq K] : AddSubgroup (K → ℤ) where
  carrier := {b | ∃ l : List ((K × (K → ℤ)) × ℤ), ∀ f, diffStep b f = expand l f}
  zero_mem' := ⟨[], fun f => by funext m; simp [diffStep, expand]⟩
  add_mem' := by
    rintro a c ⟨la, ha⟩ ⟨lc, hc⟩
    refine ⟨la ++ lc.map (fun t => ((t.1.1, t.1.2 + a), t.2)), fun f => ?_⟩
    funext m
    have h1 := congrFun (ha f) m
    have h2 := congrFun (hc f) (m - a)
    simp only [diffStep] at h1 h2 ⊢
    rw [expand_apply] at h1 h2
    rw [expand_apply, List.map_append, List.sum_append, List.map_map, ← h1]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 + a), t.2))).sum =
        (lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m - a - t.1.2)).sum := by
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply]
      congr 2
      abel
    rw [h3, ← h2]
    have : m - (a + c) = m - a - c := by abel
    rw [this]
    ring
  neg_mem' := by
    rintro c ⟨lc, hc⟩
    refine ⟨lc.map (fun t => ((t.1.1, t.1.2 - c), -t.2)), fun f => ?_⟩
    funext m
    have h2 := congrFun (hc f) (m + c)
    simp only [diffStep] at h2 ⊢
    rw [expand_apply] at h2
    rw [expand_apply, List.map_map]
    have h3 : (lc.map ((fun t : (K × (K → ℤ)) × ℤ =>
          t.2 * diffStep (Pi.single t.1.1 1) f (m - t.1.2)) ∘
          fun t => ((t.1.1, t.1.2 - c), -t.2))).sum =
        -(lc.map fun t => t.2 * diffStep (Pi.single t.1.1 1) f (m + c - t.1.2)).sum := by
      clear hc h2
      induction lc with
      | nil => simp
      | cons t l ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply] at ih ⊢
        have e : m - (t.1.2 - c) = m + c - t.1.2 := by abel
        rw [ih, e]
        ring
    rw [h3, ← h2]
    have e1 : m + c - c = m := by abel
    have e2 : m - -c = m + c := by abel
    rw [e1, e2]
    ring

lemma single_mem [DecidableEq K] (k : K) : (Pi.single k 1 : K → ℤ) ∈ expandable K :=
  ⟨[((k, 0), 1)], fun f => by funext m; simp [expand, shiftFn]⟩

theorem proof : DiffStepExpansion.Statement := by
  intro K _ _ b
  have hb : b ∈ expandable K := by
    rw [← Finset.univ_sum_single b]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    have : (Pi.single k (b k) : K → ℤ) = b k • (Pi.single k 1 : K → ℤ) := by
      ext j
      by_cases h : j = k <;> simp [h]
    rw [this]
    exact AddSubgroup.zsmul_mem _ (single_mem k) _
  obtain ⟨l, hl⟩ := hb
  exact ⟨l, fun f => hl f⟩

end DiffStepExpansion

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DimStrictDrop.proof : DimStrictDrop.Statement.{u} := by
  intro A _ Q Q' _ _ hlt
  let q : PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    ⟨⟨Q, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q' : Set A)) :=
    ⟨⟨⟨Q', inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q : Set A)) := ⟨q⟩
  let f : PrimeSpectrum.zeroLocus (R := A) (Q' : Set A) → PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    fun x => ⟨x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (le_trans (show (Q : Set A) ⊆ Q' from hlt.le) ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩
  have hf : StrictMono f := fun a b h => h
  rw [ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  have hq : q < f l.head := by
    show Q < (l.head.1.asIdeal)
    exact lt_of_lt_of_le hlt ((PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2)
  refine le_trans ?_ (le_iSup _ ((l.map f hf).cons q hq))
  have hlen : ((l.map f hf).cons q hq).length = l.length + 1 := by
    simp [RelSeries.cons_length, LTSeries.map]
  rw [hlen]
  simp

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventualValueFacts.proof : EventualValueFacts.Statement := by
  intro K f c s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨c, h⟩
    rw [eventualValue, dite_eq_left hex]
    obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
    exact hm1.symm.trans hm2
  · have ht : Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b + s, fun a ha => ?_⟩
      simpa using sub_le_sub_right ha s
    exact ht.eventually h

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsComponentDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def ComponentDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P →
      ∀ W : Ideal (MRing ι O), divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W →
        ringKrullDim (MRing ι O ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

