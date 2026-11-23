module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonneg
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem image_mk_eq_preimage_of_le {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    (QuotientAddGroup.mk : W → W ⧸ A') '' S =
      (AddSubgroup.quotientEquivProdOfLE hle) ⁻¹'
        (((QuotientAddGroup.mk : W → W ⧸ A) '' S) ×ˢ Set.univ) := by
  ext q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    have h1 : (AddSubgroup.quotientEquivProdOfLE hle (QuotientAddGroup.mk x)).1 =
        (QuotientAddGroup.mk x : W ⧸ A) := rfl
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, h1]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, QuotientAddGroup.eq.2 (hle (QuotientAddGroup.eq.1 hyx))⟩
    · rintro ⟨y, hy, hyx⟩
      have := hS y hy _ (QuotientAddGroup.eq.1 hyx)
      refine ⟨x, ?_, rfl⟩
      simpa using this

theorem ncard_image_mk_of_le {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * A'.relIndex A := by
  rw [image_mk_eq_preimage_of_le hle hS,
    Set.ncard_preimage_of_injective_subset_range (Equiv.injective _)
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _), Set.ncard_prod, Set.ncard_univ]
  rfl

theorem GoodSub.of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) : GoodSub W0 A' S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨AddSubgroup.relIndex_ne_zero_trans hi h1,
    fun h0 => h2 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    fun x hx a ha => h3 x hx a (hle ha), ?_⟩
  rw [image_mk_eq_preimage_of_le hle h3]
  haveI : Finite (A ⧸ A'.addSubgroupOf A) := Nat.finite_of_card_ne_zero hi
  exact (h4.prod Set.finite_univ).preimage (Equiv.injective _).injOn

theorem relVol_eq_mul_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W}
    (h1 : A.relIndex W0 ≠ 0) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    relVol W0 A = (A'.relIndex A : ℝ) * relVol W0 A' := by
  have h1' : A'.relIndex W0 ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hi h1
  have e1 : W0.relIndex A' * A'.relIndex A = (W0 ⊓ A').relIndex A := by
    have := AddSubgroup.relIndex_inf_mul_relIndex W0 A' A
    rwa [inf_eq_left.2 hle] at this
  have e2 : A'.relIndex (W0 ⊓ A) * W0.relIndex A = (A' ⊓ W0).relIndex A :=
    AddSubgroup.relIndex_inf_mul_relIndex A' W0 A
  have e3 : A'.relIndex (A ⊓ W0) * A.relIndex W0 = A'.relIndex W0 := by
    have := AddSubgroup.relIndex_inf_mul_relIndex A' A W0
    rwa [inf_eq_left.2 hle] at this
  rw [inf_comm A' W0, ← e1, inf_comm W0 A] at e2
  have e2' : (A'.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = W0.relIndex A' * A'.relIndex A := by
    exact_mod_cast e2
  have e3' : (A'.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = A'.relIndex W0 := by
    exact_mod_cast e3
  have n1 : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1
  have n2 : (A'.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast h1'
  unfold relVol
  rw [← mul_div_assoc, div_eq_div_iff n1 n2, ← e3']
  linear_combination (A.relIndex W0 : ℝ) * e2'

theorem GoodSub.count_eq_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard : ℝ) * relVol W0 A' := by
  rw [ncard_image_mk_of_le hle h.2.2.1, relVol_eq_mul_of_le h.1 hle hi]
  push_cast
  ring

theorem GoodSub.count_eq {W : Type} [AddCommGroup W] {W0 A B : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) (hB : GoodSub W0 B S) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard : ℝ) * relVol W0 B := by
  have i1 : (A ⊓ B).relIndex A ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_left]
    exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA.2.1
  have i2 : (A ⊓ B).relIndex B ≠ 0 := by
    rw [AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_ne_zero_trans hA.1 hB.2.1
  rw [hA.count_eq_of_le inf_le_left i1, hB.count_eq_of_le inf_le_right i2]

theorem GoodSub.cont_eq {W : Type} [AddCommGroup W] {W0 A : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) :
    cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A := by
  have h : IsCO W0 S := ⟨A, hA⟩
  unfold cont
  rw [dite_eq_left h]
  exact GoodSub.count_eq h.choose_spec hA

theorem cont_independent_pos : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W), (∀ A, GoodSub W0 A S → cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A) ∧ (∀ A A', GoodSub W0 A S → A' ≤ A → A'.relIndex A ≠ 0 → GoodSub W0 A' S) ∧ 0 ≤ cont W0 S ∧ (IsCO W0 S → S.Nonempty → 0 < cont W0 S) := by
  intro W _ W0 S
  refine ⟨fun A hA => hA.cont_eq, fun A A' h hle hi => h.of_le hle hi, ?_, ?_⟩
  · unfold cont relVol
    split_ifs
    · positivity
    · exact le_rfl
  · rintro ⟨A, hA⟩ hne
    rw [hA.cont_eq]
    have p1 : 0 < ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard :=
      (Set.ncard_pos hA.2.2.2).2 (hne.image _)
    have p2 : 0 < W0.relIndex A := Nat.pos_of_ne_zero hA.2.1
    have p3 : 0 < A.relIndex W0 := Nat.pos_of_ne_zero hA.1
    unfold relVol
    positivity

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizer
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CongFin

section Abstract

variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}

theorem mem_stab_iff (Λ : Submodule O V) (g : V ≃ₗ[E] V) :
    g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ↔ ∀ v, g v ∈ Λ ↔ v ∈ Λ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h, Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := g.injective hwv
      exact this ▸ hw
    · intro hv
      rw [← h, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      refine ⟨g.symm v, (h _).1 (by simpa using hv), ?_⟩
      exact g.apply_symm_apply v

theorem smul_mem_of (Λ : Submodule O V) {c : E} (hc : c ∈ O) {v : V} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem ⟨c, hc⟩ hv

theorem exists_pow_smul_mem {p : E} (hp : p ∈ O) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ Λ' : Submodule O V) (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ' : Set V) = ⊤) :
    ∃ a : ℕ, ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by
  first
  | exact @_root_.GlobalTheory.PowSmulMem.main
  | exact _root_.GlobalTheory.PowSmulMem.main
  | (apply _root_.GlobalTheory.PowSmulMem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowSmulMem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowSmulMem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowSmulMem.main ..)

def congSub (Λ : Submodule O V) (c : E) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = c • w}
  one_mem' := ⟨one_mem _, fun v _ => ⟨0, Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_⟩
    obtain ⟨w, hw, h⟩ := hb' v hv
    obtain ⟨w', hw', h'⟩ := ha' (b v) (((mem_stab_iff Λ b).1 hb v).2 hv)
    refine ⟨w' + w, Λ.add_mem hw' hw, ?_⟩
    rw [smul_add, ← h, ← h']
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun v hv => ?_⟩
    obtain ⟨w, hw, h⟩ := ha' (a⁻¹ v) (((mem_stab_iff Λ _).1 (inv_mem ha) v).2 hv)
    refine ⟨-w, Λ.neg_mem hw, ?_⟩
    have : a (a⁻¹ v) = v := a.apply_symm_apply v
    rw [smul_neg, ← h, this, neg_sub]

theorem conj_mem (Λ : Submodule O V) (c : E) {a g : V ≃ₗ[E] V}
    (ha : a ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ) (hg : g ∈ congSub Λ c) :
    a * g * a⁻¹ ∈ congSub Λ c := by
  refine ⟨mul_mem (mul_mem ha hg.1) (inv_mem ha), fun v hv => ?_⟩
  obtain ⟨w, hw, h⟩ := hg.2 (a⁻¹ v) (((mem_stab_iff Λ _).1 (inv_mem ha) v).2 hv)
  refine ⟨a w, ((mem_stab_iff Λ _).1 ha w).2 hw, ?_⟩
  have h2 : a (a⁻¹ v) = v := a.apply_symm_apply v
  rw [← map_smul, ← h, map_sub, h2]
  rfl

theorem conj_smul_eq (Λ : Submodule O V) (c : E) {a : V ≃ₗ[E] V}
    (ha : a ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ) :
    MulAut.conj a • congSub Λ c = congSub Λ c := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have e : (MulAut.conj a)⁻¹ • g = a⁻¹ * g * a⁻¹⁻¹ := by simp
  rw [e]
  constructor
  · intro h
    have := conj_mem Λ c ha h
    simpa [mul_assoc] using this
  · exact conj_mem Λ c (inv_mem ha)

theorem relIndex_ne_zero (Λ : Submodule O V) (hΛ : Λ.FG) {c : E} (hc : c ∈ O)
    (hfin : Finite (O ⧸ Ideal.span {(⟨c, hc⟩ : O)})) :
    (congSub Λ c).relIndex (MulAction.stabilizer (V ≃ₗ[E] V) Λ) ≠ 0 := by
  set I : Ideal O := Ideal.span {(⟨c, hc⟩ : O)} with hI
  haveI : Module.Finite O Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Finite (Λ ⧸ (I • ⊤ : Submodule O Λ)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  have hQ : ∀ x y : Λ, (Submodule.Quotient.mk x : Λ ⧸ (I • ⊤ : Submodule O Λ)) = Submodule.Quotient.mk y →
      ∃ w ∈ Λ, (x : V) - y = c • w := by
    intro x y h
    rw [Submodule.Quotient.eq, hI, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨w, -, hw⟩ := h
    exact ⟨w, w.2, (congrArg Subtype.val hw).symm⟩
  set S := MulAction.stabilizer (V ≃ₗ[E] V) Λ
  let f : S → (Λ ⧸ (I • ⊤ : Submodule O Λ)) → (Λ ⧸ (I • ⊤ : Submodule O Λ)) :=
    fun g q => Submodule.Quotient.mk ⟨g.1 (q.out : Λ), ((mem_stab_iff Λ _).1 g.2 _).2 q.out.2⟩
  have hf : ∀ g h : S, f g = f h → g⁻¹ * h ∈ (congSub Λ c).subgroupOf S := by
    intro g h hgh
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(g⁻¹ * h).2, fun v hv => ?_⟩
    let q : Λ ⧸ (I • ⊤ : Submodule O Λ) := Submodule.Quotient.mk ⟨v, hv⟩
    obtain ⟨w, hw, e1⟩ := hQ ⟨v, hv⟩ q.out (Quotient.out_eq q).symm
    obtain ⟨w', hw', e2⟩ := hQ _ _ (congrFun hgh q).symm
    have hi := (mem_stab_iff Λ _).1 (inv_mem g.2)
    have hh := (mem_stab_iff Λ _).1 h.2
    refine ⟨g.1⁻¹ (h.1 w) + g.1⁻¹ w' - w,
      Λ.sub_mem (Λ.add_mem ((hi _).2 ((hh _).2 hw)) ((hi _).2 hw')) hw, ?_⟩
    have e3 : v = (q.out : Λ) + c • w := by rw [← e1]; simp
    have e4 : h.1 (q.out : Λ) = g.1 (q.out : Λ) + c • w' := by rw [← e2]; simp
    have e5 : ∀ x, g.1⁻¹ (g.1 x) = x := fun x => g.1.symm_apply_apply x
    show g.1⁻¹ (h.1 v) - v = _
    rw [e3, map_add (f := _), e4]
    simp only [map_add (f := _), map_smul, e5, smul_add, smul_sub]
    abel
  have : Finite (S ⧸ (congSub Λ c).subgroupOf S) := by
    refine Finite.of_injective (fun q => f q.out) fun q q' h => ?_
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact hf _ _ h
  exact Subgroup.index_ne_zero_of_finite

theorem mem_stab_of_cong {p : E} (hp : p ∈ O) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ : Submodule O V) (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ : Set V) = ⊤) {N : ℕ} (hN : 1 ≤ N)
    (g : V ≃ₗ[E] V) (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p ^ N • w) :
    g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ := by
  have hg1 : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p • w := by
    intro v hv
    obtain ⟨w, hw, h⟩ := hg v hv
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    exact ⟨p ^ M • w, smul_mem_of Λ (O.pow_mem hp M) hw, by rw [h, pow_add, pow_one, mul_smul]⟩
  have hle : ∀ v ∈ Λ, g v ∈ Λ := by
    intro v hv
    obtain ⟨w, hw, h⟩ := hg1 v hv
    rw [eq_add_of_sub_eq h]
    exact Λ.add_mem (smul_mem_of Λ hp hw) hv
  have hit : ∀ k : ℕ, ∀ v ∈ Λ, ∃ u ∈ Λ, ∃ w ∈ Λ, v = g u + p ^ k • w := by
    intro k v hv
    induction k with
    | zero => exact ⟨0, Λ.zero_mem, v, hv, by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, w, hw, e⟩ := ih
      obtain ⟨w', hw', e'⟩ := hg1 w hw
      refine ⟨u + p ^ k • w, Λ.add_mem hu (smul_mem_of Λ (O.pow_mem hp k) hw), -w',
        Λ.neg_mem hw', ?_⟩
      rw [e, map_add (f := _), map_smul, eq_add_of_sub_eq e', pow_succ, mul_smul]
      simp only [smul_add, smul_neg]
      abel
  let Λ1 : Submodule O V := Λ.map (g.symm.toLinearMap.restrictScalars O)
  obtain ⟨a, ha⟩ := exists_pow_smul_mem hp hdiv Λ1 Λ (hΛ.map _) hΛ'
  rw [mem_stab_iff]
  refine fun v => ⟨fun hv => ?_, hle v⟩
  obtain ⟨u, hu, w, hw, e⟩ := hit a _ hv
  have : v = u + p ^ a • g.symm w := g.injective (by rw [e]; simp)
  rw [this]
  exact Λ.add_mem hu (ha _ ⟨w, hw, rfl⟩)

theorem exists_level {p : E} (hp : p ∈ O) (hu : IsUnit p) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ Λ' : Submodule O V) (hΛ : Λ.FG) (hs : Submodule.span E (Λ : Set V) = ⊤)
    (hΛ' : Λ'.FG) (hs' : Submodule.span E (Λ' : Set V) = ⊤) (N : ℕ) :
    ∃ N' : ℕ, ∀ g : V ≃ₗ[E] V, (∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p ^ N' • w) →
      ∀ v ∈ Λ', ∃ w ∈ Λ', g v - v = p ^ N • w := by
  obtain ⟨a, ha⟩ := exists_pow_smul_mem hp hdiv Λ Λ' hΛ hs'
  obtain ⟨b, hb⟩ := exists_pow_smul_mem hp hdiv Λ' Λ hΛ' hs
  refine ⟨b + (N + a), fun g hg v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := hg _ (hb v hv)
  refine ⟨p ^ a • w, ha w hw, ?_⟩
  rw [map_smul, ← smul_sub, pow_add, mul_smul, pow_add, mul_smul] at e
  exact (hu.pow b).smul_left_cancel.1 e

end Abstract

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_mul_mem (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (e : E) :
    ∃ a : ℕ, algebraMap F E ϖ ^ a * e ∈ L.O := by
  haveI := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  obtain ⟨y, hy, hi⟩ := ((IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2
    (Algebra.IsAlgebraic.isAlgebraic e)).exists_integral_multiple
  obtain ⟨a, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  refine ⟨a, (L.O_def _).2 ?_⟩
  have h := hi.smul (u⁻¹ : (𝒪[F])ˣ).1
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow] at h
  exact h

end GlobalTheory.HL.CongFin


open GlobalTheory.HL.CongFin in
theorem GlobalTheory.HL.congruence_subgroup_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Λ : Submodule L.O (Fin n → E)), IsLat L Λ → ∀ N : ℕ, (∃ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (∀ g, g ∈ K ↔ g ∈ stabL L Λ ∧ CongId L ϖ Λ N g) ∧ K.relIndex (stabL L Λ) ≠ 0 ∧ ∀ a ∈ stabL L Λ, MulAut.conj a • K = K) ∧ (1 ≤ N → ∀ g, CongId L ϖ Λ N g → g ∈ stabL L Λ) ∧ ∀ Λ', IsLat L Λ' → ∃ N' : ℕ, ∀ g, CongId L ϖ Λ N' g → CongId L ϖ Λ' N g := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Λ hΛ N
  obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hp : algebraMap F E ϖ ∈ L.O := (hO _).2 ϖ.2
  have hu : IsUnit (algebraMap F E ϖ) :=
    (IsUnit.mk0 (ϖ : F) (fun h => hϖ.ne_zero (Subtype.ext h))).map _
  have hdiv := exists_pow_mul_mem L ϖ hϖ
  simp only [CongId, map_pow]
  refine ⟨⟨congSub Λ (algebraMap F E ϖ ^ N), fun g => Iff.rfl, ?_, fun a ha => conj_smul_eq Λ _ ha⟩,
    fun hN g hg => mem_stab_of_cong hp hdiv Λ hΛ.1 hΛ.2 hN g hg,
    fun Λ' hΛ' => exists_level hp hu hdiv Λ Λ' hΛ.1 hΛ.2 hΛ'.1 hΛ'.2 N⟩
  refine relIndex_ne_zero Λ hΛ.1 (L.O.pow_mem hp N) ?_
  have hs : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ N)}
      = {(⟨algebraMap F E ϖ ^ N, L.O.pow_mem hp N⟩ : L.O)} := by
    ext y; simp [Subtype.ext_iff]
  have h := hcard N
  rw [hs] at h
  refine Nat.finite_of_card_ne_zero ?_
  rw [h]
  exact pow_ne_zero _ (by omega)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetGramSumElimSmulSub
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc

namespace GlobalTheory

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

private lemma hsub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [eq_sub_iff_add_eq, ← H.h_add_left, sub_add_cancel]

private lemma hsub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, hsub_left, map_sub, ← H.h_herm, ← H.h_herm]

private lemma hsmul_right (c : F) (x y : V) :
    H.h x (algebraMap F E c • y) = algebraMap F E c * H.h x y := by
  rw [H.h_herm (algebraMap F E c • y) x, H.h_smul_left, map_mul, AlgEquiv.commutes, ← H.h_herm]

private lemma det_transpose_map_cj {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι E) :
    (N.transpose.map M.L.cj).det = M.L.cj N.det := by
  have h1 := RingHom.map_det (M.L.cj : E →+* E) N.transpose
  rw [Matrix.det_transpose] at h1
  exact h1.symm

private lemma castLE_succ_eq_castSucc (r : ℕ) (h : r ≤ r + 1) :
    (Fin.castLE h : Fin r → Fin (r + 1)) = Fin.castSucc := by
  funext i
  rfl

theorem det_gram_sumElim_frames {r : ℕ} (P : LocNG.FPair H r) :
    (H.gram (Sum.elim P.A.f P.B.f)).det = (-1) ^ (r + 1) * P.Gv := by
  have diag : ∀ (Fr : LocNG.FrameD H r) (a b : Fin (r + 1)),
      H.h (Fr.f b) (Fr.f a) = Matrix.diagonal
        (fun i => if i = Fin.last r then -algebraMap F E Fr.T else 0) a b := by
    intro Fr a b
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = Fin.last r
      · subst ha
        simp [Fr.h_zz]
      · simp [ha, Fr.h_iso a a (Or.inl ha)]
    · rw [if_neg hab, Fr.h_iso b a ?_]
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hab (hc.2.trans hc.1.symm)
  have hblk : H.gram (Sum.elim P.A.f P.B.f) = Matrix.fromBlocks
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.A.T else 0)
      (H.Zhat P.A.f P.B.f)
      ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj)
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.B.T else 0) := by
    ext (a | a) (b | b)
    · exact diag P.A a b
    · rfl
    · exact H.h_herm _ _
    · exact diag P.B a b
  rw [hblk, GlobalTheory.det_gram_two_frames, det_transpose_map_cj]
  have hsub : ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj).submatrix Fin.castSucc Fin.castSucc
      = ((H.Zhat P.A.f P.B.f).submatrix Fin.castSucc Fin.castSucc).transpose.map M.L.cj := rfl
  rw [hsub, det_transpose_map_cj]
  congr 1
  simp only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, HermSp.Dl, dif_pos le_rfl,
    dif_pos (Nat.le_succ r), Fin.castLE_rfl, Matrix.submatrix_id_id, castLE_succ_eq_castSucc, map_mul]

theorem det_gram_sumElim_smul_sub {n : ℕ} (f f' : Fin n → V) (c : F) :
    (H.gram (Sum.elim f fun a => algebraMap F E c • (f' a - f a))).det
      = algebraMap F E c ^ (2 * n) * (H.gram (Sum.elim f f')).det := by
  set c' := algebraMap F E c with hc'
  have hcs : ∀ x : E, c • x = algebraMap F E c * x := fun x => Algebra.smul_def c x
  have key : H.gram (Sum.elim f fun a => c' • (f' a - f a)) =
      Matrix.fromBlocks 1 0 (-c' • (1 : Matrix (Fin n) (Fin n) E)) (c' • 1) * H.gram (Sum.elim f f') *
        Matrix.fromBlocks 1 (-c' • (1 : Matrix (Fin n) (Fin n) E)) 0 (c' • 1) := by
    ext (a | a) (b | b) <;>
      simp [HermSp.gram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, H.h_smul_left,
        hsub_left, hsub_right, hc', hsmul_right, hcs] <;> ring
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, Matrix.det_smul, Fintype.card_fin, one_mul, two_mul, pow_add]
  ring

end

theorem det_gram_frame_generators :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
      ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r _k : ℕ) (P : LocNG.FPair H r),
        (H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1))
          = (-1) ^ (r + 1) * P.Gv := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r _ P
  unfold LocNG.FPair.MMgen HermSp.MMfam LocNG.theta
  cases hs : M.split with
  | none =>
    simp only [map_one, one_pow, mul_one]
    exact det_gram_sumElim_frames H P
  | some g =>
    simp only
    rw [det_gram_sumElim_smul_sub H, det_gram_sumElim_frames H P, mul_comm _ (algebraMap F E _ ^ _),
      ← mul_assoc, ← mul_pow, ← map_mul]
    have hq : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    rw [mul_inv_cancel₀ hq, map_one, one_pow, one_mul]

end GlobalTheory
end

