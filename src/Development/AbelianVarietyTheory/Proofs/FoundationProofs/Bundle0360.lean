module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedCongrAxLemmaOddPrime
section
open Polynomial

namespace GlobalTheory.AxSen

section Step

variable {K : Type} [Field K] {A : ValuationSubring K} {ϖ : K}

theorem ge_coeff_prod (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {q : ℚ} (s : Multiset K) (hs : ∀ d ∈ s, Ge A ϖ d q) (k : ℕ) :
    Ge A ϖ ((s.map fun d => X + C d).prod.coeff k) (((s.card : ℚ) - k) * q) := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · have := (ge_natCast_iff (A := A) h0 h1 (w := 1) (m := 0)).mpr ⟨1, A.one_mem, by simp⟩
      simpa using this
    · simpa [coeff_one] using ge_zero _
  | cons d s ih =>
    have hd := hs d (Multiset.mem_cons_self _ _)
    have ih' := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, coeff_add, coeff_C_mul, Multiset.card_cons]
    refine Ge.add ?_ ((hd.mul h0 h1 (ih' k)).mono (le_of_eq (by push_cast; ring)))
    rcases k with _ | k
    · rw [coeff_X_mul_zero]; exact ge_zero _
    · rw [coeff_X_mul]; exact (ih' k).mono (le_of_eq (by push_cast; ring))

theorem exists_ge_of_prod (s : Multiset K) (hs : s ≠ 0) {q : ℚ} (h : Ge A ϖ s.prod (q * s.card)) :
    ∃ d ∈ s, Ge A ϖ d q := by
  classical
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image s.toFinset A.valuation (Multiset.toFinset_nonempty.mpr hs)
  refine ⟨d, Multiset.mem_toFinset.mp hd, Ge.root (Multiset.card_pos.mpr hs) (h.of_le ?_)⟩
  rw [map_pow, map_multiset_prod, ← Multiset.card_map A.valuation s]
  refine Multiset.pow_card_le_prod fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  exact hmin y (Multiset.mem_toFinset.mpr hy)

theorem exists_root_hasseDeriv [IsAlgClosed K] [CharZero K] (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) (T : Finset K) (α : K) {a : ℚ}
    (hT : ∀ t ∈ T, Ge A ϖ (α - t) a) {j e : ℕ} (hj : j < T.card)
    (hc : A.valuation ϖ ^ e ≤ A.valuation ((T.card.choose j : ℕ) : K)) :
    ∃ β ∈ (hasseDeriv j (∏ t ∈ T, (X - C t))).roots, Ge A ϖ (α - β) (a - e / ((T.card - j : ℕ) : ℚ)) := by
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hPd : P.natDegree = T.card := by simp [hP]
  set Q := hasseDeriv j P with hQ
  have hQd : Q.natDegree = T.card - j := by rw [hQ, natDegree_hasseDeriv, hPd]
  have hlc : Q.leadingCoeff = ((T.card.choose j : ℕ) : K) := by
    rw [leadingCoeff, hQd, hQ, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, ← hPd, hPm.coeff_natDegree, mul_one]
  have hcard : Q.roots.card = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hev : Q.eval α = ((T.val.map fun t => α - t).map fun d => X + C d).prod.coeff j := by
    rw [hQ, ← taylor_coeff, taylor_apply, hP, prod_comp, Multiset.map_map]
    apply congrArg (fun p : K[X] => p.coeff j)
    change (∏ t ∈ T, (X - C t).comp (X + C α)) = ∏ t ∈ T, (X + C (α - t))
    refine Finset.prod_congr rfl fun t _ => ?_
    simp [add_sub_assoc]
  have hge := ge_coeff_prod h0 h1 (T.val.map fun t => α - t) (q := a) (by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hd
    exact hT t ht) j
  rw [← hev, ← hfac, eval_mul, eval_C, hlc, eval_multiset_prod, Multiset.map_map] at hge
  have hdiv := hge.div h0 h1 hc
  have hpos : 0 < T.card - j := Nat.sub_pos_of_lt hj
  obtain ⟨d, hd, hd'⟩ := exists_ge_of_prod (A := A) (ϖ := ϖ) (q := a - e / ((T.card - j : ℕ) : ℚ))
    (Q.roots.map ((fun p => eval α p) ∘ fun a => X - C a)) (by
      rw [← Multiset.card_pos, Multiset.card_map, hcard, hQd]; exact hpos)
    (hdiv.mono (le_of_eq (by
      rw [Multiset.card_map, Multiset.card_map, hcard, hQd, Finset.card_val]
      have : ((T.card - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [← Nat.cast_sub hj.le]
      field_simp)))
  obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hd
  exact ⟨β, hβ, by simpa using hd'⟩

end Step

section Orbit

variable {K : Type} [Field K] [Algebra ℚ K] {A : ValuationSubring K}

def loss (p n : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p n)

theorem loss_mono {p n n' : ℕ} (hp : p.Prime) (h : n ≤ n') : loss p n ≤ loss p n' := by
  have h1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  unfold loss
  gcongr

theorem loss_nonneg {p : ℕ} (hp : p.Prime) (n : ℕ) : 0 ≤ loss p n := by
  have := loss_mono hp (Nat.zero_le n)
  simpa [loss] using this

theorem loss_le_one {p : ℕ} (hp : 3 ≤ p) (n : ℕ) : loss p n ≤ 1 := by
  have h1 : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℚ) / ((p : ℚ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by nlinarith)]; nlinarith
  have h3 : (0 : ℚ) ≤ 1 / (p : ℚ) ^ Nat.log p n := by positivity
  have h4 : (0 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 := by positivity
  unfold loss
  nlinarith [mul_nonneg h3 h4]

theorem valuation_natCast_ge {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) {c e : ℕ} (hc : ¬ p ^ (e + 1) ∣ c) :
    A.valuation (p : K) ^ e ≤ A.valuation (c : K) := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.one_lt.ne'
  have hk : k ≤ e := by
    by_contra hk
    exact hc ((pow_dvd_pow p (by omega)).mul_right u)
  have hint : ∀ z : ℤ, A.valuation (z : K) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have hu1 : 1 ≤ A.valuation (u : K) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, t, hst⟩ : IsCoprime (p : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
    have e1 : (s : K) * p + t * u = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hst
    have : A.valuation ((s : K) * p + t * u) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint s)) h1
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint t)) hlt
    rw [e1, map_one] at this
    exact lt_irrefl _ this
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le hk).trans (le_mul_of_one_le_right' hu1)

theorem exists_fixed [IsAlgClosed K] {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) (H : Subgroup (K ≃ₐ[ℚ] K))
    (hH : ∀ h ∈ H, ∀ x ∈ A, h x ∈ A) (n : ℕ) :
    ∀ (α : K) (a : ℚ) (S : Finset K), S.card ≤ n → (∀ h ∈ H, h α ∈ S) → (∀ h ∈ H, Ge A (p : K) (h α - α) a) →
      ∃ y, (∀ h ∈ H, h y = y) ∧ Ge A (p : K) (α - y) (a - loss p n) := by
  classical
  haveI : CharZero K := algebraRat.charZero K
  have h0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α a S hS hαS hα
  set T := S.filter fun t => ∃ h ∈ H, h α = t with hT
  have hmem : ∀ t, t ∈ T ↔ ∃ h ∈ H, h α = t := fun t => by
    rw [hT, Finset.mem_filter]
    exact ⟨fun h => h.2, fun ⟨h, hh, e⟩ => ⟨e ▸ hαS h hh, h, hh, e⟩⟩
  have hTn : T.card ≤ n := (Finset.card_filter_le _ _).trans hS
  by_cases h2 : 2 ≤ T.card
  swap
  · refine ⟨α, fun h hh => ?_, by simpa using ge_zero _⟩
    exact Finset.card_le_one.mp (by omega : T.card ≤ 1) _ ((hmem _).mpr ⟨h, hh, rfl⟩) _ ((hmem _).mpr ⟨1, H.one_mem, rfl⟩)
  obtain ⟨j, e, hj0, hj, hdvd, hloss⟩ := _root_.GlobalTheory.exists_choose_small_valuation_ax p hp T.card h2
  change _ + loss p _ ≤ loss p _ at hloss
  obtain ⟨β, hβ, hαβ⟩ := exists_root_hasseDeriv h0 h1.le T α (a := a) (fun t ht => by
    obtain ⟨h, hh, rfl⟩ := (hmem t).mp ht
    exact (hα h hh).symm) hj (valuation_natCast_ge hp h1 hdvd)
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPd : P.natDegree = T.card := by simp [hP]
  have hQd : (hasseDeriv j P).natDegree = T.card - j := by rw [natDegree_hasseDeriv, hPd]
  have hPmap : ∀ h ∈ H, P.map (h : K →+* K) = P := by
    intro h hh
    rw [hP, Polynomial.map_prod]
    refine Finset.prod_bij (fun t _ => h t) (fun t ht => ?_) (fun t _ t' _ e => h.injective e) (fun t ht => ?_) (fun t _ => by simp)
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact (hmem _).mpr ⟨h * g, H.mul_mem hh hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact ⟨(h⁻¹ * g) α, (hmem _).mpr ⟨_, H.mul_mem (H.inv_mem hh) hg, rfl⟩, by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]⟩
  have hQmap : ∀ h ∈ H, (hasseDeriv j P).map (h : K →+* K) = hasseDeriv j P := by
    intro h hh
    ext k
    rw [coeff_map, hasseDeriv_coeff, map_mul, map_natCast, ← coeff_map, hPmap h hh]
  have he : (0 : ℚ) ≤ e / ((T.card - j : ℕ) : ℚ) := by positivity
  obtain ⟨y, hy, hβy⟩ := ih (T.card - j) (by omega) β (a - e / ((T.card - j : ℕ) : ℚ)) (hasseDeriv j P).roots.toFinset
    ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hQd.le)) (fun h hh => by
      rw [Multiset.mem_toFinset, mem_roots'] at *
      refine ⟨hβ.1, ?_⟩
      rw [← hQmap h hh]
      exact hβ.2.map (h : K →+* K)) (fun h hh => by
      have k1 := hαβ.symm.map h0 (h : K →+* K) (hH h hh) (map_natCast _ p)
      rw [map_sub] at k1
      exact Ge.trans k1 (((hα h hh).mono (by linarith)).trans hαβ))
  have hm := loss_mono hp hTn
  have hnn := loss_nonneg hp (T.card - j)
  exact ⟨y, hy, (hαβ.mono (by linarith)).trans (hβy.mono (by linarith))⟩

end Orbit


open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Ord2 in
theorem exists_fixed_congr (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (H : Subgroup (G ℚ Ω)) (hH : H ≤ Dec (F := ℚ) A) (m : ℕ) (x : Ω) (hx : x ∈ A)
    (hcg : ∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) :
    ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  classical
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have h0 : (l : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨v, hv, hlv⟩ := hA
  have h1 : A.valuation (l : Ω) < 1 := by simpa using (hv _).mpr hlv
  have hint : IsIntegral ℚ x := (IsAlgClosure.isAlgebraic.isAlgebraic x).isIntegral
  have h3 : 3 ≤ l := by have := hp.two_le; omega
  obtain ⟨y, hy, hxy⟩ := exists_fixed hp h1 H (fun h hh z hz => (apply_mem_iff_of_mem_Dec (hH hh) z).mpr hz) _ x ((m + 1 : ℕ) : ℚ)
    ((minpoly ℚ x).aroots Ω).toFinset le_rfl (fun h _ => by
      rw [Multiset.mem_toFinset, mem_aroots]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [aeval_algHom_apply, minpoly.aeval, map_zero])
    (fun h hh => (ge_natCast_iff h0 h1.le).mpr (hcg h hh))
  have hm : Ge A (l : Ω) (x - y) (m : ℚ) := hxy.mono (by
    have := loss_le_one h3 ((minpoly ℚ x).aroots Ω).toFinset.card
    push_cast; linarith)
  obtain ⟨z, hz, e⟩ := (ge_natCast_iff h0 h1.le).mp hm
  refine ⟨y, ?_, hy, z, hz, e⟩
  have : y = x - (l : Ω) ^ m * z := by rw [← e]; ring
  rw [this]
  exact A.sub_mem hx (A.mul_mem _ _ (A.pow_mem (natCast_mem A l) m) hz)

end GlobalTheory.AxSen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolyInRootOfInertiaCyclotomicFixed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaCycFixed

theorem cycMod_eq_one_of_fix (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (s : G ℚ Ω) (hs : s ζ = ζ) : cycMod ℚ Ω l m s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l (n := m)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
  have hs' : (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ = ζ := hs
  rw [hs'] at hspec
  set x : ZMod (l ^ m) := ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow m)
    with hx
  have hmod : x.val ≡ 1 [MOD l ^ m] := by
    have hne : l ^ m ≠ 0 := pow_ne_zero m (Fact.out : l.Prime).ne_zero
    have hz : IsPrimitiveRoot (hζ.isUnit hne).unit (l ^ m) := IsPrimitiveRoot.isUnit_unit hne hζ
    have key := (pow_eq_pow_iff_modEq (x := (hζ.isUnit hne).unit) (n := x.val) (m := 1)).1 (by
      ext
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_one]
      exact hspec.symm)
    rwa [← hz.eq_orderOf] at key
  have h1 : ((x.val : ℕ) : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  apply Units.ext
  simpa [cycMod, cycZ, hx] using h1

theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u : Ω, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ Q.eval ζ = u := by
  intro l _ Ω _ _ _ A m ζ hζ u hu
  have : IsGalois ℚ Ω := {}
  have hint : Algebra.IsIntegral ℚ Ω := Algebra.IsAlgebraic.isIntegral
  set I : Subgroup (G ℚ Ω) := Ine (F := ℚ) A with hI
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField I with hK
  have : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  set L : IntermediateField ℚ Ω := (IntermediateField.adjoin K {ζ}).restrictScalars ℚ with hL
  have hKL : K ≤ L := fun x hx => by
    show x ∈ IntermediateField.adjoin K {ζ}
    exact (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨x, hx⟩
  have hζL : ζ ∈ L := IntermediateField.mem_adjoin_simple_self K ζ

  have hfix : ∀ s ∈ L.fixingSubgroup, s u = u := by
    intro s hs

    let C : ClosedSubgroup (G ℚ Ω) := ⟨I.topologicalClosure, I.isClosed_topologicalClosure⟩
    have hsC : s ∈ I.topologicalClosure := by
      have hle : IntermediateField.fixedField C.toSubgroup ≤ K := by
        intro x hx
        rw [IntermediateField.mem_fixedField_iff] at hx ⊢
        intro f hf
        exact hx f (I.le_topologicalClosure hf)
      have h1 : s ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hKL hs
      have h2 := IntermediateField.fixingSubgroup_antitone hle h1
      rwa [InfiniteGalois.fixingSubgroup_fixedField C] at h2

    set E : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {u, ζ} with hE
    have : FiniteDimensional ℚ E := by
      rw [hE]
      refine IntermediateField.finiteDimensional_adjoin ?_
      intro x _
      exact Algebra.IsIntegral.isIntegral x
    have hopen : IsOpen ((E.fixingSubgroup : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := E.fixingSubgroup_isOpen
    have hopen' : IsOpen {x : G ℚ Ω | s⁻¹ * x ∈ E.fixingSubgroup} :=
      hopen.preimage (continuous_const.mul continuous_id)
    have hsmem : s ∈ {x : G ℚ Ω | s⁻¹ * x ∈ E.fixingSubgroup} := by
      simp only [Set.mem_ofPred_eq, inv_mul_cancel]
      exact one_mem _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hsC
    obtain ⟨i, hi1, hi2⟩ := mem_closure_iff.1 hsC _ hopen' hsmem
    simp only [Set.mem_ofPred_eq] at hi1
    have hu' : (s⁻¹ * i) u = u :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hi1 u (IntermediateField.subset_adjoin ℚ _ (by simp))
    have hζ' : (s⁻¹ * i) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hi1 ζ (IntermediateField.subset_adjoin ℚ _ (by simp))
    have hsζ : s ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ hζL
    have hiζ : i ζ = ζ := by
      have : i = s * (s⁻¹ * i) := by group
      rw [this, AlgEquiv.mul_apply, hζ', hsζ]
    have hiu : i u = u := hu i hi2 (cycMod_eq_one_of_fix l Ω m ζ hζ i hiζ)
    have : i = s * (s⁻¹ * i) := by group
    rw [this, AlgEquiv.mul_apply, hu'] at hiu
    exact hiu
  have huL : u ∈ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    exact hfix
  have huK : u ∈ IntermediateField.adjoin K {ζ} := huL
  have hζint : IsIntegral K ζ := (Algebra.IsIntegral.isIntegral (R := ℚ) ζ).tower_top
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at huK
  obtain ⟨P, hP⟩ := huK
  refine ⟨P.map (algebraMap K Ω), ?_, ?_⟩
  · intro x hx s hs
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [Polynomial.coeff_map]
    exact ((IntermediateField.mem_fixedField_iff _ _).1 (P.coeff n).2) s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hP

end GlobalTheory.InertiaCycFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInertiaFixedEvalEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory

theorem exists_polynomial_closedSubgroup_fixed_eval_eq {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] [IsGalois F Ω] (H : ClosedSubgroup (Ω ≃ₐ[F] Ω)) (ζ u : Ω)
    (h : ∀ s ∈ H.toSubgroup, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ H.toSubgroup, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u := by
  classical
  let T : IntermediateField F Ω := IntermediateField.fixedField H.toSubgroup
  have hT : T.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  let E : IntermediateField F Ω :=
    (IntermediateField.adjoin T ({ζ} : Set Ω)).restrictScalars F
  have hu : u ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs
    refine h s ?_ (hs ζ (IntermediateField.mem_adjoin_simple_self T ζ))
    have : s ∈ T.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hs x ((IntermediateField.adjoin T ({ζ} : Set Ω)).algebraMap_mem ⟨x, hx⟩)
    rw [hT] at this
    exact this
  have hint : IsIntegral T ζ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := F) ζ).isIntegral.tower_top
  have hu' : u ∈ (IntermediateField.adjoin T ({ζ} : Set Ω)).toSubalgebra := hu
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hu'
  obtain ⟨Q, hQ⟩ := hu'
  refine ⟨Q.map (algebraMap T Ω), ?_, ?_⟩
  · intro s hs d
    rw [Polynomial.coeff_map]
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup _).1 (Q.coeff d).2 s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hQ

theorem exists_polynomial_inertia_fixed_eval_eq (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω)
    (h : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) :
    ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧
      P.eval ζ = u :=
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  exists_polynomial_closedSubgroup_fixed_eval_eq
    ⟨Ine (F := ℚ) A, isClosed_Ine (F := ℚ) A⟩ ζ u h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernel
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaClosed

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem isOpen_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsOpen {σ : G ℚ Ω | P (σ x)} := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hH : ((IntermediateField.adjoin ℚ {x}).fixingSubgroup : Set (G ℚ Ω)) ∈ nhds (1 : G ℚ Ω) :=
    (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  rw [← map_mul_left_nhds_one σ]
  refine Filter.mem_map.2 (Filter.mem_of_superset hH fun τ hτ => ?_)
  have hτx : τ x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self ℚ x)
  show P ((σ * τ) x)
  rw [AlgEquiv.mul_apply, hτx]
  exact hσ

theorem isClosed_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {σ : G ℚ Ω | P (σ x)} := by
  have h := isOpen_setOf_apply x (fun y => ¬ P y)
  rw [← isOpen_compl_iff]
  convert h using 1

theorem mem_dec_of_forall {A : ValuationSubring Ω} {σ : G ℚ Ω} (h : ∀ x, σ x ∈ A ↔ x ∈ A) :
    σ ∈ A.decompositionSubgroup ℚ := by
  show σ ∈ Dec (F := ℚ) A
  rw [mem_Dec]
  ext x
  rw [show x = σ ((σ⁻¹ : G ℚ Ω) x) from (mul_inv_apply x).symm, ← AlgEquiv.smul_def σ ((σ⁻¹ : G ℚ Ω) x),
    ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, h]

theorem isClosed_Ine [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) :
    IsClosed ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have e : ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (⋂ x : Ω, {σ : G ℚ Ω | (σ x ∈ A ↔ x ∈ A)}) ∩
        ⋂ x : Ω, {σ : G ℚ Ω | A.valuation x ≤ 1 → A.valuation (σ x - x) < 1} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun x => apply_mem_iff_of_mem_Dec (F := ℚ) h.1 x, h.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mem_dec_of_forall h1, h2⟩
  rw [e]
  exact (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x (fun y => (y ∈ A ↔ x ∈ A))).inter
    (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x
      (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

theorem continuous_toZModPow' (l : ℕ) [hl : Fact l.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := l) n) := by
  first
  | exact @_root_.GlobalTheory.ContinuousZModPow.main
  | exact _root_.GlobalTheory.ContinuousZModPow.main
  | (apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousZModPow.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousZModPow.main ..)

theorem isClosed_ker_cycMod (l : ℕ) [Fact l.Prime] (m : ℕ) :
    IsClosed (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have hc : Continuous fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) :=
    (continuous_toZModPow' l m).comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))
  have e : (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' {1} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Units.val_eq_one]
    rfl
  rw [e]
  exact (isClosed_discrete _).preimage hc

end GlobalTheory.InertiaClosed


open GlobalTheory.InertiaClosed in
theorem GlobalTheory.isClosed_Ine_inf_ker_cycMod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ),
    IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  intro l _ Ω _ _ _ A m
  rw [Subgroup.coe_inf]
  exact (isClosed_Ine A).inter (isClosed_ker_cycMod l m)
end
end

