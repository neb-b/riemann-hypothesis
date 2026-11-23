module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblMixed
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem perm_lift {α β : Type*} (f : α → β) {m m' : List β} (h : m.Perm m') :
    ∀ l : List α, l.map f = m' → ∃ l' : List α, l'.Perm l ∧ l'.map f = m := by
  induction h with
  | nil => intro l hl; exact ⟨l, .refl _, hl⟩
  | cons b _ ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a l =>
      simp only [List.map_cons, List.cons.injEq] at hl
      obtain ⟨l', hp, hm⟩ := ih l hl.2
      exact ⟨a :: l', hp.cons a, by simp [hm, hl.1]⟩
  | swap a b t =>
    intro l hl
    match l, hl with
    | u :: v :: l, hl =>
      simp only [List.map_cons, List.cons.injEq] at hl
      exact ⟨v :: u :: l, .swap _ _ _, by simp [hl.1, hl.2.1, hl.2.2]⟩
  | trans _ _ ih₁ ih₂ =>
    intro l hl
    obtain ⟨l₂, hp₂, hm₂⟩ := ih₂ l hl
    obtain ⟨l₁, hp₁, hm₁⟩ := ih₁ l₂ hm₂
    exact ⟨l₁, hp₁.trans hp₂, hm₁⟩

private theorem pairwise_filter_sym {α : Type*} (r : α → α → Prop) (p : α → Prop) [DecidablePred p] (l : List α)
    (h : (Multiset.filter p (l : Multiset α)).Pairwise r) :
    (l.filter fun b => decide (p b)).Pairwise fun y z => r y z ∨ r z y := by
  obtain ⟨l', hl', hp⟩ := h
  rw [Multiset.filter_coe, Multiset.coe_eq_coe] at hl'
  exact (List.Perm.pairwise_iff (fun h => h.symm) hl').2 (hp.imp Or.inl)

private theorem inert_both {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hIn : ∀ (m : ℕ) (x y : IrrCl (GL (Fin m) k)), IrrGL.IsCusp ⟨m, x⟩ → IrrGL.IsCusp ⟨m, y⟩ →
      UpperTheory.Zero.LLC.DZ ⟨m, x⟩ → UpperTheory.Zero.LLC.DZ ⟨m, y⟩ →
      (∀ γ, LinearMap.trace ℂ _ (levelZero x.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero y.rep.ρ γ)) →
      IrrGL.Inert ⟨m, x⟩ ⟨m, y⟩)
    (θ : AlgebraicClosure 𝓀[k] →* ℂ) (y z : IrrGL (k := k)) (hy : y.IsCusp) (hz : z.IsCusp)
    (hy' : UpperTheory.Zero.LLC.DZ y) (hz' : UpperTheory.Zero.LLC.DZ z) (cy cz : ℕ)
    (ty : ∀ γ, LinearMap.trace ℂ _ (levelZero y.rep γ) = cusp θ y.1 cy γ)
    (tz : ∀ γ, LinearMap.trace ℂ _ (levelZero z.rep γ) = cusp θ z.1 cz γ)
    (h : y.1 = z.1) (hc : cusp θ y.1 cz = cusp θ y.1 cy) : y.Inert z ∧ z.Inert y := by
  obtain ⟨m, X⟩ := y
  obtain ⟨m', Y⟩ := z
  obtain rfl : m = m' := h
  have e : ∀ γ, LinearMap.trace ℂ _ (levelZero X.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero Y.rep.ρ γ) := fun γ => by
    have h1 := ty γ
    have h2 := tz γ
    exact h1.trans ((congrFun hc γ).symm.trans h2.symm)
  exact ⟨hIn m X Y hy hz hy' hz' e, hIn m Y X hz hy hz' hy' fun γ => (e γ).symm⟩

private theorem core {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (hG : Group1) (hCF : CuspFrob) (hUF : UnlFull) (hJP : JDPair) (hJC : JDChar) (hLF : LblFull)
    (hIn : ∀ (m : ℕ) (x y : IrrCl (GL (Fin m) k)), IrrGL.IsCusp ⟨m, x⟩ → IrrGL.IsCusp ⟨m, y⟩ →
      UpperTheory.Zero.LLC.DZ ⟨m, x⟩ → UpperTheory.Zero.LLC.DZ ⟨m, y⟩ →
      (∀ γ, LinearMap.trace ℂ _ (levelZero x.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero y.rep.ρ γ)) →
      IrrGL.Inert ⟨m, x⟩ ⟨m, y⟩)
    (θ : AlgebraicClosure 𝓀[k] →* ℂ) (hθ : Inj θ) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hsm : IsSmooth π) (hirr : π.IsIrreducible)
    (s : Multiset (IrrGL (k := k))) (hs : HasSupport π s) (hU : GlobalTheory.RoadU.Unlinked s)
    (hP : (s.filter fun y => 2 ≤ y.1).Pairwise fun y z => ¬ y.Inert z)
    (m : ℕ) (x : Fin m → IrrGL (k := k)) (c : Fin m → ℕ) (hxs : Finset.univ.val.map x = s)
    (hx : ∀ a, (x a).IsCusp ∧ UpperTheory.Zero.LLC.DZ (x a) ∧ Reg (Nat.card 𝓀[k]) (x a).1 (c a) ∧
        ∀ γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).1 (c a) γ)
    (hL : HasLbl θ π ⟨Nat.card 𝓀[k], [], List.ofFn fun a => ((x a).1, c a)⟩) :
    ∃ a : Lbl, HasLbl θ π a ∧ a.Apart ∧ ∀ p ∈ a.L, ∃ y ∈ s, y.1 = p.1 := by
  obtain ⟨⟨hq2, -, hOk⟩, -, hn, -⟩ := hL
  have hpos : ∀ a, 0 < (x a).1 := fun a => (hOk _ (List.mem_ofFn.2 ⟨a, rfl⟩)).1
  set q := Nat.card 𝓀[k] with hq
  let c₁ : Fin m → ℕ := fun a => if (x a).1 = 1 then c a % (q - 1) else c a
  have hc₁ : ∀ a, cusp θ (x a).1 (c₁ a) = cusp θ (x a).1 (c a) := by
    intro a
    by_cases h : (x a).1 = 1
    · refine hCF 𝓀[k] θ hθ (x a).1 (c a) (c₁ a) 0 (hpos a) ?_
      simp only [c₁, if_pos h, h, ← hq, pow_one, pow_zero, mul_one]
      exact Nat.mod_modEq _ _
    · simp only [c₁, if_neg h]
  have hreg : ∀ a, Reg q (x a).1 (c₁ a) := by
    intro a
    by_cases h : (x a).1 = 1
    · intro i h0 h1
      omega
    · simp only [c₁, if_neg h]
      exact (hx a).2.2.1
  let f : IrrGL (k := k) × ℕ → ℕ × ℕ := fun t => (t.1.1, t.2)
  let T₀ : List (IrrGL (k := k) × ℕ) := List.ofFn fun a => (x a, c₁ a)
  have hmem : ∀ t ∈ T₀, ∃ a, t = (x a, c₁ a) := fun t ht => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 ht
    exact ⟨a, rfl⟩
  have hmemL : ∀ p ∈ T₀.map f, ∃ a, p = ((x a).1, c₁ a) := fun p hp => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
    obtain ⟨a, rfl⟩ := hmem t ht
    exact ⟨a, rfl⟩
  obtain ⟨D, hD, hDn, hDp⟩ := hG (T₀.map f) (fun p hp => by
    obtain ⟨a, rfl⟩ := hmemL p hp
    exact hpos a)
  obtain ⟨T, hTp, hTm⟩ := perm_lift f hDp T₀ rfl

  let x' : Fin T.length → IrrGL (k := k) := fun a => (T.get a).1
  let c' : Fin T.length → ℕ := fun a => (T.get a).2
  have hmap : Finset.univ.val.map x' = s := by
    rw [← hxs, Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe]
    have e1 : List.ofFn x' = T.map Prod.fst := by
      conv_rhs => rw [← List.ofFn_get T, List.map_ofFn]
      rfl
    have e2 : List.ofFn x = T₀.map Prod.fst := by
      simp only [T₀, List.map_ofFn]
      rfl
    rw [e1, e2]
    exact hTp.map _
  have hofn : List.ofFn (fun a => ((x' a).1, c' a)) = expand D ++ (T₀.map f).filter fun p => 2 ≤ p.1 := by
    rw [← hTm]
    conv_rhs => rw [← List.ofFn_get T, List.map_ofFn]
    rfl
  have hdegP : GlobalTheory.Shin.deg (expand D ++ (T₀.map f).filter fun p => 2 ≤ p.1) = GlobalTheory.Shin.deg (T₀.map f) := by
    unfold GlobalTheory.Shin.deg
    exact (hDp.map _).sum_eq
  have hdeg₀ : GlobalTheory.Shin.deg (T₀.map f) = n := by
    rw [hn]
    show _ = GlobalTheory.Shin.deg [] + GlobalTheory.Shin.deg _
    simp only [GlobalTheory.Shin.deg, T₀, List.map_ofFn, List.map_nil, List.sum_nil, zero_add]
    rfl
  have hd' : ∑ a, (x' a).1 = n := by
    rw [← hdeg₀, ← hdegP, ← hofn]
    simp only [GlobalTheory.Shin.deg, List.map_ofFn, List.sum_ofFn]
    rfl
  have heq := hUF k n V π T.length x' hd' (by rw [hmap]; exact hs) (by rw [hmap]; exact hU)
  have key : ∀ t ∈ T, ∀ γ, LinearMap.trace ℂ _ (levelZero t.1.rep γ) = cusp θ t.1.1 t.2 γ := by
    intro t ht
    obtain ⟨b, rfl⟩ := hmem t (hTp.mem_iff.1 ht)
    intro γ
    exact ((hx b).2.2.2 γ).trans (congrFun (hc₁ b) γ).symm
  have htr : ∀ a γ, LinearMap.trace ℂ _ (levelZero (x' a).rep γ) = cusp θ (x' a).1 (c' a) γ :=
    fun a => key (T.get a) (List.get_mem _ _)
  have hLm : ∀ p ∈ (T₀.map f).filter (fun p => 2 ≤ p.1), ∃ a, p = ((x a).1, c a) ∧ 2 ≤ (x a).1 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
    obtain ⟨a, rfl⟩ := hmemL p hp1
    have h2 : 2 ≤ (x a).1 := by simpa using hp2
    refine ⟨a, ?_, h2⟩
    have : (x a).1 ≠ 1 := by omega
    simp only [c₁, if_neg this]
  let a₀ : Lbl := ⟨q, D, (T₀.map f).filter fun p => 2 ≤ p.1⟩
  have hOk₀ : a₀.Ok := by
    refine ⟨hq2, fun p hp => (hD p hp).1, fun p hp => ?_⟩
    obtain ⟨a, rfl, -⟩ := hLm p hp
    exact ⟨hpos a, (hx a).2.2.1⟩
  obtain ⟨hJ1, hJ2⟩ := hJP 𝓀[k] θ hθ a₀ hOk₀ rfl
  have hrk : n = a₀.rk := by
    rw [← hJ1]
    exact (hdegP.trans hdeg₀).symm
  have hch := (hJC 𝓀[k] θ hθ).2 a₀ hOk₀ rfl
  rw [← hrk] at hJ2 hch
  have hMeets : Meets (levelZero π) (JD θ a₀.D a₀.L n) :=
    hLF k θ n V π hsm hirr T.length x' c' hd' heq htr _ hch (by rw [hofn]; exact hJ2)
  refine ⟨a₀, ⟨hOk₀, rfl, hrk, hMeets⟩, ⟨?_, hDn, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, ha⟩ := hmemL _ (hD p hp).2
    have h1 : (x a).1 = 1 := (Prod.ext_iff.1 ha).1.symm
    have h2 : p.2 = c₁ a := (Prod.ext_iff.1 ha).2
    show p.2 < q - 1
    rw [h2]
    simp only [c₁, if_pos h1]
    exact Nat.mod_lt _ (by have : 2 ≤ q := hq2; omega)
  · intro p hp
    obtain ⟨a, rfl, h2⟩ := hLm p hp
    exact h2
  · have hs₀ : s = ((T₀.map Prod.fst : List _) : Multiset _) := by
      rw [← hxs, Fin.univ_val_map]
      simp only [T₀, List.map_ofFn]
      rfl
    rw [hs₀] at hP
    have h1 := pairwise_filter_sym _ _ _ hP
    rw [List.filter_map, List.pairwise_map] at h1
    show ((T₀.map f).filter _).Pairwise _
    rw [List.filter_map, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ h1
    intro t₁ t₂ m₁ m₂ hh heq i hcong
    obtain ⟨m₁, r₁⟩ := List.mem_filter.1 m₁
    obtain ⟨m₂, r₂⟩ := List.mem_filter.1 m₂
    obtain ⟨a, rfl⟩ := hmem t₁ m₁
    obtain ⟨b, rfl⟩ := hmem t₂ m₂
    have ra : 2 ≤ (x a).1 := by simpa using r₁
    have rb : 2 ≤ (x b).1 := by simpa using r₂
    have na : (x a).1 ≠ 1 := by omega
    have nb : (x b).1 ≠ 1 := by omega
    have hcong' : c b ≡ c a * q ^ i [MOD q ^ (x a).1 - 1] := by
      have : c₁ b ≡ c₁ a * q ^ i [MOD q ^ (x a).1 - 1] := hcong
      simpa only [c₁, if_neg na, if_neg nb] using this
    have := inert_both hIn θ (x a) (x b) (hx a).1 (hx b).1 (hx a).2.1 (hx b).2.1 (c a) (c b) (hx a).2.2.2 (hx b).2.2.2
      heq (hCF 𝓀[k] θ hθ (x a).1 (c a) (c b) i (hpos a) hcong')
    exact hh.elim (· this.1) (· this.2)
  · intro p hp
    obtain ⟨a, rfl, -⟩ := hLm p hp
    exact ⟨x a, by rw [← hxs]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a), rfl⟩

theorem UpperTheory.Gal.InertialTypesAlt.lblMixed :
    LblOf → Group1 → CuspFrob → InertOf → UnlFull → JDPair → JDChar → LblFull → LblMixed := by
  intro hOf hG hCF hIn hUF hJP hJC hLF E Ω _ _ _ _ _ A v hv g _ i hi θ hθ n τ hM
  haveI : CharZero (v.adicCompletion E) :=
    charZero_of_injective_algebraMap (R := E) (algebraMap E (v.adicCompletion E)).injective
  obtain ⟨hDZ, s, hs, hU, hP⟩ := hM
  have e₀ := IrrGL.equivOf τ.ρ τ.smooth τ.irred
  have hs' : HasSupport τ.ρ s := hs.of_equiv e₀.symm
  have hfix : fixed τ.ρ (KOne (v.adicCompletion E) (Fin n)) ≠ ⊥ :=
    GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv e₀.symm hDZ
  obtain ⟨m, x, c, hxs, hx, hL⟩ := hOf (v.adicCompletion E) θ hθ n τ.V τ.ρ s hs' hfix
  obtain ⟨a, h1, h2, h3⟩ := core hG hCF hUF hJP hJC hLF (hIn E Ω A v hv g i hi) θ hθ n τ.ρ τ.smooth τ.irred s hs' hU hP
    m x c hxs hx hL
  exact ⟨a, s, h1, h2, hs', h3⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSepOf
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks

private theorem key {N M c x y : ℕ} (hc0 : 0 < c) (h : M * c = N) :
    ((x * c : ℕ) : ZMod N) = ((y * c : ℕ) : ZMod N) ↔ x ≡ y [MOD M] := by
  subst h
  rw [ZMod.natCast_eq_natCast_iff]
  exact ⟨Nat.ModEq.mul_right_cancel' hc0.ne', Nat.ModEq.mul_right' c⟩

private theorem fix_iff {N M c x : ℕ} (t : ℕ) (hc0 : 0 < c) (h : M * c = N) :
    ((t : ℕ) : ZMod N) * ((x * c : ℕ) : ZMod N) = ((x * c : ℕ) : ZMod N) ↔ x * t ≡ x [MOD M] := by
  rw [← Nat.cast_mul, show t * (x * c) = (x * t) * c by ring]
  exact key hc0 h

private theorem quot {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) :
    (q ^ m - 1) * ((q ^ f - 1) / (q ^ m - 1)) = q ^ f - 1 ∧ 0 < (q ^ f - 1) / (q ^ m - 1) := by
  have hdvd : q ^ m - 1 ∣ q ^ f - 1 := Nat.pow_sub_one_dvd_pow_sub_one q hd
  have h1 : (q ^ m - 1) * ((q ^ f - 1) / (q ^ m - 1)) = q ^ f - 1 := Nat.mul_div_cancel' hdvd
  refine ⟨h1, Nat.pos_of_ne_zero fun h0 => ?_⟩
  rw [h0, mul_zero] at h1
  have : 2 ≤ q ^ f := le_trans hq (Nat.le_self_pow hf.ne' q)
  omega

private def cl (q f m k j : ℕ) : ZMod (q ^ f - 1) :=
  ((k * q ^ j * ((q ^ f - 1) / (q ^ m - 1)) : ℕ) : ZMod (q ^ f - 1))

private theorem cl_fix {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (k j r : ℕ) :
    ((q ^ r : ℕ) : ZMod (q ^ f - 1)) * cl q f m k j = cl q f m k j ↔
      k * q ^ j * q ^ r ≡ k * q ^ j [MOD q ^ m - 1] := by
  obtain ⟨h1, h2⟩ := quot hq hf hd
  unfold cl
  exact fix_iff (q ^ r) h2 h1

private theorem cl_eq {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) {k k' j j' : ℕ}
    (h : cl q f m k j = cl q f m k' j') : k * q ^ j ≡ k' * q ^ j' [MOD q ^ m - 1] := by
  obtain ⟨h1, h2⟩ := quot hq hf hd
  unfold cl at h
  exact (key h2 h1).1 h

private theorem pow_one_mod {q m : ℕ} (hq : 2 ≤ q) : q ^ m ≡ 1 [MOD q ^ m - 1] := by
  exact Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))

private theorem not_fix {q m k : ℕ} (hq : 2 ≤ q) (hr : Reg q m k) (j r : ℕ) (h0 : 0 < r) (h1 : r < m) :
    ¬ k * q ^ j * q ^ r ≡ k * q ^ j [MOD q ^ m - 1] := by
  have := hr.not_modEq_of_lt hq (u := j) (v := j + r) (by omega) (by omega)
  rwa [pow_add, ← mul_assoc] at this

private theorem cross {q f m m' k k' j j' : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hd' : m' ∣ f)
    (hr : Reg q m' k') (hlt : m < m') : cl q f m k j ≠ cl q f m' k' j' := by
  intro h
  have hm : 0 < m := Nat.pos_of_dvd_of_pos hd hf
  have a := (cl_fix hq hf hd k j m).2 (by simpa using (pow_one_mod (m := m) hq).mul_left (k * q ^ j))
  rw [h] at a
  exact not_fix hq hr j' m hm hlt ((cl_fix hq hf hd' k' j' m).1 a)

private theorem same {q f m k k' j j' : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hj' : j' < m)
    (h : cl q f m k j = cl q f m k' j') : ∃ i, k' ≡ k * q ^ i [MOD q ^ m - 1] := by
  refine ⟨j + (m - j'), ?_⟩
  have e := (cl_eq hq hf hd h).mul_right (q ^ (m - j'))
  have e2 : k' * q ^ j' * q ^ (m - j') = k' * q ^ m := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj'.le]
  have e3 : k * q ^ j * q ^ (m - j') = k * q ^ (j + (m - j')) := by
    rw [mul_assoc, ← pow_add]
  rw [e2, e3] at e
  have e4 : k' * q ^ m ≡ k' [MOD q ^ m - 1] := by
    simpa using (pow_one_mod (m := m) hq).mul_left k'
  exact e4.symm.trans e.symm

private theorem block_nodup {q f m k : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hr : Reg q m k) :
    ((Multiset.range m).map (cl q f m k)).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range m)
  intro x hx y hy hxy
  rw [Multiset.mem_range] at hx hy
  have e := cl_eq hq hf hd hxy
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact Reg.not_modEq_of_lt hq hr hlt (by omega) e.symm
  · exact Reg.not_modEq_of_lt hq hr hlt (by omega) e

private def blk (q f : ℕ) (L : List (ℕ × ℕ)) : Multiset (ℕ × ZMod (q ^ f - 1)) :=
  (L.map fun p => (Multiset.range p.1).map fun j => ((1 : ℕ), cl q f p.1 p.2 j)).sum

private theorem map_snd_cons (q f : ℕ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    (blk q f (p :: L)).map Prod.snd =
      (Multiset.range p.1).map (cl q f p.1 p.2) + (blk q f L).map Prod.snd := by
  simp [blk, Multiset.map_map, Function.comp_def]

private theorem mem_blk {q f : ℕ} {L : List (ℕ × ℕ)} {e : ZMod (q ^ f - 1)}
    (h : e ∈ (blk q f L).map Prod.snd) : ∃ p ∈ L, ∃ j < p.1, e = cl q f p.1 p.2 j := by
  induction L with
  | nil => simp [blk] at h
  | cons p L ih =>
    rw [map_snd_cons, Multiset.mem_add] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 h
      exact ⟨p, List.mem_cons.2 (Or.inl rfl), j, Multiset.mem_range.1 hj, rfl⟩
    · obtain ⟨r, hr, j, hj, he⟩ := ih h
      exact ⟨r, List.mem_cons.2 (Or.inr hr), j, hj, he⟩

private theorem blk_nodup {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, Reg q p.1 p.2 ∧ p.1 ∣ f)
    (hP : L.Pairwise fun p r => p.1 = r.1 → ∀ i : ℕ, ¬ r.2 ≡ p.2 * q ^ i [MOD q ^ p.1 - 1]) :
    ((blk q f L).map Prod.snd).Nodup := by
  induction L with
  | nil => simp [blk]
  | cons p L ih =>
    rw [List.pairwise_cons] at hP
    have hp := hL p (List.mem_cons.2 (Or.inl rfl))
    have hL' : ∀ r ∈ L, Reg q r.1 r.2 ∧ r.1 ∣ f := fun r hr => hL r (List.mem_cons.2 (Or.inr hr))
    rw [map_snd_cons, Multiset.nodup_add]
    refine ⟨block_nodup hq hf hp.2 hp.1, ih hL' hP.2, ?_⟩
    rw [Multiset.disjoint_left]
    intro e he1 he2
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 he1
    rw [Multiset.mem_range] at hj
    obtain ⟨r, hr, j', hj', he⟩ := mem_blk he2
    have hrr := hL' r hr
    rcases lt_trichotomy p.1 r.1 with hlt | heq | hgt
    · exact cross hq hf hp.2 hrr.2 hrr.1 hlt he
    · have he' : cl q f p.1 p.2 j = cl q f p.1 r.2 j' := by
        rw [he, heq]
      obtain ⟨i, hi⟩ := same hq hf hp.2 (by omega) he'
      exact hP.1 r hr heq i hi
    · exact cross hq hf hrr.2 hp.2 hp.1 hgt he.symm

private theorem d_quot {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) :
    (q - 1) * ((q ^ f - 1) / (q - 1)) = q ^ f - 1 ∧ 0 < (q ^ f - 1) / (q - 1) := by
  simpa using quot hq hf (one_dvd f)

private theorem d_nodup {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (D : List (ℕ × ℕ))
    (hlt : ∀ p ∈ D, p.2 < q - 1) (hnd : (D.map Prod.snd).Nodup) :
    (D.map fun p => ((p.2 * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))).Nodup := by
  obtain ⟨h1, h2⟩ := d_quot hq hf
  have e : D.map (fun p => ((p.2 * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))) =
      (D.map Prod.snd).map (fun k => ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))) := by
    rw [List.map_map]
    rfl
  rw [e]
  refine List.Nodup.map_on ?_ hnd
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  have hm := (key h2 h1).1 hxy
  have ha' := hlt a ha
  have hb' := hlt b hb
  unfold Nat.ModEq at hm
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hm

private theorem d_fix {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (k : ℕ) :
    ((q ^ 1 : ℕ) : ZMod (q ^ f - 1)) * ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1)) =
      ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1)) := by
  refine (fix_iff _ (d_quot hq hf).2 (d_quot hq hf).1).2 ?_
  simpa using (pow_one_mod (m := 1) hq).mul_left k

end UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks

open UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks in
theorem UpperTheory.Gal.InertialTypesAlt.sepOf :
    SepOf := by
  intro a Q hok hap hsp
  obtain ⟨hq, -, hL⟩ := hok
  obtain ⟨hDlt, hDnd, hL2, hP⟩ := hap
  obtain ⟨f, hf, rfl, hdiv⟩ := hsp
  have hB : ((blk a.q f a.L).map Prod.snd).Nodup :=
    blk_nodup hq hf a.L (fun p hp => ⟨(hL p hp).2, hdiv p hp⟩) hP
  have hDn := d_nodup hq hf a.D hDlt hDnd
  unfold Lbl.Sep Lbl.blocks
  rw [Multiset.map_add (f := _), Multiset.nodup_add]
  refine ⟨?_, hB, ?_⟩
  · rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map]
    exact hDn
  · rw [Multiset.disjoint_left]
    intro e he1 he2
    rw [Multiset.map_coe, Multiset.mem_coe, List.map_map] at he1
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 he1
    obtain ⟨r, hr, j, hj, he⟩ := mem_blk (q := a.q) (f := f) (L := a.L) he2
    have e1 : e = ((p.2 * ((a.q ^ f - 1) / (a.q - 1)) : ℕ) : ZMod (a.q ^ f - 1)) := hpe.symm
    have hfix := d_fix hq hf p.2
    rw [← e1, he] at hfix
    have hr' := (cl_fix hq hf (hdiv r hr) r.2 j 1).1 hfix
    exact not_fix hq (hL r hr).2 j 1 one_pos (by have := hL2 r hr; omega) hr'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTensInc
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

theorem tensInc : TensInc := by
  intro k _ _ _ _ s d V _ _ σ
  refine ⟨PiTensorProduct.map fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype, ?_, ?_⟩
  · intro u w h
    have hl : ∀ a, ∃ g : V a →ₗ[ℂ] fixed (σ a) (KOne k (Fin (d a))),
        g ∘ₗ (fixed (σ a) (KOne k (Fin (d a)))).subtype = LinearMap.id := fun a =>
      LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
    choose g hg using hl
    have e : PiTensorProduct.map g ∘ₗ
        (PiTensorProduct.map fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hg]
      exact PiTensorProduct.map_id
    have h1 := LinearMap.congr_fun e u
    have h2 := LinearMap.congr_fun e w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, h]
  · intro x z
    have key : ∀ a, (fixed (σ a) (KOne k (Fin (d a)))).subtype ∘ₗ
        levelZero (σ a) (redLevi k (fun a => Fin (d a)) x a) =
          σ a ((x : (a : Fin s) → GL (Fin (d a)) k) a) ∘ₗ (fixed (σ a) (KOne k (Fin (d a)))).subtype :=
      fun a => LinearMap.ext fun v => levelZero_apply (σ a) ⟨_, x.2 a (Set.mem_univ a)⟩ v
    change (PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) ∘ₗ
        PiTensorProduct.map (fun a => levelZero (σ a) (redLevi k (fun a => Fin (d a)) x a))) z =
      (PiTensorProduct.map (fun a => σ a ((x : (a : Fin s) → GL (Fin (d a)) k) a)) ∘ₗ
        PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype)) z
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    simp only [key]

end UpperTheory.Gal.InertialTypesAlt
end
end

