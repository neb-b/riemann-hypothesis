module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveMulEqVonMangoldtConvolutionStatement
section
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution : ∀ (F : Type) [Field F] (q : ℕ), 2 ≤ q → ∀ (s m : F[X] → ℂ), IsAdditive s → m 1 = 1 → (∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P) → ∀ P : F[X], P.Monic → s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by
  first | exact @GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv | exact GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv | (intros; apply GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterEqInducedOfImprimitivitySystem
section
open GlobalTheory.BI

namespace GlobalTheory.BI

theorem character_eq_ind_of_imprimitive :
    ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  intro L _ _ G _ _ V _ _ _ ρ T e hirr he0 hee hT hoff
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨fun t => LinearMap.trace L V (ρ t * e), ?_, ?_⟩
  · exact isChar_trace_mul_idempotent L T V (ρ.comp T.subtype) e hee (fun t => hT t t.2)
  · intro g
    have hsum := GlobalTheory.sum_conj_idempotent_eq_card_smul L G V ρ T e hirr he0 hee hT hoff
    have hcard : (Nat.card T : L) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := T)).ne'
    have hkey : ∀ h : G, LinearMap.trace L V (ρ h * e)
        = ext0 T (fun t : T => LinearMap.trace L V (ρ t * e)) h := by
      intro h
      unfold ext0
      split_ifs with hh
      · rfl
      · have h2 : ρ h * e = ρ h * e * e := by rw [mul_assoc, hee]
        rw [h2, LinearMap.trace_mul_comm, ← mul_assoc, hoff h hh, map_zero]
    have hterm : ∀ x : G, LinearMap.trace L V (ρ g * (ρ x * e * ρ x⁻¹))
        = LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      intro x
      rw [show ρ g * (ρ x * e * ρ x⁻¹) = (ρ g * ρ x * e) * ρ x⁻¹ by simp only [mul_assoc],
        LinearMap.trace_mul_comm]
      simp only [map_mul, mul_assoc]
    have htr : (Nat.card T : L) * LinearMap.trace L V (ρ g)
        = ∑ x : G, LinearMap.trace L V (ρ (x⁻¹ * g * x) * e) := by
      have h3 : (Nat.card T : L) * LinearMap.trace L V (ρ g)
          = LinearMap.trace L V (ρ g * ∑ x : G, ρ x * e * ρ x⁻¹) := by
        rw [hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h3, Finset.mul_sum, map_sum]
      exact Finset.sum_congr rfl (fun x _ => hterm x)
    rw [Representation.character, ind, finsum_eq_sum_of_fintype]
    simp only [← hkey]
    rw [← htr, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMulParabolicInductionTrivial
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.MassMult

open scoped Classical

open Classical in
theorem finsum_subtype_dite {α : Type} [Fintype α] (p : α → Prop) (f : {x // p x} → ℂ) :
    ∑ᶠ x, f x = ∑ x, if h : p x then f ⟨x, h⟩ else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∑ i : {x // ¬ p x}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dif_neg i.2
  rw [h1, add_zero]
  exact Finset.sum_congr rfl fun i _ => by rw [dite_eq_left i.2]


open Classical in
theorem mass_eq {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (P : F[X]) :
    mass φ P = ∑ᶠ g, if LinearMap.charpoly g = P then φ g else 0 := by
  unfold mass
  refine finsum_congr fun g => ?_
  rw [finsum_eq_if]
  rfl

theorem finite_pairs {F : Type} [Field F] (P : F[X]) (hP : P.Monic) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  have h : {g : F[X] | g.Monic ∧ g ∣ P}.Finite := by
    have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
    exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})
  refine (h.prod h).subset ?_
  rintro x ⟨h1, h2, h3⟩
  exact ⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩

theorem finite_end (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] : Finite (Module.End F V) :=
  Module.finite_of_finite F

theorem mass_eq_zero {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (P : F[X]) (h : Module.finrank F V ≠ P.natDegree) : mass φ P = 0 := by
  rw [mass_eq]
  refine finsum_eq_zero_of_forall_eq_zero fun g => if_neg ?_
  rintro rfl
  exact h (LinearMap.charpoly_natDegree g).symm


open Classical in
theorem indicator_split {F : Type} [Field F] (P : F[X])
    (T : Finset (F[X] × F[X])) (hT : ∀ x, x ∈ T ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P)
    {a b c : F[X]} (ha : a.Monic) (hb : b.Monic) (hc : c = a * b) (z : ℂ) :
    (if c = P then z else 0) =
      ∑ x ∈ T, (if a = x.1 then z else 0) * (if b = x.2 then (1 : ℂ) else 0) := by
  by_cases hg : c = P
  · rw [if_pos hg, Finset.sum_eq_single (a, b)]
    · rw [if_pos rfl, if_pos rfl, mul_one]
    · rintro ⟨b1, b2⟩ _ hb
      by_cases h1 : a = b1
      · by_cases h2 : b = b2
        · exact absurd (by rw [h1, h2]) hb
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro hn
      exact (hn ((hT (a, b)).2 ⟨ha, hb, hc.symm.trans hg⟩)).elim
  · rw [if_neg hg]
    refine (Finset.sum_eq_zero ?_).symm
    rintro ⟨b1, b2⟩ hb
    by_cases h1 : a = b1
    · by_cases h2 : b = b2
      · refine absurd ?_ hg
        rw [hc, h1, h2]
        exact ((hT (b1, b2)).1 hb).2.2
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]


open Classical in
theorem stab_sum (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (φ : Module.End F W → ℂ) (P : F[X])
    (T : Finset (F[X] × F[X])) (hT : ∀ x, x ∈ T ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P) :
    ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        (if LinearMap.charpoly g.1 = P then φ (g.1.restrict g.2) else 0) =
      ∑ x ∈ T, (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
        (mass φ x.1 * mass (fun _ : Module.End F (V ⧸ W) => (1 : ℂ)) x.2) := by
  have := finite_end F V
  have := Fintype.ofFinite {g : Module.End F V // ∀ x ∈ W, g x ∈ W}
  have key : ∀ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
      (if LinearMap.charpoly g.1 = P then φ (g.1.restrict g.2) else 0) =
      ∑ x ∈ T, (if LinearMap.charpoly (g.1.restrict g.2) = x.1 then φ (g.1.restrict g.2) else 0) *
        (if LinearMap.charpoly (W.mapQ W g.1 (fun x hx => g.2 x hx)) = x.2 then (1 : ℂ) else 0) := by
    intro g
    have hc := (_root_.GlobalTheory.CuspGL.charpoly_block F V W g.1 g.2).1
    exact indicator_split P T hT (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _) hc _
  rw [finsum_congr key, finsum_eq_sum_of_fintype, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mass_eq, mass_eq, ← finsum_eq_sum_of_fintype]
  exact _root_.GlobalTheory.CuspGL.finsum_stabiliser_mul_blocks F V W (fun a => if LinearMap.charpoly a = x.1 then φ a else 0)
    (fun b => if LinearMap.charpoly b = x.2 then (1 : ℂ) else 0)

theorem glCard_ne_zero (F : Type) [Field F] [Finite F] (n : ℕ) : glCard F n ≠ 0 := by
  unfold glCard
  exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'

theorem mass_mult : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V → mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, Φ W.1 (g.restrict W.2)) P / glCard F P.natDegree = conv (fun D => mass (Φ (Fin D.natDegree → F)) D / glCard F D.natDegree) mu P := by
  classical
  intro F _ _ V _ _ _ Φ hΦ P hP hdeg
  have := finite_end F V
  have : Finite V := Module.finite_of_finite F
  have := Fintype.ofFinite (Module.End F V)
  have := Fintype.ofFinite (Submodule F V)
  have hfin := finite_pairs P hP
  have hT : ∀ x, x ∈ hfin.toFinset ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P := fun x => by
    rw [Set.Finite.mem_toFinset]; rfl
  have h1 : mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      Φ W.1 (g.restrict W.2)) P = ∑ W : Submodule F V,
      ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        (if LinearMap.charpoly g.1 = P then Φ W (g.1.restrict g.2) else 0) := by
    rw [mass_eq, finsum_eq_sum_of_fintype]
    simp only [finsum_subtype_dite]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : LinearMap.charpoly g = P
    · simp only [if_pos hg]
    · simp only [if_neg hg, dite_eq_ite, ite_self, Finset.sum_const_zero]
  rw [h1, conv, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [fun W : Submodule F V => stab_sum F V W (Φ W) P _ hT]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro ⟨D, E⟩ hx
  obtain ⟨hD, hE, hDE⟩ := (hT _).1 hx
  simp only at hD hE hDE ⊢
  have hsum : D.natDegree + E.natDegree = Module.finrank F V := by
    rw [← hdeg, ← hDE, hD.natDegree_mul hE]
  have h2 : ∀ W : Submodule F V, (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
      (mass (Φ W) D * mass (fun _ : Module.End F (V ⧸ W) => (1 : ℂ)) E) =
      if Module.finrank F W = D.natDegree then (Nat.card F : ℂ) ^ (D.natDegree * E.natDegree) *
        (mass (Φ (Fin D.natDegree → F)) D *
          mass (fun _ : Module.End F (Fin E.natDegree → F) => (1 : ℂ)) E) else 0 := by
    intro W
    by_cases hW : Module.finrank F W = D.natDegree
    · have hq : Module.finrank F (V ⧸ W) = E.natDegree := by
        have := Submodule.finrank_quotient_add_finrank W
        omega
      rw [if_pos hW, _root_.GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant F W Φ hΦ D hW.symm,
        _root_.GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant F (V ⧸ W) (fun _ _ _ _ _ => (1 : ℂ)) (fun _ _ _ _ _ _ _ _ _ _ => rfl) E hq.symm,
        hW, hq]
    · rw [if_neg hW, mass_eq_zero _ _ hW, zero_mul, mul_zero]
  have h3 := _root_.GlobalTheory.CuspGL.card_subspaces_mul_glCard F V D.natDegree (by omega)
  have h4 : Module.finrank F V - D.natDegree = E.natDegree := by omega
  rw [h4, Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = D.natDegree}),
    Fintype.card_subtype] at h3
  rw [Finset.sum_congr rfl fun W _ => h2 W, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hdeg, mu]
  have g1 := glCard_ne_zero F D.natDegree
  have g2 := glCard_ne_zero F E.natDegree
  have g3 := glCard_ne_zero F (Module.finrank F V)
  rw [div_mul_div_comm, div_eq_div_iff g3 (mul_ne_zero g1 g2), ← h3]
  ring

end GlobalTheory.CuspGL.MassMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIrrCharAdd
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_irreducible_subrepresentation {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

theorem exists_irrChar_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ G _ a ha h0
  obtain ⟨n, ρ, hρ⟩ := ha
  have hn : Nontrivial (Fin n → K) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply h0
    funext g
    have : ρ g = 0 := Subsingleton.elim _ _
    simp [hρ, Representation.character, this]
  obtain ⟨S, hS⟩ := exists_irreducible_subrepresentation ρ
  let f : Representation.IntertwiningMap S.toRepresentation ρ :=
    ⟨S.toSubmodule.subtype, fun g => by ext v; rfl⟩
  obtain ⟨c, hc, hcg⟩ := _root_.GlobalTheory.BI.exists_isChar_eq_add_of_injective K L G _ _ ρ S.toRepresentation f
    S.toSubmodule.injective_subtype
  refine ⟨_, c, (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep K L G _ S.toRepresentation).2 hS, hc, ?_⟩
  funext g
  rw [hρ, hcg]
  rfl

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIsCharEqAddOfPairNeZero
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_isChar_eq_add_of_pair_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (φ a : G → L), IsIrrChar K L φ → IsChar K L a → pair a φ ≠ 0 → ∃ c : G → L, IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ _ _ G _ _ φ a hφ ha hp
  obtain ⟨m, σ, hσ, hφ⟩ := hφ
  obtain ⟨n, ρ, ha⟩ := ha
  have hφ' : φ = fun g => algebraMap K L (σ.character g) := funext hφ
  have ha' : a = fun g => algebraMap K L (ρ.character g) := funext ha
  have h := _root_.GlobalTheory.BI.pair_character_eq_finrank K L G (Fin m → K) (Fin n → K) σ ρ
  rw [← hφ', ← ha'] at h
  have hex : ∃ f : Representation.IntertwiningMap σ ρ, f ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : Subsingleton (Representation.IntertwiningMap σ ρ) :=
      ⟨fun x y => (hne x).trans (hne y).symm⟩
    apply hp
    rw [h, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  obtain ⟨f, hf⟩ := hex
  haveI := hσ
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  obtain ⟨c, hc, hc'⟩ := _root_.GlobalTheory.BI.exists_isChar_eq_add_of_injective K L G (Fin n → K) (Fin m → K) ρ σ f hi
  refine ⟨c, hc, funext fun g => ?_⟩
  rw [Pi.add_apply, ha g, hφ g, hc' g]

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsMonomialBasisAbelianByPrimePower
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_monomial_basis_of_isCompl {k : Type} [Field k] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (U U' : Submodule k V) (h : IsCompl U U')
    (hU : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V))
    (hU' : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U'), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  obtain ⟨n, b, hb⟩ := hU
  obtain ⟨n', b', hb'⟩ := hU'
  let B := (b.prod b').map (Submodule.prodEquivOfIsCompl U U' h)
  have h1 : ∀ i, B (Sum.inl i) = (b i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  have h2 : ∀ i, B (Sum.inr i) = (b' i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  refine ⟨n + n', B.reindex finSumFinEquiv, fun g i => ?_⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · obtain ⟨j, c, hj⟩ := hb g i
    refine ⟨finSumFinEquiv (Sum.inl j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h1, hj]
  · obtain ⟨j, c, hj⟩ := hb' g i
    refine ⟨finSumFinEquiv (Sum.inr j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h2, hj]

theorem exists_monomial_basis_of_abByP : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → (Nat.card G : k) ≠ 0 → ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n), ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  intro k _
  have key : ∀ (m : ℕ) (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k],
      Nat.card G + Module.finrank k V = m → AbByP G → (Nat.card G : k) ≠ 0 →
      ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
        ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro G _ _ V _ _ _ ρ _ hm hG hcard
    by_cases h0 : Module.finrank k V = 0
    · exact ⟨0, Module.finBasisOfFinrankEq k V h0, fun g i => i.elim0⟩
    by_cases hirr : ρ.IsIrreducible
    · rcases finrank_eq_one_or_imprimitive k G V ρ hG hirr with h1 | ⟨T, W, hT, hW, hind, hsup⟩
      · let b := Module.finBasisOfFinrankEq k V h1
        refine ⟨1, b, fun g i => ⟨0, b.repr (ρ g (b i)) 0, ?_⟩⟩
        have := b.sum_repr (ρ g (b i))
        rw [Fin.sum_univ_one] at this
        exact this.symm
      · refine exists_monomial_basis_of_imprimitive k G V ρ T W hind hsup ?_
        let σ : Subrepresentation (ρ.comp T.subtype : Representation k T V) :=
          ⟨W, fun t w hw => hW t t.2 w hw⟩
        have hlt : Nat.card T < Nat.card G := by
          have := T.card_le_card_group
          have h2 : Nat.card T ≠ Nat.card G := fun H => hT (Subgroup.eq_top_of_card_eq T H)
          omega
        have hle : Module.finrank k W ≤ Module.finrank k V := Submodule.finrank_le W
        have hc : (Nat.card T : k) ≠ 0 := by
          intro H
          obtain ⟨d, hd⟩ := T.card_subgroup_dvd_card
          apply hcard
          rw [hd, Nat.cast_mul, H, zero_mul]
        obtain ⟨n, b, hb⟩ := ih _ (by omega) T W σ.toRepresentation rfl (AbByP.subgroup G T hG) hc
        refine ⟨n, b, fun t ht i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb ⟨t, ht⟩ i
        exact ⟨j, c, congrArg Subtype.val hj⟩
    · haveI : NeZero (Nat.card G : k) := ⟨hcard⟩
      haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
      haveI : Nontrivial (Subrepresentation ρ) :=
        ⟨⊥, ⊤, fun H => (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
          (congrArg Subrepresentation.toSubmodule H)⟩
      have hex : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
        by_contra H
        push Not at H
        exact hirr ⟨fun U => by
          by_cases hU : U = ⊥
          · exact Or.inl hU
          · exact Or.inr (H U hU)⟩
      obtain ⟨U, hU0, hU1⟩ := hex
      obtain ⟨U', hUU'⟩ := exists_isCompl U
      have hcompl : IsCompl U.toSubmodule U'.toSubmodule :=
        ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot),
          codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩
      have hsub : ∀ S : Subrepresentation ρ, S ≠ ⊤ →
          ∃ (n : ℕ) (b : Module.Basis (Fin n) k S.toSubmodule), ∀ (g : G) (i : Fin n),
            ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V) := by
        intro S hS
        have hlt : Module.finrank k S.toSubmodule < Module.finrank k V :=
          Submodule.finrank_lt (fun H => hS (Subrepresentation.ext H))
        obtain ⟨n, b, hb⟩ := ih _ (by omega) G S.toSubmodule S.toRepresentation rfl hG hcard
        refine ⟨n, b, fun g i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb g i
        exact ⟨j, c, congrArg Subtype.val hj⟩
      refine exists_monomial_basis_of_isCompl ρ _ _ hcompl (hsub U hU1) (hsub U' ?_)
      rintro rfl
      exact hU0 (by simpa using hUU'.inf_eq_bot)
  intro G _ _ V _ _ _ ρ _ hG hc
  exact key _ G V ρ rfl hG hc

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZero
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem IsPrimitive.finsum_unipotentRadical_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ)
    (φ : Module.End F (Fin d → F) → ℂ) (hφ : IsPrimitive φ) (a : ℕ) (ha : 0 < a) (had : a < d) :
    ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d,
      (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)},
      φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  obtain ⟨A, H, hA, hH, hbij⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d a had.le
  have hbot : A ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hA
    omega
  have htop : A ≠ ⊤ := by
    rintro rfl
    rw [finrank_top, Module.finrank_fin_fun] at hA
    omega
  rw [← hH, ← hφ A hbot htop 1 (fun x hx => hx)]
  refine finsum_mem_eq_of_bijOn _ hbij fun u _ => ?_
  simp only [add_sub_cancel]

end GlobalTheory.CuspGL
end

