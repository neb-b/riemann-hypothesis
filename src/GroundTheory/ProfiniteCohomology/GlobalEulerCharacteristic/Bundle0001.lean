module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ArtinCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open MulAction

theorem natCard_subtype_eq_sum_natCard_fiber {α β : Type*} [Finite α] [DecidableEq β] (f : α → β)
    (t : Finset β) (P : α → Prop) (hP : ∀ a, P a ↔ f a ∈ t) :
    Nat.card {a // P a} = ∑ b ∈ t, Nat.card {a // f a = b} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := t)
    (fun a ha => (hP a).1 (Finset.mem_filter.1 ha).2)]
  refine Finset.sum_congr rfl fun b hb => ?_
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨And.right, fun h => ⟨(hP a).2 (h ▸ hb), h⟩⟩

variable {Γ : Type*} [Group Γ]

theorem card_mul_card_fixedBy_quotient [Finite Γ] (D : Subgroup Γ) (x : Γ) :
    Nat.card D * Nat.card (fixedBy (Γ ⧸ D) x) = Nat.card {y : Γ // y⁻¹ * x * y ∈ D} := by
  have hP : ∀ y : Γ, y⁻¹ * x * y ∈ D ↔
      (Subgroup.groupEquivQuotientProdSubgroup (s := D) y).1 ∈ fixedBy (Γ ⧸ D) x := by
    intro y
    change _ ↔ x • (y : Γ ⧸ D) = y
    rw [MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq, smul_eq_mul, ← mul_assoc]
  let e : {y : Γ // y⁻¹ * x * y ∈ D} ≃ fixedBy (Γ ⧸ D) x × D :=
    (Subgroup.groupEquivQuotientProdSubgroup.subtypeEquiv hP).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun q => q ∈ fixedBy (Γ ⧸ D) x))
  rw [Nat.card_congr e, Nat.card_prod, mul_comm]

theorem exists_artin_relation [Finite Γ] :
    ∃ (s : Finset (Subgroup Γ)) (c : Subgroup Γ → ℤ), (∀ D ∈ s, IsCyclic D) ∧
      ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ D ∈ s, c D * Nat.card (fixedBy (Γ ⧸ D) x) := by
  classical
  have := Fintype.ofFinite (Subgroup Γ)
  let π : Subgroup Γ → Γ → ℤ := fun D x => Nat.card (fixedBy (Γ ⧸ D) x)
  let f : Subgroup Γ → Γ → ℤ := fun C x => Nat.card {y : Γ // Subgroup.zpowers (y⁻¹ * x * y) = C}
  let V : Submodule ℤ (Γ → ℤ) :=
    Submodule.span ℤ (Set.range fun D : {D : Subgroup Γ // IsCyclic D} => π D)
  have hrec : ∀ (C : Subgroup Γ) (x : Γ),
      (Nat.card C : ℤ) * π C x = ∑ D ∈ Finset.univ.filter (· ≤ C), f D x := by
    intro C x
    simp only [π, f]
    rw [← Nat.cast_mul, card_mul_card_fixedBy_quotient,
      natCard_subtype_eq_sum_natCard_fiber (fun y => Subgroup.zpowers (y⁻¹ * x * y))
        (Finset.univ.filter (· ≤ C)) _ (fun y => by simp [Subgroup.zpowers_le])]
    push_cast
    rfl
  have htot : ∀ x : Γ, (Nat.card Γ : ℤ) = ∑ C, f C x := by
    intro x
    have h := natCard_subtype_eq_sum_natCard_fiber (fun y : Γ => Subgroup.zpowers (y⁻¹ * x * y))
      Finset.univ (fun _ => True) (by simp)
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))] at h
    simp only [f]
    exact_mod_cast h
  have hcyc : ∀ C : Subgroup Γ, ¬ IsCyclic C → f C = 0 := by
    intro C hC
    funext x
    simp only [f, Pi.zero_apply, Nat.cast_eq_zero]
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨y, hy⟩
    exact hC (hy ▸ inferInstance)
  have hmem : ∀ C, f C ∈ V := by
    intro C
    refine WellFounded.induction (C := fun C => f C ∈ V) wellFounded_lt C ?_
    intro C ih
    by_cases hC : IsCyclic C
    · have hsplit : Finset.univ.filter (· ≤ C) = insert C (Finset.univ.filter (· < C)) := by
        ext D
        simp [le_iff_eq_or_lt]
      have hnot : C ∉ Finset.univ.filter (· < C) := by simp
      have heq : f C = (Nat.card C : ℤ) • π C - ∑ D ∈ Finset.univ.filter (· < C), f D := by
        funext x
        have h := hrec C x
        rw [hsplit, Finset.sum_insert hnot] at h
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        linarith
      rw [heq]
      exact V.sub_mem (V.smul_mem _ (Submodule.subset_span ⟨⟨C, hC⟩, rfl⟩))
        (V.sum_mem fun D hD => ih D (Finset.mem_filter.1 hD).2)
    · rw [hcyc C hC]
      exact V.zero_mem
  have hconst : (fun _ : Γ => (Nat.card Γ : ℤ)) ∈ V := by
    have h : (fun _ : Γ => (Nat.card Γ : ℤ)) = ∑ C, f C := by
      funext x
      rw [Finset.sum_apply]
      exact htot x
    rw [h]
    exact V.sum_mem fun C _ => hmem C
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hconst
  refine ⟨Finset.univ.filter (fun D => IsCyclic D), fun D => if h : IsCyclic D then c ⟨D, h⟩ else 0,
    fun D hD => (Finset.mem_filter.1 hD).2, fun x => ?_⟩
  have h := congrFun hc x
  rw [Finset.sum_apply] at h
  rw [← h, Finset.sum_subtype (Finset.univ.filter (fun D => IsCyclic D))
    (p := fun D : Subgroup Γ => IsCyclic D) (by simp)]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  show c D * π D x = (if h : IsCyclic (D : Subgroup Γ) then c ⟨D, h⟩ else 0) * π D x
  rw [dite_eq_left D.2]

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PermLatticeCharacter
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Module Representation

universe uk uG uU uV uW

variable {k : Type uk} {G : Type uG} [Field k] [Group G]

theorem character_prod {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g :=
  LinearMap.trace_prodMap' (ρ g) (σ g)

noncomputable def equivProdRight {U : Type uU} {V : Type uV} {W : Type uW} [AddCommGroup U]
    [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (τ : Representation k G U) {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : (τ.prod ρ).Equiv (τ.prod σ) :=
  Representation.Equiv.mk ((LinearEquiv.refl k U).prodCongr e.toLinearEquiv) fun g =>
    LinearMap.ext fun x => Prod.ext rfl (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x.2)

theorem exists_equiv_prod_of_injective [Finite G] [NeZero (Nat.card G : k)] {U : Type uU}
    {W : Type uW} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    {τ : Representation k G U} {σ : Representation k G W} (f : IntertwiningMap τ σ)
    (hf : Function.Injective f) :
    ∃ Z : Subrepresentation σ, Nonempty ((τ.prod Z.toRepresentation).Equiv σ) := by
  obtain ⟨Z, hZ⟩ := exists_isCompl f.range
  have hZ' : IsCompl (LinearMap.range f.toLinearMap) Z.toSubmodule :=
    ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hZ.disjoint)),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hZ.codisjoint))⟩
  let e : (U × Z.toSubmodule) ≃ₗ[k] W :=
    ((LinearEquiv.ofInjective f.toLinearMap hf).prodCongr (LinearEquiv.refl k Z.toSubmodule)).trans
      (Submodule.prodEquivOfIsCompl _ _ hZ')
  have he : ∀ u z, e (u, z) = f u + z := fun u z => by
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨Z, ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_⟩⟩
  obtain ⟨u, z⟩ := x
  have h1 : f (τ g u) = σ g (f u) := LinearMap.congr_fun (f.isIntertwining' g) u
  show e (τ g u, Z.toRepresentation g z) = σ g (e (u, z))
  rw [he, he, map_add (f := _), h1]
  rfl

theorem nonempty_equiv_of_character_eq [CharZero k] [Finite G] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  suffices H : ∀ n : ℕ, ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W), finrank k V = n →
      ρ.character = σ.character → Nonempty (ρ.Equiv σ) from H _ ρ σ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ ρ σ hn h
  have : Fintype G := Fintype.ofFinite G
  have hG : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : NeZero (Nat.card G : k) := ⟨hG⟩
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hG
  have hdim : finrank k W = finrank k V := by
    have h1 := congrFun h 1
    rw [Representation.char_one, Representation.char_one] at h1
    exact_mod_cast h1.symm
  by_cases hV : finrank k V = 0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (hdim.trans hV)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hdim.symm) fun g =>
      LinearMap.ext fun _ => Subsingleton.elim _ _⟩

  have hex : ∃ m, ∃ Y : Subrepresentation ρ, Y ≠ ⊥ ∧ finrank k Y.toSubmodule = m := by
    refine ⟨finrank k V, ⊤, fun h0 => hV ?_, finrank_top k V⟩
    have h1 : (⊤ : Submodule k V) = ⊥ := congrArg Subrepresentation.toSubmodule h0
    rw [← finrank_top k V, h1, finrank_bot]
  classical
  obtain ⟨Y, hY0, hYm⟩ := Nat.find_spec hex
  have hmin : ∀ Y' : Subrepresentation ρ, Y' ≠ ⊥ →
      finrank k Y.toSubmodule ≤ finrank k Y'.toSubmodule := fun Y' hY' => by
    rw [hYm]
    exact Nat.find_min' hex ⟨Y', hY', rfl⟩
  have hYsub : Y.toSubmodule ≠ ⊥ := fun h0 => hY0 (Subrepresentation.toSubmodule_injective h0)

  let ι : IntertwiningMap Y.toRepresentation ρ :=
    ⟨Y.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hι0 : ι ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hYsub
    intro h0
    exact hy0 (congrArg (fun φ : IntertwiningMap Y.toRepresentation ρ => φ ⟨y, hy⟩) h0)

  have hHom : finrank k (IntertwiningMap Y.toRepresentation σ) =
      finrank k (IntertwiningMap Y.toRepresentation ρ) := by
    have h1 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation ρ
    have h2 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation σ
    rw [h] at h1
    exact_mod_cast h2.symm.trans h1
  have hpos : 0 < finrank k (IntertwiningMap Y.toRepresentation σ) :=
    hHom ▸ Module.finrank_pos_iff_exists_ne_zero.2 ⟨ι, hι0⟩
  obtain ⟨f, hf0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos

  have hfinj : Function.Injective f := by
    let K : Submodule k Y.toSubmodule := LinearMap.ker f.toLinearMap
    by_cases hK : K = ⊥
    · exact LinearMap.ker_eq_bot.1 hK
    exfalso
    let K' : Subrepresentation ρ := ⟨K.map Y.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      refine ⟨Y.toRepresentation g y, ?_, rfl⟩
      have h1 := LinearMap.congr_fun (f.isIntertwining' g) y
      have hy' : f.toLinearMap y = 0 := hy
      show f.toLinearMap (Y.toRepresentation g y) = 0
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
      rw [h1, hy', map_zero]⟩
    have hK'dim : finrank k K'.toSubmodule = finrank k K := Submodule.finrank_map_subtype_eq _ _
    have hKpos : finrank k K ≠ 0 := fun h0 => hK (Submodule.finrank_eq_zero.1 h0)
    have hK'0 : K' ≠ ⊥ := by
      intro h0
      have h1 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h0
      rw [h1, finrank_bot] at hK'dim
      exact hKpos hK'dim.symm
    have h1 := hmin K' hK'0
    have h2 : finrank k K = finrank k Y.toSubmodule :=
      le_antisymm (Submodule.finrank_le K) (hK'dim ▸ h1)
    have hKtop : K = ⊤ := Submodule.eq_top_of_finrank_eq h2
    exact hf0 (IntertwiningMap.ext (LinearMap.ker_eq_top.1 hKtop))

  obtain ⟨V', ⟨eV⟩⟩ := exists_equiv_prod_of_injective ι hιinj
  obtain ⟨W', ⟨eW⟩⟩ := exists_equiv_prod_of_injective f hfinj
  have hchar : V'.toRepresentation.character = W'.toRepresentation.character := by
    funext g
    have h1 := congrFun (char_iso eV) g
    have h2 := congrFun (char_iso eW) g
    have h3 := congrFun h g
    rw [character_prod] at h1 h2
    linear_combination h1 - h2 + h3
  have hYpos : 0 < finrank k Y.toSubmodule :=
    Nat.pos_of_ne_zero fun h0 => hYsub (Submodule.finrank_eq_zero.1 h0)
  have hlt : finrank k V'.toSubmodule < n := by
    have h1 := eV.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at h1
    omega
  obtain ⟨e'⟩ := ih _ hlt V'.toRepresentation W'.toRepresentation rfl hchar
  exact ⟨eV.symm.trans ((equivProdRight Y.toRepresentation e').trans eW)⟩

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

def funDiagRepresentation (X : Type*) [MulAction G X] (ρ : Representation k G V) :
    Representation k G (X → V) where
  toFun g :=
    { toFun := fun F x => ρ g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (ρ g) _ _
      map_smul' := fun c F => funext fun x => map_smul (ρ g) c _ }
  map_one' := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp [mul_smul]

abbrev funDiagRep {k G : Type u} [CommRing k] [Group G] (X : Type u) [MulAction G X]
    (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (funDiagRepresentation X A.ρ)

end GroundTheory.ProfCoh
end

