module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforwardEqZero
section
open MulAction

theorem UpperTheory.orbitalFiber_pushforward_eq_zero :
    UpperTheory.V.Z.Sym.Glob.Fib.PushZero := by
  intro H Y _ _ H₀ k hidx htriv hk hfin
  classical
  have hout : ∀ (o : orbitRel.Quotient H Y) (y : Y),
      (Quotient.mk (orbitRel H Y) y : orbitRel.Quotient H Y) = o ↔ y ∈ orbit H o.out := by
    intro o y
    rw [← orbitRel_apply, ← Quotient.eq (r := orbitRel H Y), Quotient.out_eq]
  have hkeq : ∀ (x y : Y), y ∈ orbit H x → k y = k x := by
    rintro x y ⟨h, rfl⟩
    exact hk h x
  set S : Finset Y := hfin.toFinset with hS
  have hmem : ∀ y, y ∈ S ↔ k y ≠ 0 := by
    intro y; simp [hS]
  let q : Y → orbitRel.Quotient H Y := fun y => Quotient.mk (orbitRel H Y) y
  have h1 : ∑ᶠ y, k y = ∑ y ∈ S, k y := finsum_eq_sum k hfin
  have h2 : UpperTheory.V.Z.Sym.gq H₀ k =
      ∑ o ∈ S.image q, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ) := by
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_sum_of_support_subset
    intro o ho
    have hne : k o.out ≠ 0 := by
      intro h0
      exact ho (by simp [h0])
    simp only [Finset.coe_image]
    exact ⟨o.out, by simpa [hmem] using hne, Quotient.out_eq o⟩
  rw [h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image q) (g := q)
    (fun y hy => Finset.mem_image_of_mem q hy), Finset.sum_div]
  refine Finset.sum_congr rfl fun o ho => ?_
  obtain ⟨y₀, hy₀, hy₀o⟩ := Finset.mem_image.mp ho
  have hne : k o.out ≠ 0 := by
    rw [← hkeq o.out y₀ ((hout o y₀).mp hy₀o)]
    exact (hmem y₀).mp hy₀
  have hset : ((S.filter fun y => q y = o : Finset Y) : Set Y) = orbit H o.out := by
    ext y
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · exact fun h => (hout o y).mp h.2
    · intro h
      exact ⟨(hmem y).mpr (by rw [hkeq _ _ h]; exact hne), (hout o y).mpr h⟩
  have hcard : (S.filter fun y => q y = o).card = (stabilizer H o.out).index := by
    rw [index_stabilizer, ← hset, Set.ncard_coe_finset]
  have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
  have hmul := Subgroup.relIndex_mul_index hle
  have hsum : ∑ y ∈ S with q y = o, k y = ((stabilizer H o.out).index : ℂ) * k o.out := by
    rw [Finset.sum_congr rfl (g := fun _ => k o.out), Finset.sum_const, hcard, nsmul_eq_mul]
    intro y hy
    exact hkeq _ _ ((hout o y).mp (Finset.mem_filter.mp hy).2)
  rw [← hmul] at hidx
  have ha : ((H₀.relIndex (stabilizer H o.out) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (left_ne_zero_of_mul hidx)
  have hb : (((stabilizer H o.out).index : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hidx)
  rw [hsum, ← hmul, Nat.cast_mul]
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberRepresentatives
section
private theorem reps_setoid {G : Type} (r : Setoid G) (Y : Finset G) (x₀ : G)
    (hY : ∀ g, ∃ y ∈ Y, r y g) :
    ∃ (n : ℕ) (x : Fin (n + 1) → G), x 0 = x₀ ∧ (∀ i, x i = x₀ ∨ x i ∈ Y) ∧
      (∀ i j, r (x i) (x j) → i = j) ∧ ∀ g, ∃ i, r (x i) g := by
  classical
  have hσ : ∀ q : Quotient r, ∃ y ∈ Y, Quotient.mk r y = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨y, hy, h⟩ := hY g
      exact ⟨y, hy, Quotient.sound h⟩
  choose σ hσY hσ using hσ
  haveI : Finite (Quotient r) := by
    refine Finite.of_injective (fun q => (⟨σ q, hσY q⟩ : Y)) ?_
    intro a b h
    have h' : σ a = σ b := congrArg Subtype.val h
    rw [← hσ a, ← hσ b, h']
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r x₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (Quotient r) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Quotient r)).ne'
  let e₀ : Fin (n + 1) ≃ Quotient r := (Finite.equivFinOfCardEq hn).symm
  let e : Fin (n + 1) ≃ Quotient r := e₀.trans (Equiv.swap (e₀ 0) (Quotient.mk r x₀))
  have he : e 0 = Quotient.mk r x₀ := by simp [e]
  let x : Fin (n + 1) → G := fun i => if i = 0 then x₀ else σ (e i)
  have hx : ∀ i, Quotient.mk r (x i) = e i := by
    intro i
    by_cases h : i = 0
    · subst h; simp [x, he]
    · simp [x, h, hσ]
  refine ⟨n, x, by simp [x], ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = 0
    · left; simp [x, h]
    · right; simp [x, h, hσY]
  · intro i j h
    apply e.injective
    rw [← hx, ← hx]
    exact Quotient.sound h
  · intro g
    refine ⟨e.symm (Quotient.mk r g), Quotient.exact ?_⟩
    rw [hx]; simp

theorem UpperTheory.orbitalFiber_representatives :
    UpperTheory.V.Z.Sym.Glob.Fib.Reps := by
  intro Γ G _ _ ι S U' Y x₀ hS hY
  let r : Setoid G :=
    { r := fun a b => ∃ γ, ∃ s ∈ S, ∃ u ∈ U', b = ι γ * s * a * u
      iseqv :=
        { refl := fun a => ⟨1, 1, S.one_mem, 1, U'.one_mem, by simp⟩
          symm := by
            rintro a b ⟨γ, s, hs, u, hu, rfl⟩
            refine ⟨γ⁻¹, ι γ * s⁻¹ * (ι γ)⁻¹, hS.conj_mem _ (S.inv_mem hs) _, u⁻¹, U'.inv_mem hu, ?_⟩
            rw [map_inv]; group
          trans := by
            rintro a b c ⟨γ, s, hs, u, hu, rfl⟩ ⟨γ', s', hs', u', hu', rfl⟩
            refine ⟨γ' * γ, (ι γ)⁻¹ * s' * (ι γ)⁻¹⁻¹ * s,
              S.mul_mem (hS.conj_mem _ hs' _) hs, u * u', U'.mul_mem hu hu', ?_⟩
            rw [map_mul]; group } }
  obtain ⟨n, x, h0, h1, h2, h3⟩ := reps_setoid r Y x₀ (by
    intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, h⟩ := hY g
    exact ⟨y, hy, γ, s, hs, u, hu, h⟩)
  refine ⟨n, x, h0, h1, fun i j γ s hs u hu h => h2 i j ⟨γ, s, hs, u, hu, h⟩, fun g => ?_⟩
  obtain ⟨i, γ, s, hs, u, hu, h⟩ := h3 g
  exact ⟨i, γ, s, hs, u, hu, h⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberStabilizerFinite
section
namespace UpperTheory

theorem orbitalFiber_stabilizer_finite : UpperTheory.V.Z.Sym.Glob.Fib.StabFin := by
  intro H G _ _ S U U' ι x hS hidx hfin
  let ψ : H →* G := (MulAut.conj x⁻¹).toMonoidHom.comp (S.subtype.comp ι)
  have hψ : ∀ h, ψ h = x⁻¹ * ι h * x := fun h => by simp [ψ]
  have hB : (U' ⊓ S).comap ψ = U'.comap ψ := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, and_iff_left_iff_imp]
    intro _
    rw [hψ]
    simpa using hS.conj_mem _ (ι h).2 x⁻¹
  have h1 : (U.comap ψ).relIndex (U'.comap ψ) ≠ 0 := by
    rw [← hB]
    exact Subgroup.relIndex_comap_ne_zero ψ hidx
  have hA : Finite (U.comap ψ) := by
    have : ((U.comap ψ : Subgroup H) : Set H).Finite := by
      convert hfin using 1
      ext h
      simp [hψ]
    exact this.to_subtype
  have hA' : Finite ((U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Finite.of_injective (fun a => (⟨a.1.1, a.2⟩ : U.comap ψ)) (fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : U.comap ψ => (z : H)) hab)
  have hq : Finite ((U'.comap ψ) ⧸ (U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Nat.finite_of_card_ne_zero h1
  have hfB : Finite (U'.comap ψ) :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup
      (s := (U.comap ψ).subgroupOf (U'.comap ψ))).symm
  have : ((U'.comap ψ : Subgroup H) : Set H).Finite := Set.toFinite _
  convert this using 1
  ext h
  simp [hψ]

end UpperTheory
end

