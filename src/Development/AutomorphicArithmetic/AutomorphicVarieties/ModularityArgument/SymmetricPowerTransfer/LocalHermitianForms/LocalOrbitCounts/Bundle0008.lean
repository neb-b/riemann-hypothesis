module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OrbEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SemiSemi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ExistsRho
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinUq
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Loc.finUq : UpperTheory.V.Z.Sym.Loc.FinUq := by
  intro O K _ _ _ _ _ Δ τ L c d m h δ ι P hM
  refine ⟨orbEq O K Δ τ L c d m h δ ι P hM, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := finU O K Δ τ L c d m h δ ι P hM
    refine ⟨s, fun y hy => hs y ?_⟩
    by_contra hn
    exact hy (by simp [UpperTheory.V.Z.Sym.Glob.one, hn])
  · intro y
    refine QuotientGroup.induction_on y ?_
    intro y
    have e : MulAction.stabilizer (U3 Δ) (QuotientGroup.mk y : U3 Δ ⧸ KU O Δ)
        = (KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom := by
      ext g
      simp [MulAction.mem_stabilizer_iff, QuotientGroup.eq, mul_assoc]
      constructor
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
    rw [e]
    exact stabU O K Δ τ L c d m h δ ι P hM y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.hsLaw : UpperTheory.V.Z.Sym.Loc.HsLaw := by
  intro O K _ _ _ _ _ Δ L
  have h2 : (2 : K) ≠ 0 := L.two_ne
  haveI := L.frac
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    unfold hs
    by_cases h1 : ∃ a b : K, a ^ 2 - x * b ^ 2 = y
    · rw [if_pos h1, if_pos (nm_symm hx h2 h1 hy)]
    · have h1' : ¬ ∃ a b : K, a ^ 2 - y * b ^ 2 = x := fun h => h1 (nm_symm hy h2 h hx)
      rw [if_neg h1, if_neg h1']
  · rintro x y ⟨U, s, hs0, rfl⟩ ⟨V, t, -, rfl⟩
    obtain ⟨a, b, hab⟩ := L.nm_unit U V
    have hK := congrArg (algebraMap O K) hab
    simp only [map_sub, map_mul, map_pow] at hK
    unfold hs
    rw [if_pos]
    refine ⟨algebraMap O K a * t, algebraMap O K b * t / s, ?_⟩
    rw [← hK]
    field_simp
  · intro D hD hsq
    by_cases he : EvenVal O D
    · obtain ⟨U, s, hs0, rfl⟩ := he
      obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hUsq : ¬ IsSquare (algebraMap O K U) := by
        rintro ⟨r, hr⟩
        exact hsq ⟨r * s, by rw [hr]; ring⟩
      have hp0 : algebraMap O K p ≠ 0 := by
        intro h0
        apply hp.ne_zero
        apply IsFractionRing.injective O K
        rw [h0, map_zero]
      refine ⟨algebraMap O K p, hp0, ?_⟩
      unfold hs
      rw [if_neg]
      rintro ⟨a, b, hab⟩
      have e : a ^ 2 - algebraMap O K ↑U * (s * b) ^ 2 = algebraMap O K p := by
        rw [← hab]; ring
      apply L.not_even hp
      rw [← e]
      exact L.even_of_norm U hUsq (by rw [e]; exact hp0)
    · obtain ⟨ε, hε⟩ := ramUnit O K Δ L D hD he
      refine ⟨algebraMap O K ε, ?_, hε⟩
      intro h0
      rw [h0] at hε
      unfold hs at hε
      rw [if_pos ⟨0, 0, by ring⟩] at hε
      norm_num at hε
  · rintro D x hD ⟨r, rfl⟩
    have hr : r ≠ 0 := by
      rintro rfl
      simp at hD
    unfold hs
    rw [if_pos]
    refine ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
    field_simp
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapRam
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem inv_norm {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K} (L : IsLoc O Δ)
    {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

theorem UpperTheory.V.Z.Sym.Loc.kapRam : UpperTheory.V.Z.Sym.Loc.KapRam := by
  intro O K _ _ _ _ _ Δ τ L c d m h hτ hodd
  obtain ⟨a, rfl⟩ := hτ
  have h2 := L.two
  have hu : IsUnit (2 - a) := by
    by_contra hn
    apply hodd
    have hp : IsUnit (2 + a) := by
      by_contra hp
      have hsum := IsLocalRing.nonunits_add hn hp
      apply hsum
      have e : (2 - a) + (2 + a) = 2 * 2 := by ring
      rw [e]
      exact h2.mul h2
    refine ⟨hp.unit, 1, one_ne_zero, ?_⟩
    simp [map_add (f := _), map_ofNat]
  obtain ⟨v, hv⟩ := hu
  have hv' : algebraMap O K (v : O) = 2 - algebraMap O K a := by
    rw [hv, map_sub, map_ofNat]
  have hex : ∃ u : Oˣ, algebraMap O K ↑u = 2 - algebraMap O K a := ⟨v, hv'⟩
  refine ⟨hex, ?_⟩
  have hD : ¬ EvenVal O (algebraMap O K a ^ 2 - 4) := by
    rintro ⟨u, s, hs0, hus⟩
    apply hodd
    refine ⟨-(u * v⁻¹), s, hs0, ?_⟩
    have hw : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hv'] at hw
    simp only [Units.val_neg, Units.val_mul, map_neg, map_mul]
    linear_combination (-(algebraMap O K ((v⁻¹ : Oˣ) : O))) * hus + (-(2 + algebraMap O K a)) * hw
  have hreg := h.reg
  obtain ⟨ε, hε⟩ := ramUnit O K Δ L _ hreg hD
  have hinv : ∀ t ∈ NE (algebraMap O K a), ∀ x : Kˣ,
      lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) :=
    fun t ht x => inv_norm L h t ht x
  have hg : ((Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) = algebraMap O K ε := rfl
  obtain ⟨_, h2', _⟩ := sumShift O K Δ _ L hreg (fun y : Kˣ => lcount O c d ((y : K) • m)) hinv
    (Units.map (algebraMap O K : O →* K) ε)
  have hshift : ∀ x : Kˣ, lcount O c d (((x * Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) • m)
      = lcount O c d ((x : K) • m) := by
    intro x
    rw [Units.val_mul, hg, mul_comm, mul_smul]
    exact splitM O K Δ _ L c d _ (datSmul K Δ _ c d m h x) ⟨a, rfl⟩ hex ε
  simp only [hshift, hg, hε] at h2'
  have h3 : kapSum O c d m = -1 * kapSum O c d m := by
    unfold kapSum
    exact h2'
  linear_combination h3 / 2
end

