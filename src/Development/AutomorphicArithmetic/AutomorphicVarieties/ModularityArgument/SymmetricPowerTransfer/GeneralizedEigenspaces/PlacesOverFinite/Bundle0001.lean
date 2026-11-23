module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0051
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.ChiUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Pl

private theorem root_one {l : ℕ} [Fact l.Prime] {x : Qbar l} {n : ℕ} (hn : ¬ l ∣ n) (hx : x ^ n = 1)
    (h : ‖x - 1‖ < 1) : x = 1 := by
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero l)
  have hnorm : ‖x‖ = 1 := by
    have h1 : ‖x‖ ^ n = 1 := by rw [← norm_pow, hx, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hn0).1 h1
  have hpow : ∀ i : ℕ, ‖x ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simpa using zero_lt_one
    | succ i ih =>
      have e : x ^ (i + 1) - 1 = x ^ i * (x - 1) + (x ^ i - 1) := by ring
      rw [e]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ih)
      rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]
      exact h
  have hnn : ‖(n : Qbar l)‖ = 1 := by
    have h1 : ‖(n : ℚ_[l])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)
    have h2 : ((n : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by simp
    rw [h2, PadicAlgCl.norm_extends, h1]
  have hS : ∑ i ∈ Finset.range n, x ^ i ≠ 0 := by
    intro h0
    have e : (n : Qbar l) = -∑ i ∈ Finset.range n, (x ^ i - 1) := by
      rw [Finset.sum_sub_distrib, h0]; simp
    have hlt : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (x ^ i - 1)‖ < 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ih (hpow m))
    rw [e, norm_neg] at hnn
    exact (hlt n).ne hnn
  have : (x - 1) * ∑ i ∈ Finset.range n, x ^ i = 0 := by
    rw [mul_geom_sum, hx, sub_self]
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hS)

private theorem cyc_one (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have e1 := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have e2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [show Chr.cls ℚ Ω (l ^ n) σ = 1 from (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ] at e2
  have e3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (e1.symm.trans e2)
  rw [ZMod.val_injective _ e3]
  simp

theorem chiUnr : ChiUnr := by
  intro Ω _ _ _ l _ c N _ e ψ χ' j hord hcong M hM L _ _ _ A hA s hs
  have hv : ¬ A.valuation (l : Ω) < 1 ∧ ¬ A.valuation (N : Ω) < 1 := by
    obtain ⟨k, rfl⟩ := hM
    have hn : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).2 (natCast_mem A n)
    rw [Nat.cast_mul, Nat.cast_mul, map_mul, map_mul] at hA
    refine ⟨fun h => hA ?_, fun h => hA ?_⟩
    · exact mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le h (hn N)) (hn k)
    · exact mul_lt_one_of_lt_of_le (lt_of_le_of_lt (mul_le_of_le_one_left' (hn l)) h) (hn k)
  have hσ : galEmb ℚ L Ω s ∈ Ine (F := ℚ) A := ⟨hs.1, fun x hx => hs.2 x hx⟩
  set σ := galEmb ℚ L Ω s with hσdef
  have hz : cycZ ℚ Ω l σ = 1 := cyc_one Ω l A hv.1 hσ
  have hcyc : cycBar ℚ Ω l σ = 1 := by simp [cycBar, hz]
  have hchi : UpperTheory.V.Base.chiO ℚ Ω l c.O σ = 1 := by simp [UpperTheory.V.Base.chiO, hz]
  have hdir : Chr.dirG ℚ Ω ψ σ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply,
      show Chr.cls ℚ Ω N σ = 1 from (Chr.clsFacts ℚ Ω N).2.2.2.2 A hv.2 hσ, map_one]
  have hP : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    rw [Chr.Psi, MonoidHom.mul_apply, MonoidHom.zpow_apply, hchi, hdir, one_zpow, one_mul]
  have h := hcong σ
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hcyc, one_pow, one_mul, hP] at h
  have h' : ‖((χ' σ : (Qbar l)ˣ) : Qbar l) - 1‖ < 1 := h
  have ho : ((χ' σ : (Qbar l)ˣ) : Qbar l) ^ orderOf χ' = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply, Units.val_one]
  exact Units.ext (root_one hord ho h')

end UpperTheory.V.Z.Sym.Pl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

private theorem isPlaceOver_under {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {A : ValuationSubring Ω} {w : Plc L} (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 (Lp L))) := by
  intro x
  exact h (algebraMap _ (𝓞 L) x)

theorem UpperTheory.V.Z.Sym.Pl.linkUnr :
    UpperTheory.V.Z.Sym.Pl.LinkUnr := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ Φ k
  haveI : IsAlgClosure L Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed ℚ
      isAlgebraic := haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
        Algebra.IsAlgebraic.tower_top (K := ℚ) L }
  refine ⟨UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω fun A _ _ g hg => (k.mem_range_resP g).2 (k.unr A ⟨hg, (Pr.toUpl Ω L g).2⟩), fun w hw => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  have hM : A.valuation (M : Ω) < 1 := (Pr.natCast_place hA M).2 hw
  exact UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω A _ (isPlaceOver_under hA)
    (fun g hg => (k.mem_range_resP g).2 (k.split A hM ⟨hg, (Pr.toUpl Ω L g).2⟩)) w rfl
end

