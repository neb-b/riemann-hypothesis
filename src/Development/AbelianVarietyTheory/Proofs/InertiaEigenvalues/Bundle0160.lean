module

public import Mathlib
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHeightSqLintegralLtTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0152
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TamePairing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwist
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.CyclotomicH2Bound

open GlobalTheory.ShapeNeg

theorem cycK_eq_of_prim {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (n : ℕ)
    (g : Formalism.GaloisCohomology.GK p K) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) (a : ℕ)
    (ha : g ζ = ζ ^ a) : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = (a : ZMod (p ^ n)) := by
  have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have h1 : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [h1, ha] at hsp
  have h3 : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) =
      (PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]) := rfl
  rw [h3]
  set b := ((PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]))
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
  have hz : ζ ^ ((a : ℤ) - (b.val : ℤ)) = 1 := by
    rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
  have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
  have h0 : (((a : ℤ) - (b.val : ℤ) : ℤ) : ZMod (p ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hd
  push_cast at h0
  rw [ZMod.natCast_zmod_val] at h0
  exact (sub_eq_zero.1 h0).symm

theorem exists_prim (p : ℕ) [Fact p.Prime] (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
  HasEnoughRootsOfUnity.exists_primitiveRoot _ _

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem finite_quot [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) (k : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ k}) := by
  have hI : Ideal.span {ϖ} = IsLocalRing.maximalIdeal O :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ).symm
  haveI : Finite (O ⧸ Ideal.span {ϖ}) := by
    rw [hI]; exact (inferInstance : Finite (IsLocalRing.ResidueField O))
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

theorem lev_cyclic {M : Type} [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] Formalism.NG.KO O)
    {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    ∃ x₀ : Lev M (ϖ ^ n), ∀ y : Lev M (ϖ ^ n), ∃ t : O, y = t • x₀ := by
  have hϖ0 : (algebraMap O (FractionRing O) ϖ) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hϖ.ne_zero
  let z₀ : FractionRing O := (algebraMap O (FractionRing O) ϖ ^ n)⁻¹
  have hk : (ϖ ^ n) • eM.symm (Submodule.Quotient.mk z₀) = 0 := by
    rw [← map_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, map_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hϖ0)]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.one_le.1 le_rfl), map_zero]
  refine ⟨Lev.mk _ hk, fun y => ?_⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (eM y.val)
  have hy := y.smul_val
  have hm : (ϖ ^ n) • (Submodule.Quotient.mk z : Formalism.NG.KO O) = 0 := by
    rw [hz, ← map_smul, hy, map_zero]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at hm
  obtain ⟨t, ht⟩ := hm
  refine ⟨t, Lev.ext ?_⟩
  rw [Lev.val_smul, Lev.val_mk, ← eM.symm_apply_apply y.val, ← hz, ← map_smul,
    ← Submodule.Quotient.mk_smul]
  congr 2
  rw [Algebra.smul_def, ht, Algebra.smul_def, map_pow, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_mul]

theorem td_nsmul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M) (k : ℕ)
    (y : M) : φ (k • y) = k • φ y := map_nsmul (show M →ₗ[R] R from φ) k y
theorem td_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x - y) = φ x - φ y := (show M →ₗ[R] R from φ).map_sub x y
theorem td_add {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x + y) = φ x + φ y := (show M →ₗ[R] R from φ).map_add x y

theorem out_smul {N : Type} [AddCommGroup N] [Module O N] {ϖ : O} (k : ℕ) {z : N}
    (hz : (ϖ ^ k) • z = 0) (t : O) : (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out • z = t • z := by
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t := Ideal.Quotient.mk_out _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
  rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hz, smul_zero]

theorem h2_bounded_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hLTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ ε hε e M _ _ eM ρ hρ σ₀ hσ hcont
  have hw : ((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1 ≠ 0 := by
    intro h0; apply hσ; ext; rw [Units.val_one]; exact sub_eq_zero.1 h0
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hpϖ
  haveI hQ := finite_quot hϖ c
  refine ⟨(p ^ c) ^ ((p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c})), ?_⟩
  intro n hn h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hkn : ∀ y : Lev M (ϖ ^ n), (ϖ ^ n) • y = 0 := fun y => Lev.ext (by
    rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  haveI : Finite (Lev M (ϖ ^ n)) := by
    haveI := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) (fun y => ?_)
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n (hkn x₀) t⟩
  obtain ⟨⟨eB⟩, -, -, -, hcup, -⟩ := hLTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)
  have hpn : ∀ y : Lev M (ϖ ^ n), ((p : O) ^ n) • y = 0 := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hr, mul_smul, hkn, smul_zero]
  obtain ⟨ζ, hζ⟩ := exists_prim p n
  obtain ⟨a₀, ha₀, hdiff⟩ := hε σ₀ n ζ hζ.pow_eq_one
  have hcyc := cycK_eq_of_prim n σ₀ hζ a₀ ha₀
  have hεy : ∀ y : Lev M (ϖ ^ n), ((ε σ₀ : Oˣ) : O) • y = (a₀ : O) • y := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hdiff
    rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hpn, smul_zero]
  have hεk : ∀ (k : ℕ) (y : Lev M (ϖ ^ n)), ((ε σ₀ : Oˣ) : O) ^ k • y = (a₀ ^ k : ℕ) • y := by
    intro k; induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ, mul_smul, hεy, ih, ← Nat.cast_smul_eq_nsmul O (a₀ ^ k),
        ← Nat.cast_smul_eq_nsmul O (a₀ ^ (k + 1)), smul_smul, Nat.cast_pow, Nat.cast_pow, ← pow_succ]
  have hinv : ∀ y : Lev M (ϖ ^ n), levRepZ p n h ρ σ₀⁻¹ y = ((ε σ₀ : Oˣ) : O) ^ e • y := by
    intro y; apply Lev.ext
    rw [levRepZ_apply, levRep_val, hρ, Lev.val_smul, map_inv, inv_pow, inv_inv, Units.val_pow_eq_pow_val]
  let A := H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id _))
  have hfix : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n))) * (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y := by
    intro a y
    have h1 := DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 a.2 σ₀) y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at h1
    rw [hinv, hεk, td_nsmul, nsmul_eq_mul, hcyc, ← mul_assoc] at h1
    have h2 : ((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n)) = (a₀ : ZMod (p ^ n)) * ((a₀ ^ e : ℕ) : ZMod (p ^ n)) := by
      push_cast; ring
    rw [h2]; exact h1
  have hkill : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((ϖ ^ c) • y) = 0 := by
    intro a y
    have hy : (ϖ ^ c) • y = (((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1) • (((u⁻¹ : Oˣ) : O) • y) := by
      rw [hu, smul_smul, mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]
    rw [hy, sub_smul, one_smul, Units.val_pow_eq_pow_val, hεk, td_sub, td_nsmul, nsmul_eq_mul, hfix,
      sub_self]
  have hkillp : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((p ^ c : ℕ) • y) = 0 := by
    intro a y
    have hy : (p ^ c : ℕ) • y = (ϖ ^ c) • ((s ^ c) • y) := by
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul, ← mul_pow, mul_comm ϖ s, hs, Nat.cast_pow]
    rw [hy, hkill]
  have hA : ∀ a : A, (p ^ c : ℕ) • a = 0 := by
    intro a; apply Subtype.ext; apply LinearMap.ext; intro y
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), Submodule.coe_smul]
    change ((p ^ c : ℕ) : ZMod (p ^ n)) •
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y = 0
    rw [Nat.cast_smul_eq_nsmul, ← td_nsmul, hkillp]
  let T := {x : ZMod (p ^ n) // (p ^ c) • x = 0}
  have hT : Nat.card T ≤ p ^ c := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsAddCyclic.card_nsmul_eq_zero_le (pow_pos (Fact.out : p.Prime).pos c)
  have hq : ∀ (a : A) (t : O), (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n)))
      ((Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀) =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (t • x₀) := by
    intro a t
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1
      (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t)))
    have h1 : (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀ = t • x₀ + (ϖ ^ c) • (r • x₀) := by
      rw [smul_smul, mul_comm (ϖ ^ c) r, hr, sub_smul, add_sub_cancel]
    rw [h1, td_add, hkill, add_zero]
  let G : A → (O ⧸ Ideal.span {ϖ ^ c} → T) := fun a q =>
    ⟨(a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (q.out • x₀), by rw [← td_nsmul, hkillp]⟩
  have hGinj : Function.Injective G := by
    intro a a' hG; apply Subtype.ext; apply LinearMap.ext; intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    have h1 := congrArg Subtype.val (congrFun hG (Ideal.Quotient.mk _ t))
    simp only [G] at h1
    rwa [hq a t, hq a' t] at h1
  haveI : Finite A := Finite.of_injective G hGinj
  have hAcard : Nat.card A ≤ (p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c}) :=
    (Nat.card_le_card_of_injective G hGinj).trans (by rw [Nat.card_fun]; exact Nat.pow_le_pow_left hT _)
  let F : H2 ((levRepZ p n h ρ).comp (MonoidHom.id _)) → (A → T) := fun f a =>
    ⟨eB (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) f a), by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), ← LinearEquiv.map_smul, ← LinearMap.map_smul,
        Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), hA a, LinearMap.map_zero, LinearEquiv.map_zero]⟩
  have hFinj : Function.Injective F := by
    intro f f' hF; apply hcup; apply LinearMap.ext; intro a; apply eB.injective
    exact congrArg Subtype.val (congrFun hF a)
  show Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id _))) ≤ _
  calc _ ≤ Nat.card (A → T) := Nat.card_le_card_of_injective F hFinj
    _ = Nat.card T ^ Nat.card A := Nat.card_fun
    _ ≤ (p ^ c) ^ Nat.card A := Nat.pow_le_pow_left hT _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos c) hAcard

end GlobalTheory.CyclotomicH2Bound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantOrbitOfInvPowCharacter
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem isLocallyConstant_orbit_of_inv_pow_character :
    ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  intro p O _ G _ _ ε hε e M _ _ ρ hρ m N hm
  have key : ∀ g g' : G,
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g' : Oˣ) : O) → ρ g m = ρ g' m := by
    intro g g' h
    have h1 : Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g) ^ e : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g') ^ e : Oˣ) : O) := by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, h]
    rw [hρ, hρ]
    generalize (ε g) ^ e = u at h1 ⊢
    generalize (ε g') ^ e = v at h1 ⊢
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h2 : ((v⁻¹ : Oˣ) : O) - ((u⁻¹ : Oˣ) : O) =
        (((u⁻¹ : Oˣ) : O) * ((v⁻¹ : Oˣ) : O) * b) * (p : O) ^ N := by
      rw [mul_assoc, hb]
      have hu : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
      have hv : ((v⁻¹ : Oˣ) : O) * (v : O) = 1 := v.inv_mul
      linear_combination (-((v⁻¹ : Oˣ) : O)) * hu + ((u⁻¹ : Oˣ) : O) * hv
    symm
    rw [← sub_eq_zero, ← sub_smul, h2, mul_smul, hm, smul_zero]
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  obtain ⟨U, hU, hg, hc⟩ := ((IsLocallyConstant.iff_exists_open _).1 (hε N)) g₀
  exact ⟨U, hU, hg, fun g hgU => key g g₀ (hc g hgU)⟩

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRelativeJacquetBlockLevi
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages GlobalTheory.InertSupp

namespace GlobalTheory.JacStagesExact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def relJacMap (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (f : σ.IntertwiningMap τ) :
    (relJacD e' σ).IntertwiningMap (relJacD e' τ) :=
  twistMap (jacquetMap f _ _ _) _

theorem relJacMap_surjective (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (relJacMap e' f) := fun y => by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem relJacMap_injective (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (relJacMap e' f) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨S, hS, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
  have hH : ∀ a, ∃ H : Subgroup (GL (Fin (d a)) k), H ≤ unipRad k (e' a) ∧
      IsCompact (H : Set (GL (Fin (d a)) k)) ∧ ∀ u ∈ S, u a ∈ H := by
    intro a
    have hN : unipRad k (e' a) = unipOf k fun i => ((blk (e' a) i).val : ℤ) :=
      unipRad_eq_unipOf k fun i j => by simp
    obtain ⟨H, hle, hc, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup k (Fin (d a)) _
      (S.image fun u => u a) (by
        intro u hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
        have hm : u' a ∈ unipRad k (e' a) := hS u' hu' a (Set.mem_univ a)
        exact hN ▸ hm)
    exact ⟨H, hle.trans hN.ge, hc, fun u hu => hSH _ (Finset.mem_image_of_mem _ hu)⟩
  choose H hle hc hSH using hH
  let H' : Subgroup (Levi k fun a => Fin (d a)) := Subgroup.pi Set.univ H
  have hc' : IsCompact (H' : Set (Levi k fun a => Fin (d a))) := by
    have : (H' : Set (Levi k fun a => Fin (d a))) = Set.pi Set.univ fun a => (H a : Set _) := rfl
    rw [this]
    exact isCompact_univ_pi hc
  have hle' : H' ≤ relUnipD k e' := fun u hu a _ => hle a (hu a (Set.mem_univ a))
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono hle'
    (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ f hf hc' (h2 H' fun u hu a _ => hSH a u hu))

theorem isSubquotient_relJacD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi k fun a => Fin (d a)) V)
    (τ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth τ → IsSubquotient σ τ → IsSubquotient (relJacD e' σ) (relJacD e' τ) := by
  intro k _ _ _ _ s d t d' e' V W _ _ _ _ σ τ hτ h
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  exact (IsSubquotient.of_surjective _ (relJacMap_surjective e' f hf)).trans
    (.of_injective _ (relJacMap_injective e' hτ ι Subtype.val_injective))

end GlobalTheory.JacStagesExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimit
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LTwoLemma
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem u_locallyConstant (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    IsLocallyConstant (fun z => Ψ (wS A.K * nS z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨U, hU, hinv⟩ := h.1
  have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
  have ht : Tendsto (fun y : A.K => y - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  filter_upwards [ht hU] with y hy
  simp only [Set.mem_preimage] at hy
  have he : wS A.K * nS y = (wS A.K * nS z) * nS (y - z) := by
    rw [mul_assoc]; congr 1; apply Subtype.ext
    show !![(1 : A.K), y; 0, 1] = !![1, z; 0, 1] * !![1, y - z; 0, 1]
    rw [Matrix.mul_fin_two]; simp
  rw [he]
  apply hinv
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nS, h0, hy]

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK; split_ifs <;> simp

theorem weyl_unipotent_l2_finite [Unram F E] (hB1 : type_of% _root_.GlobalTheory.JR.LamBound.main) (hB2 : type_of% _root_.GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top) (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure)
    (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ < ⊤ := by
  obtain ⟨C, hC⟩ := hB1 F E A Ψ h
  have hB := hB2 F E A μ hμ
  have h0 : ENNReal.ofReal C + 1 ≠ 0 := by simp
  have hT : ENNReal.ofReal C + 1 ≠ ⊤ := by simp
  have hle : ∀ z, ‖Ψ (wS A.K * nS z)‖ₑ ≤ (ENNReal.ofReal C + 1) *
      ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s) := by
    intro z
    simp only [ENNReal.mul_iInf_of_ne h0 hT]
    refine le_iInf₂ fun s hs => ?_
    obtain ⟨hs1, hs2, α, hα, β, hβ, he⟩ := hs
    have hb := hC z s α β hα hβ hs1 hs2 he
    calc ‖Ψ (wS A.K * nS z)‖ₑ = ENNReal.ofReal ‖Ψ (wS A.K * nS z)‖ := (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal (C * A.absK s) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * ENNReal.ofReal (A.absK s) := ENNReal.ofReal_mul' (absK_nonneg A _)
      _ ≤ _ := by gcongr; exact le_self_add
  calc ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ z, ((ENNReal.ofReal C + 1) * ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ :=
        lintegral_mono fun z => pow_le_pow_left' (hle z) 2
    _ = (ENNReal.ofReal C + 1) ^ 2 * ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hB

end GlobalTheory.JR.LTwoLemma

open GlobalTheory.JR.LTwoLemma in
theorem GlobalTheory.JR.kirillov_vanishing_l2 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd Ψ hI hlim
  have hμ : μK.IsAddHaarMeasure := hsd.1
  have hu : (fun z => Ψ (wS A.K * nS z)) = 0 :=
    _root_.GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier F E A ψ hψ μK hsd _ (u_locallyConstant A Ψ hI) (weyl_unipotent_l2_finite _root_.GlobalTheory.JR.LamBound.main _root_.GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top A μK hμ Ψ hI) hlim
  have h1 : ∀ z, Ψ (wS A.K * nS z) = 0 := fun z => congrFun hu z
  exact ⟨h1, _root_.GlobalTheory.JR.lam_flip_eq_zero F E A ψ μK hμ Ψ hI h1⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierColumnTwiceNegColumnStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  first | exact @GlobalTheory.JR.PartialInv.ptrB_ptrB | exact GlobalTheory.JR.PartialInv.ptrB_ptrB | (intros; apply GlobalTheory.JR.PartialInv.ptrB_ptrB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuCocycleCoboundaryLiftStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_cocycle_coboundary_lift : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (n : ℕ) (w : Z2 (muLoc F l 1 A)) (a : Dec (F := F) A → ZMod (l ^ (n + 1))), Continuous a → (∀ g h : Dec (F := F) A, ((cycMod F Ω l (n + 1) g : (ZMod (l ^ (n + 1)))ˣ) : ZMod (l ^ (n + 1))) * a h - a (g * h) + a g = ((l ^ n * (w.1 (g, h)).val : ℕ) : ZMod (l ^ (n + 1)))) → (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  first | exact @GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary | exact GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary | (intros; apply GlobalTheory.MuTowerInj.mk_eq_zero_of_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZeroStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (a : E'), a ≠ 0 → (∀ φ : E' →+* ℝ, 0 < φ a) → ∀ φ : E →+* ℝ, 0 < φ (Algebra.norm E a) := by
  first | exact @GlobalTheory.norm_pos_of_totallyPositive | exact GlobalTheory.norm_pos_of_totallyPositive | (intros; apply GlobalTheory.norm_pos_of_totallyPositive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_local_inv_eq_zero_of_unramified_cocycle : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  first | exact @GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | exact GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | (intros; apply GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TamePairingStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_pairing_statement : TameLocal → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → normV v ≡ 1 [MOD l ^ 1] → (∀ g : Dec (F := F) A, cycMod F Ω l 1 g = 1) → ∀ e : H2 (muLoc F l 1 A) →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1), Function.Bijective e → ∀ (M : ℕ), 1 ≤ M → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → ∀ γ φ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) (φ : G F Ω) → ∃ u : (ZMod (l ^ 1))ˣ, ∀ z y : Dec (F := F) A → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → y g = 0) → ∀ w : Z2 (muLoc F l 1 A), (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = (u : ZMod (l ^ 1)) * (z γ * y φ) := by
  first | exact @GlobalTheory.TamePairing.tame_pairing | exact GlobalTheory.TamePairing.tame_pairing | (intros; apply GlobalTheory.TamePairing.tame_pairing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKerStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B), IsOpen (f.ker : Set (v.adicCompletion F)ˣ) → IsOpen (g.ker : Set (v.adicCompletion F)ˣ) → (∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) → ∀ x, f x = g x := by
  first | exact @GlobalTheory.units_adicCompletion_hom_ext | exact GlobalTheory.units_adicCompletion_hom_ext | (intros; apply GlobalTheory.units_adicCompletion_hom_ext <;> assumption)
end

