module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.DetUpdateRowDiagonal
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem det_updateRow_diagonal {R : Type} [CommRing R] {m : ℕ} (c r : Fin m → R) (i : Fin m) :
    ((Matrix.diagonal c).updateRow i r).det = (∏ j ∈ Finset.univ.erase i, c j) * r i := by
  rw [← Matrix.cramer_transpose_apply, Matrix.diagonal_transpose, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.adjugate_diagonal, Matrix.mulVec_diagonal]

theorem len_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  intro C _ v R _ _ hv ι _ L L' hL x y hx0 hx hy
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨e'⟩, rfl⟩ := hy
  haveI := isLocal_of_integers hv
  let π : ((i : Fin m) → R ⧸ Ideal.span {c i}) →ₗ[R] ((i : Fin n) → R ⧸ Ideal.span {d i}) :=
    e'.toLinearMap ∘ₗ (Submodule.factor hL) ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    e'.surjective.comp ((Submodule.factor_surjective hL).comp e.symm.surjective)
  let s : Fin m → ((i : Fin m) → R ⧸ Ideal.span {c i}) :=
    fun i => Pi.single i (1 : R ⧸ Ideal.span {c i})
  have hsp : Submodule.span R (Set.range fun i => π (s i)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := hπ z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_single c w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdiag : ∀ k, ∑ i, Matrix.diagonal c k i • π (s i) = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, ← map_smul, single_smul_self c k, map_zero]
    · intro i _ hi
      rw [Matrix.diagonal_apply_ne' _ hi, zero_smul]
    · simp
  have key : ∀ T : Matrix (Fin m) (Fin m) R, (∀ k, ∑ i, T k i • π (s i) = 0) →
      v (algebraMap R C T.det) ≤ ∏ i, v (algebraMap R C (d i)) := by
    intro T hT
    have h := det_mem_span_prod n d m _ hsp T hT
    rw [Ideal.mem_span_singleton] at h
    have h2 := hv.le_of_dvd h
    rwa [map_prod, map_prod] at h2
  refine ⟨?_, fun hxy => le_antisymm hL fun l hl => ?_⟩
  · have := key _ hdiag
    rwa [Matrix.det_diagonal, map_prod, map_prod] at this
  · set w := e (Submodule.Quotient.mk l) with hw
    have hπw : π w = 0 := by
      have : (Submodule.Quotient.mk l : (ι → R) ⧸ L') = 0 := (Submodule.Quotient.mk_eq_zero _).2 hl
      simp [π, hw, this]
    have hw0 : w = 0 := by
      funext i
      have hrel : ∑ k, (Quotient.out (w k) : R) • π (s k) = 0 := by
        rw [← hπw]
        set_option synthInstance.maxHeartbeats 100000 in
          conv_rhs => rw [eq_sum_single c w, map_sum]
        simp only [map_smul, s]
      have h := key ((Matrix.diagonal c).updateRow i fun k => (Quotient.out (w k) : R)) (by
        intro k
        by_cases hk : k = i
        · subst hk
          simpa only [Matrix.updateRow_self] using hrel
        · simpa only [Matrix.updateRow_ne hk] using hdiag k)
      rw [det_updateRow_diagonal, ← hxy, map_mul, map_mul, map_prod, map_prod,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at h
      have hne : ∏ j ∈ Finset.univ.erase i, v (algebraMap R C (c j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ =>
          Finset.prod_ne_zero_iff.1 hx0 j (Finset.mem_univ j)
      have h2 := le_of_mul_le_mul_left h (pos_iff_ne_zero.2 hne)
      have h3 := hv.dvd_of_le h2
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out] at h3
      exact h3
    have : (Submodule.Quotient.mk l : (ι → R) ⧸ L) = 0 := e.injective (by rw [← hw, hw0, map_zero])
    exact (Submodule.Quotient.mk_eq_zero _).1 this

end PositivityTheory.HtPt.Rh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowEqSelf
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Teich

theorem eq_of_pow_eq_self {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (q : ℕ)
    (hq : (q : IsLocalRing.ResidueField O) = 0) {x y : O} (hx : x ^ q = x) (hy : y ^ q = y)
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hgeom := geom_sum₂_mul x y q
  rw [hx, hy] at hgeom
  have hS : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) = 1 := by
    have hmul : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) * (x - y) = 1 * (x - y) := by
      rw [hgeom, one_mul]
    exact mul_right_cancel₀ hsub hmul
  have hres := congrArg (IsLocalRing.residue O) hS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one] at hres
  simp only [map_mul, map_pow, ← h] at hres
  rw [geom_sum₂_self, hq, zero_mul] at hres
  exact zero_ne_one hres

theorem card_eq_zero {O : Type} [CommRing O] [IsLocalRing O] {F : Type} [Field F] [Fintype F]
    (σ : F →+* IsLocalRing.ResidueField O) :
    ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 := by
  rw [← map_natCast σ, FiniteField.cast_card_eq_zero, map_zero]

theorem exists_lift {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {F : Type} [Field F]
    [Fintype F] (ζ : O) (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1))
    (σ : F →+* IsLocalRing.ResidueField O) (a : F) :
    ∃ x : O, x ^ Fintype.card F = x ∧ IsLocalRing.residue O x = σ a := by
  have hQ1 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 := ⟨Fintype.card F - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel] at hζ
  haveI : NeZero m := ⟨by omega⟩
  have hQres := PositivityTheory.HtPt.Teich.card_eq_zero (O := O) σ
  have hfix : ∀ k : ℕ, (ζ ^ k) ^ Fintype.card F = ζ ^ k := by
    intro k
    rw [hm, pow_succ, ← pow_mul, mul_comm k m, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hprim : IsPrimitiveRoot (IsLocalRing.residue O ζ) m := by
    refine ⟨?_, ?_⟩
    · rw [← map_pow, hζ.pow_eq_one, map_one]
    · intro l hl
      apply hζ.dvd_of_pow_eq_one
      apply PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQres (hfix l) (one_pow _)
      rw [map_pow, hl, map_one]
  by_cases ha : a = 0
  · refine ⟨0, zero_pow (by omega), ?_⟩
    rw [ha, map_zero, map_zero]
  · have hpow := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hm, Nat.add_sub_cancel] at hpow
    have h1 : (σ a) ^ m = 1 := by rw [← map_pow, hpow, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, hfix i, by rw [map_pow, hi]⟩

theorem glue_teich : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p := by
  intro O _ _ _ F _ _ p _ _ ζ hζ σ
  have hQ : ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 :=
    PositivityTheory.HtPt.Teich.card_eq_zero σ
  have huniq : ∀ {x y : O}, x ^ Fintype.card F = x → y ^ Fintype.card F = y →
      IsLocalRing.residue O x = IsLocalRing.residue O y → x = y :=
    fun hx hy h => PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQ hx hy h
  have hfixχ : ∀ (χ : F →*₀ O) (a : F), χ a ^ Fintype.card F = χ a := fun χ a => by
    rw [← map_pow, FiniteField.pow_card]
  refine ⟨?_, ?_⟩
  · choose L hL hLres using PositivityTheory.HtPt.Teich.exists_lift ζ hζ σ
    let χ : F →*₀ O :=
      { toFun := L
        map_zero' := huniq (hL 0) (zero_pow Fintype.card_ne_zero) (by rw [hLres, map_zero, map_zero])
        map_one' := huniq (hL 1) (one_pow _) (by rw [hLres, map_one, map_one])
        map_mul' := fun a b => huniq (hL (a * b)) (by rw [mul_pow, hL a, hL b])
          (by rw [hLres, map_mul, map_mul, hLres, hLres]) }
    refine ⟨χ, hLres, fun χ' hχ' => ?_⟩
    exact MonoidWithZeroHom.ext fun a => huniq (hfixχ χ' a) (hL a) ((hχ' a).trans (hLres a).symm)
  · intro σ' χ χ' hσ' hχ hχ' a
    refine huniq (hfixχ χ' a) (by rw [← pow_mul, mul_comm p, pow_mul, hfixχ χ a]) ?_
    rw [hχ', hσ', map_pow, hχ]

end PositivityTheory.HtPt.Teich
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FinClosure
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem fin_closure : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.EssFiniteType ℤ A] (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L) := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  let A₀ := Algebra.EssFiniteType.subalgebra ℤ A
  let S := Algebra.EssFiniteType.submonoid ℤ A
  have hS : ∀ a : A, ∃ u s : A₀, IsUnit (s : A) ∧ a * s = u := fun a => by
    obtain ⟨⟨u, s⟩, e⟩ := IsLocalization.surj S a
    exact ⟨u, s, IsLocalization.map_units A s, e⟩
  have : FaithfulSMul A₀ K := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((IsFractionRing.injective A K).comp Subtype.val_injective)
  have : IsFractionRing A₀ K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨u, s, hs, e⟩ := hS a
    obtain ⟨v, t, ht, e'⟩ := hS b
    refine ⟨u * t, v * s, ?_⟩
    have h1 : algebraMap A K s ≠ 0 := (hs.map _).ne_zero
    have h2 : algebraMap A K t ≠ 0 := (ht.map _).ne_zero
    show _ = algebraMap A K (u * t) / algebraMap A K (v * s)
    rw [← e, ← e']
    simp only [map_mul]
    rw [mul_assoc, mul_assoc, mul_comm (algebraMap A K t), mul_div_mul_right _ _ (mul_ne_zero h1 h2)]
  have hfin : Module.Finite A₀ (integralClosure A₀ L) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.proof A₀ K L
  obtain ⟨g, hg⟩ : (Subalgebra.toSubmodule (integralClosure A₀ L)).FG := Module.Finite.iff_fg.1 hfin
  refine (Module.Finite.iff_fg (N := Subalgebra.toSubmodule (integralClosure A L))).2 ⟨g, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 fun y hy => ?_
    have h : y ∈ Subalgebra.toSubmodule (integralClosure A₀ L) := hg ▸ Submodule.subset_span hy
    exact IsIntegral.tower_top (R := A₀) h
  · intro y hy
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization S y (hy : IsIntegral A y)
    have h : m • y ∈ Submodule.span A₀ (g : Set L) := by
      rw [hg]
      exact hm
    have h' : (m.1 : A) • y ∈ Submodule.span A (g : Set L) := Submodule.span_le_restrictScalars A₀ A _ h
    obtain ⟨w, hw⟩ := (IsLocalization.map_units A m).exists_left_inv
    have := Submodule.smul_mem _ w h'
    have hw' : w * (m.1 : A) = 1 := hw
    rwa [smul_smul, hw', one_smul] at this

end PositivityTheory.HtPt.Mb
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FinrankWAddConj
section
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem eigQuot_lattice {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (ρ : 𝓞 E →+* Module.End C Ω) (σ : E →+* C) (X : Submodule O Ω) (hX : X.IsLattice C) :
    (latIn (eigQuot ρ σ X) (eigSp ρ σ)).IsLattice C := by
  let f : Ω →ₗ[O] eigSp ρ σ :=
    ((eigProj ρ σ).codRestrict (eigSp ρ σ) (LatBasic.eigProj_mem ρ σ)).restrictScalars O
  have hmap : latIn (eigQuot ρ σ X) (eigSp ρ σ) = X.map f := by
    ext x
    change (∃ y ∈ X, eigProj ρ σ y = (x : Ω)) ↔ ∃ y ∈ X, f y = x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, Subtype.ext h⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, congrArg Subtype.val h⟩
  haveI : IsFractionRing O C := hv.isFractionRing
  rw [hmap]
  exact Submodule.IsLattice.of_fg C (hX.fg.map f)

theorem pt_om_block : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω) (σ : E →+* C), P.omHT σ ≤ P.omRec σ ∧ (∀ x ∈ P.omRec σ, κ • x ∈ P.omHT σ) ∧ (latIn (P.omHT σ) (P.Ωsp σ)).IsLattice C ∧ (latIn (P.omRec σ) (P.Ωsp σ)).IsLattice C := by
  intro C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ
  refine ⟨Submodule.map_mono ?_, ?_, eigQuot_lattice hv _ _ _ (PtBasic.om'_lattice P),
    eigQuot_lattice hv _ _ _ P.om_lat.toIsLattice⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact P.ht_mem x hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, e⟩ := P.κ_mem y hy
    exact ⟨κ • y, ⟨x, hx, e⟩, map_smul _ _ _⟩

section

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem e_eigProj (hc : ∀ x, c (c x) = x) (σ : E →+* C) {x : V} (hx : x ∈ eigSp P.ρ σ) (y : V) :
    P.e x (eigProj P.ρ (σ.comp c.toRingHom) y) = P.e x y := by
  have h : ∀ a : 𝓞 E, P.e x (P.ρ a y) = σ (c (a : E)) * P.e x y := by
    intro a
    have h1 := P.adj (RingOfIntegers.mapRingEquiv c a) x y
    have h2 : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      ext; exact hc _
    rw [h2, LatBasic.mem_eigSp.1 hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul,
    ← mul_assoc]
  rw [← Finset.sum_mul]
  have : ∑ k, (σ.comp c.toRingHom) (dualInt E k) * σ (c ((RingOfIntegers.basis E k : 𝓞 E) : E)) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one (σ.comp c.toRingHom), ← LatBasic.sum_dualInt_mul, map_sum]
    simp
  rw [this, one_mul]

theorem finrank_eigSp [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (eigSp P.ρ σ) = N := by
  obtain ⟨h1, d, -, -, h2⟩ := exists_diff_generator C v O hv E σ
  obtain ⟨-, -, h3, h4⟩ := SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d
    hv.hom_inj h1 h2 P.free
  rw [← h4, finrank_span_eq_card h3, Fintype.card_fin]

theorem finrank_W_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Ωsp σ) = N := by
  haveI := PtBasic.finite_V P
  let f := P.ht ∘ₗ (eigSp P.ρ σ).subtype
  have h := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range f = P.Ωsp σ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change P.ht x ∈ eigSp _ _
      rw [← LatBasic.eigProj_of_mem x.2, PtBasic.ht_eigProj]
      exact LatBasic.eigProj_mem _ _ _
    · intro y hy
      obtain ⟨x, rfl⟩ := PtBasic.ht_surjective P y
      refine ⟨⟨_, LatBasic.eigProj_mem P.ρ σ x⟩, ?_⟩
      change P.ht (eigProj P.ρ σ x) = _
      rw [PtBasic.ht_eigProj, LatBasic.eigProj_of_mem hy]
  have hk : finrank C (LinearMap.ker f) = finrank C (P.Wsp σ) := by
    rw [← Submodule.finrank_map_subtype_eq, LinearMap.ker_comp, Submodule.map_comap_subtype,
      inf_comm]
    rfl
  rw [hr, hk, finrank_eigSp P hv] at h
  omega

theorem finrank_W_add_conj [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Wsp (σ.comp c.toRingHom)) = N := by
  haveI := PtBasic.finite_V P
  set τ := σ.comp c.toRingHom
  let B : eigSp P.ρ σ →ₗ[C] Module.Dual C (eigSp P.ρ τ) :=
    (P.e.domRestrict₁₂ (eigSp P.ρ σ) (eigSp P.ρ τ))
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have : (x : V) = 0 := P.nondeg _ fun y => by
      rw [PtBasic.e_skew, ← e_eigProj P hc σ x.2, neg_eq_zero]
      exact congrArg (fun φ => φ ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩) (LinearMap.mem_ker.1 hx)
    exact Subtype.ext this
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, finrank_eigSp P hv, finrank_eigSp P hv])).1 hinj
  let W₁ : Submodule C (eigSp P.ρ σ) := P.W.comap (eigSp P.ρ σ).subtype
  let W₂ : Submodule C (eigSp P.ρ τ) := P.W.comap (eigSp P.ρ τ).subtype
  have hW : W₁ = W₂.dualAnnihilator.comap B := by
    ext x
    rw [Submodule.mem_comap (f := B), Submodule.mem_dualAnnihilator]
    change P.ht x = 0 ↔ _
    rw [P.lagr]
    refine ⟨fun h w hw => h w hw, fun h y hy => ?_⟩
    rw [← e_eigProj P hc σ x.2]
    refine h ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩ ?_
    change P.ht (eigProj P.ρ τ y) = 0
    rw [PtBasic.ht_eigProj, hy, map_zero]
  have e1 : finrank C W₁ = finrank C W₂.dualAnnihilator := by
    rw [← (LinearEquiv.ofBijective B ⟨hinj, hsurj⟩).finrank_map_eq W₁, hW]
    exact congrArg (fun U : Submodule C (Module.Dual C (eigSp P.ρ τ)) => finrank C U)
      (Submodule.map_comap_eq_of_surjective hsurj _)
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W₂
  have e3 : ∀ s : E →+* C, finrank C (P.W.comap (eigSp P.ρ s).subtype) = finrank C (P.Wsp s) := by
    intro s
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]
    rfl
  rw [← e1, finrank_eigSp P hv, e3, e3] at e2
  omega

theorem finrank_Ω_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Ωsp σ) + finrank C (P.Ωsp (σ.comp c.toRingHom)) = N := by
  have h1 := finrank_W_add_Ω P hv σ
  have h2 := finrank_W_add_Ω P hv (σ.comp c.toRingHom)
  have h3 := finrank_W_add_conj P hv hc σ
  omega

end

end PositivityTheory.HtPt.Gb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem dom_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' i f hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := RegAtDom.map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, RegAtDom.genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := RegAtDom.genMap_stalkMap hd q hq hp s
    have hone : genMap ξ' ⟨q, hq⟩ (1 - (f.stalkMap q).hom s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hv, ht, mul_inv_cancel₀ h0, sub_self]
    have hu : IsUnit ((f.stalkMap q).hom s) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((f.stalkMap q).hom s * t) with h | h
      · exact isUnit_of_mul_isUnit_left h
      · have h' := h.map (genMap ξ' ⟨q, hq⟩)
        rw [hone] at h'
        exact absurd h' not_isUnit_zero
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

theorem dom_comp {X X₁ X₂ : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂}
    {f : X₁ ⟶ X} {g : X₂ ⟶ X₁} {i : Ω →+* Ω₁} {k : Ω₁ →+* Ω₂} (hf : Dominates ξ₁ ξ f i)
    (hg : Dominates ξ₂ ξ₁ g k) : Dominates ξ₂ ξ (g ≫ f) (k.comp i) := by
  unfold Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem iso_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X₁ X₂ : Scheme.{0}) (Ω' : Type) [Field Ω'] (i : Ω →+* Ω') (p : Cpt ξ), (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g i → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → NormAt ξ₂ g i p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω') ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω') → NormAt ξ₁ f i p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω') p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω) → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω) p₁) → IsoAt ξ₂ (g ≫ f) (RingHom.id Ω) p) := by
  intro X Ω _ ξ X₁ X₂ Ω' _ i p
  refine ⟨fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_⟩
  · have hr : ∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → regAt ξ p = regAt ξ₁ p₁ := fun p₁ h => by
      rw [hf.regAt_eq p₁ h, Subring.map_id]
    refine ⟨fun q hq => ?_, ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q
      rw [hr ⟨_, h⟩ hq]
      exact (hn ⟨_, h⟩ hq).exists_max q rfl
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      rw [hr p₁ h₁]
      intro P hP
      obtain ⟨q, ⟨hq, hq'⟩, hqu⟩ := (hn p₁ h₁).existsUnique P hP
      refine ⟨q, ⟨(congrArg f hq).trans h₁, hq'⟩, fun q' hq'' => hqu q' ⟨?_, hq''.2⟩⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq''.1)
  · have hr : ∀ (q : Cpt ξ₂) (p₁ : Cpt ξ₁), g q.1 = p₁.1 → f p₁.1 = p.1 → regAt ξ₂ q = regAt ξ₁ p₁ :=
      fun q p₁ h h' => by rw [(hn p₁ h').regAt_eq q h, Subring.map_id]
    refine ⟨fun q hq => ?_, fun P hP => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.id_comp] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [hr q ⟨_, h⟩ rfl hq]
      exact hf.exists_max ⟨_, h⟩ hq
    · obtain ⟨p₁, ⟨h₁, h₁'⟩, hu⟩ := hf.existsUnique P hP
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, ⟨(congrArg f hq).trans h₁, (hr q p₁ hq h₁).trans h₁'⟩, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ ⟨hq'.1, (hr q' ⟨_, h⟩ rfl hq'.1).symm.trans hq'.2⟩)
  · refine ⟨?_, fun q hq => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, (congrArg f hq).trans h₁, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq')
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [(hn ⟨_, h⟩ hq).regAt_eq q rfl, Subring.map_id, hf.regAt_eq ⟨_, h⟩ hq]

end PositivityTheory.HtPt.Mb
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDefs
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

structure PairHost {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
    (H : Host E) (H' : Host E') where

  ψ : 𝓞 E' →+* Matrix (Fin 2) (Fin 2) (𝓞 E)

  σ : 𝓞 E' ≃+* 𝓞 E'
  bar : ∀ a i j, ψ (H'.bar a) i j = H.bar (ψ a j i)
  w0 : ψ H'.w0 = Matrix.scalar (Fin 2) H.w0
  conj : ∀ a, ψ (σ a) * Matrix.diagonal ![1, -1] = Matrix.diagonal ![1, -1] * ψ a
  rt : σ H'.rt = H'.rt
  chars : ∀ (k : Type) [Field k] [CharZero k] (τ τ' : 𝓞 E' →+* k), τ H'.rt = τ' H'.rt →
    τ' = τ ∨ τ' = τ.comp σ.toRingHom

end PositivityTheory.HtPt.Kftwo
end
end

