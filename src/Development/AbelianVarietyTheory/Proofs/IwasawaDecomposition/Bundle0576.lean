module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0024
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0561
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayReg
open NumberField

theorem isDedekindDomain_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine GlobalTheory.CycAway.isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _

theorem isDedekindDomain_cycAway_of_ne_zero {n : ℕ} (hn : n ≠ 0) : IsDedekindDomain (cycAway n) := by
  haveI : NeZero n := ⟨hn⟩
  let K := CyclotomicField n ℚ
  let φ : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hz : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta n ℚ K)) n := hζ.map_of_injective φ.injective
  have he : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨k, hk, hkc⟩ := hz.eq_pow_of_pow_eq_one he.pow_eq_one
  have hζk := hζ.pow_of_coprime k (hz.pow_iff_coprime (Nat.pos_of_ne_zero hn) k |>.1 (hkc ▸ he))
  have := isDedekindDomain_closure φ hζk
  rwa [map_pow, hkc] at this

theorem isDedekindDomain_cycAway (n : ℕ) : IsDedekindDomain (cycAway n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : cycAway 0 = cycAway 1 := by
      have hb : ∀ m : ℕ, m ≤ 1 → cycAway m = ⊥ := by
        intro m hm
        refine le_antisymm (Subring.closure_le.2 ?_) bot_le
        rintro _ (rfl | rfl)
        · interval_cases m <;> simp [zeta]
        · interval_cases m <;> simp
      rw [hb 0 zero_le_one, hb 1 le_rfl]
    rw [h]
    exact isDedekindDomain_cycAway_of_ne_zero one_ne_zero
  · exact isDedekindDomain_cycAway_of_ne_zero hn.ne'

end GlobalTheory.CycAwayReg

namespace GlobalTheory.CycAwayReg

end GlobalTheory.CycAwayReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumMulEqOfSumToRealEq
section
noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section OfCover

variable {X : Type} [AddCommGroup X]

theorem sum_mul_eq_of_sum_toReal_eq {L ι κ : Type} [AddCommGroup L] [Fintype ι] [Fintype κ]
    {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X} (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {u : ι → L} {w : κ → L}
    {a : ι → ℝ} {b : κ → ℝ} (h : ∑ i, a i • toReal (j (u i)) = ∑ k, b k • toReal (j (w k))) :
    ∑ i, a i * (ℓ (u i) : ℝ) = ∑ k, b k * (ℓ (w k) : ℝ) := by
  have := sum_mul_eq_zero_of_sum_toReal hj ℓ (β := Sum.elim u w) (c := Sum.elim a (-b)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, h, add_neg_cancel])
  rw [Fintype.sum_sum_type] at this
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
  linarith

theorem toReal_injective : Function.Injective (toReal : LinearMap.BilinForm ℤ X → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply] at this
    exact_mod_cast this

end OfCover

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.LineNorm.IsTanBasis t x e) (φ : R →+* S) :
    GlobalTheory.LineNorm.IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

theorem ext_uniq (hX : X.IsSeparated) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem mem_latDR_iff (hX : X.IsSeparated) {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis t x e) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (φ : R →+* ↥(intO C)) (cf : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ spMap φ ≫ x) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hb := isTanBasis_map t he φ
  have hv : ∀ i, IsTanAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) := fun i => by
    rw [← bc_bc]; exact GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hb.1 i)
  have hxC : spMap (intO C).subtype ≫ spMap φ ≫ x = spMap ((intO C).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  constructor
  · rintro ⟨xO, hx, vO, hvO, rfl⟩ i
    obtain rfl := ext_uniq hX C _ _ hx
    obtain ⟨a, ha, -⟩ := he.2 (↥(intO C)) φ vO hvO
    have hc := GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha
    simp only [bc_bc] at hc
    have ht := GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hvO
    rw [hxC] at ht hc hw
    have e1 := (he.2 C _ _ ht).unique hw hc
    rw [e1]
    exact (a i).2
  · intro hc
    obtain ⟨wO, hwO, hcO⟩ := GlobalTheory.FlagEmb.exists_comb t hb.1 fun i => (⟨cf i, hc i⟩ : ↥(intO C))
    refine ⟨_, rfl, wO, hwO, ?_⟩
    have hb' := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [bc_bc] at hb'
    exact GlobalTheory.FlagEmb.comb_unique t hv hb' hw

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

end GlobalTheory.HTPres
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm.Chart

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet

section Alg

theorem exists_minor_ne_zero {K : Type} [Field K] {m g k : ℕ} (a : Fin m → Fin g → K) (ha : LinearIndependent K a)
    (hk : k ≤ m) : ∃ s, minor a hk s ≠ 0 := by
  classical
  let M : Matrix (Fin k) (Fin g) K := Matrix.of fun l i => a (Fin.castLE hk l) i
  have hM : LinearIndependent K M.row := ha.comp _ (Fin.castLE_injective hk)
  obtain ⟨κ, b, hb, hsp, hli⟩ := exists_linearIndependent' K M.col
  have : Finite κ := Finite.of_injective b hb
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = k := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix, Fintype.card_fin]
  let e : Fin k ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (M.submatrix id (b ∘ e)).col := hli.comp e e.injective
  exact ⟨b ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h1)).ne_zero⟩

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : φ (minor a hk s) = minor (fun l i => φ (a l i)) hk s := by
  rw [minor, RingHom.map_det]; rfl

end Alg

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) {Z : Scheme.{0}}
    (v : Sp (DualNumber R) ⟶ Z) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ v = spMap (dualMap (ψ.comp φ)) ≫ v := by
  rw [← Category.assoc, spMap_comp']
  congr 2
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m g : ℕ}

theorem comb_iff {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) (a : Fin m → R)
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ l, a l • tanOf (hu l))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ l, a l • tanOf (hu l))).left := (isComb_iff (fun l => tanOf (hu l)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  exact ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans
    ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h0)

theorem comb_tan {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x u a w) : IsTanAtG t x w :=
  (comb_iff hu a w).1 h ▸ isTan_tv _

theorem sum_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) (c : Fin m → R) :
    ∑ l, c l • tanOf (hu l) = ∑ i, (∑ l, c l • a l) i • tanOf (he i) := by
  have h : ∀ l, tanOf (hu l) = ∑ i, a l i • tanOf (he i) := fun l => tan_ext ((comb_iff he _ _).1 (ha l))
  simp only [h, Finset.smul_sum, Finset.sum_apply, Finset.sum_smul, Pi.smul_apply, smul_smul, smul_eq_mul]
  exact Finset.sum_comm

theorem comb_comb {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) {c : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (hw : IsCombAtG t x u c w) : IsCombAtG t x e (∑ l, c l • a l) w := by
  have hu := fun l => comb_tan he (ha l)
  rw [comb_iff he, ← sum_comb he hu ha]
  exact (comb_iff hu _ _).1 hw

end Tan

section Geo

theorem ringHom_ext {S : Scheme.{0}} {V : S.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    {φ φ' : Γ(S, V) →+* R} (h : spMap φ ≫ hV.fromSpec = spMap φ' ≫ hV.fromSpec) : φ = φ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

variable {F : Type} [Field F] [NumberField F] {Y : Var F}


end Geo

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)}

theorem coord_map {R S : Type} [CommRing R] [CommRing S] (α : A →+* R) (ψ : R →+* S) {a : Fin g → R}
    {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) a w) :
    IsCombAtG t (spMap (ψ.comp α) ≫ x₀) (fun i => spMap (dualMap (ψ.comp α)) ≫ e i) (fun i => ψ (a i))
      (spMap (dualMap ψ) ≫ w) := by
  have := GlobalTheory.LatDRFree.comb_map t ψ h
  simp only [dual_comp] at this
  rwa [← Category.assoc, spMap_comp'] at this

end Coord

end GlobalTheory.LineNorm.Chart

end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionFunctionalEquation
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem feq_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e : ℕ, U.ExpandsAt e k σ f) → ∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + k • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) k α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) k mu α) κ.left z J).val := by
  intro R _ _ _ hCN G _ _ hSA D A U k hk σ f hE mu α T κ y z J hJ
  have hR : AdmBase R (maximalIdeal R) := admissibleBase_of_completeNormalLocalCharZero hCN
  have := hR.1
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((k : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ (pullback.fst G.hom (jK R)))
  have hU := U.expand k hk
  obtain ⟨E, hsE, -⟩ := hU.1 s
  obtain ⟨g, hg, hgE⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D A G U.toUnifPre k σ s
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero R _ hR D A G U.toUnifPre k 2 ![1, -1] ![σ, σ] ![f, g]
    (fun i => by fin_cases i; exacts [hE, hg])).1 (fun j => by
      simp [Fin.sum_univ_two, Out.scal])
  obtain rfl : f = g := funext fun α => SecOps.sec_ext fun j => by
    have := H α j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  let ρ : T ⟶ DegPre.BF D.toPre (FractionRing R) := lift κ y
  have ρ₁ : ρ ≫ fst _ _ = κ := lift_fst _ _
  have ρ₂ : ρ ≫ DegPre.prB D.toPre (FractionRing R) = y := lift_snd _ _
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) GlobalTheory.globalFns_holds k mu α
  have vu := hv u hu hc _ ρ z J hJ
  have hrel := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (E.fe mu α u hu hc) _ ρ.left z J hJ
  rw [← SectionScalarValuation.secScal_sval (hgE _) _ z hJ, ← SectionScalarValuation.secScal_sval (hgE _) _ z hJ] at hrel
  have htr : (ρ ≫ DegPre.trF D.toPre (FractionRing R) mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      y * cP D.toPre T mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ρ₂, comp_cP, comp_cP]
  rw [vu] at hrel
  rw [← htr, ← congrArg (fun q => sval (f (α + k • mu)) q.left z J) ρ₂]
  rw [ρ₁] at hrel
  simp only [Over.comp_left]
  exact hrel

end GlobalTheory.PsiCompare
end
end

