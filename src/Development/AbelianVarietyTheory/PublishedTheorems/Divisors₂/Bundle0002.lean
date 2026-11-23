module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
section
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Published

noncomputable def sqrtNegNat (p : ℕ) : ℂ := (Real.sqrt p : ℂ) * Complex.I

def IsIntegersLattice (p : ℕ) (L : PeriodPair) : Prop :=
  ∀ z : ℂ, z ∈ L.lattice ↔ z ∈ ℚ⟮sqrtNegNat p⟯ ∧ IsIntegral ℤ z

section Reduction

variable {F : Type} [Field F] [NumberField F]

def HasGoodReductionOutside (p : ℕ) (A : WeierstrassCurve F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∉ v.asIdeal →
    ∃ C : VariableChange F, (C • A).HasGoodReduction (v.valuationSubringAtPrime F)

def HasMinimalDiscriminant (A : WeierstrassCurve F) (D : F) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F),
    ∃ (C : VariableChange F) (u : (v.valuationSubringAtPrime F)ˣ),
      (C • A).IsMinimal (v.valuationSubringAtPrime F) ∧
        (C • A).Δ = ((u : v.valuationSubringAtPrime F) : F) * D

end Reduction

def IsGoodCMCurve (p : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F) : Prop :=
  ∃ (_ : NumberField F) (_ : A.IsElliptic) (L : PeriodPair), IsIntegersLattice p L ∧
    F = ℚ⟮(latticeCurve L).j⟯ ∧ (A.j : ℂ) = (latticeCurve L).j ∧ HasGoodReductionOutside p A

def CMCurveGoodOutsidePrimeSt : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → 3 < p →
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (A : WeierstrassCurve F),
      IsGoodCMCurve p F A ∧ HasMinimalDiscriminant A (-(p : F) ^ 3)

section Lattice

theorem sqrtNegNat_sq (p : ℕ) : sqrtNegNat p ^ 2 = -(p : ℂ) := by
  unfold sqrtNegNat
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  push_cast
  ring

theorem latticeCurve_j_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    (latticeCurve L).j = (latticeCurve L').j := by
  have hG : ∀ n, L.G n = L'.G n := by
    intro n
    unfold PeriodPair.G
    rw [h]
  rw [latticeCurve_j_eq, latticeCurve_j_eq]
  simp only [PeriodPair.g₂, PeriodPair.g₃, hG]

theorem IsIntegersLattice.j_eq {p : ℕ} {L L' : PeriodPair} (h : IsIntegersLattice p L)
    (h' : IsIntegersLattice p L') : (latticeCurve L).j = (latticeCurve L').j := by
  apply latticeCurve_j_congr
  ext z
  rw [h z, h' z]

variable {p : ℕ} {K : Type} [Field K] [NumberField K]

theorem isTotallyComplex_of_sq_eq_neg (hp : 0 < p) {x : K} (hx : x ^ 2 = -(p : K)) :
    IsTotallyComplex K := by
  refine ⟨fun v => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h1
  have h2 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

variable [Algebra K ℂ]

private theorem algebraMap_rat_ne_sqrtNegNat (hp : 0 < p) (q : ℚ) : algebraMap ℚ ℂ q ≠ sqrtNegNat p := by
  intro hq
  have h1 := sqrtNegNat_sq p
  rw [← hq, eq_ratCast] at h1
  have h3 : ((q ^ 2 : ℚ) : ℂ) = ((-(p : ℚ) : ℚ) : ℂ) := by
    push_cast
    exact h1
  have h4 := Rat.cast_injective h3
  have h5 : (0 : ℚ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg q]

private theorem finrank_adjoin_sqrtNegNat_eq_two (hp : 0 < p) : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by
      simp [sqrtNegNat_sq]⟩
  rw [IntermediateField.adjoin.finrank hint]
  have hle : (minpoly ℚ (sqrtNegNat p)).natDegree ≤ 2 := by
    have hd := minpoly.degree_le_of_ne_zero ℚ (sqrtNegNat p)
      (Polynomial.X_pow_add_C_ne_zero two_pos (p : ℚ)) (by simp [sqrtNegNat_sq])
    rw [Polynomial.degree_X_pow_add_C two_pos] at hd
    exact Polynomial.natDegree_le_of_degree_le hd
  have hne : (minpoly ℚ (sqrtNegNat p)).natDegree ≠ 1 := by
    intro h1
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact algebraMap_rat_ne_sqrtNegNat hp q hq
  have hpos := minpoly.natDegree_pos hint
  omega

theorem mem_adjoin_sqrtNegNat_iff (hp : 0 < p) (h2 : Module.finrank ℚ K = 2) {x : K}
    (hx : x ^ 2 = -(p : K)) (z : ℂ) :
    z ∈ ℚ⟮sqrtNegNat p⟯ ↔ ∃ y : K, algebraMap K ℂ y = z := by
  let φ : K →ₐ[ℚ] ℂ := (algebraMap K ℂ).toRatAlgHom
  have hxs : sqrtNegNat p ^ 2 = φ x ^ 2 := by
    rw [sqrtNegNat_sq, ← map_pow, hx, map_neg, map_natCast]
  have hsE : sqrtNegNat p ∈ φ.fieldRange := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxs with h | h
    · exact AlgHom.mem_fieldRange.mpr ⟨x, h.symm⟩
    · exact AlgHom.mem_fieldRange.mpr ⟨-x, by rw [map_neg, h]⟩
  have hle : ℚ⟮sqrtNegNat p⟯ ≤ φ.fieldRange := IntermediateField.adjoin_simple_le_iff.mpr hsE
  have hE : Module.finrank ℚ φ.fieldRange = 2 := by
    rw [← h2]
    exact (AlgEquiv.ofInjectiveField φ).toLinearEquiv.finrank_eq.symm
  have : FiniteDimensional ℚ φ.fieldRange := Module.finite_of_finrank_pos (by omega)
  have heq : ℚ⟮sqrtNegNat p⟯ = φ.fieldRange :=
    IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hE, finrank_adjoin_sqrtNegNat_eq_two hp])
  rw [heq]
  exact AlgHom.mem_fieldRange

theorem isIntegersLattice_iff (hp : 0 < p) (h2 : Module.finrank ℚ K = 2) {x : K}
    (hx : x ^ 2 = -(p : K)) (L : PeriodPair) :
    IsIntegersLattice p L ↔ IsIdealLattice (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) L := by
  let ψ : K →ₐ[ℤ] ℂ := (algebraMap K ℂ).toIntAlgHom
  have key : ∀ z : ℂ, (z ∈ ℚ⟮sqrtNegNat p⟯ ∧ IsIntegral ℤ z) ↔
      z ∈ algebraMap K ℂ '' (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
    intro z
    rw [mem_adjoin_sqrtNegNat_iff hp h2 hx z, Units.val_one]
    constructor
    · rintro ⟨⟨y, rfl⟩, hz⟩
      have hy : IsIntegral ℤ y :=
        (isIntegral_algHom_iff ψ (algebraMap K ℂ).injective).mp hz
      refine ⟨y, ?_, rfl⟩
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy
      refine ⟨⟨_, rfl⟩, ?_⟩
      exact (isIntegral_algHom_iff ψ (algebraMap K ℂ).injective).mpr r.isIntegral_coe
  unfold IsIntegersLattice IsIdealLattice
  constructor
  · intro h
    ext z
    exact (h z).trans (key z)
  · intro h z
    rw [key z]
    exact Set.ext_iff.mp h z

theorem exists_isIntegersLattice (hp : 0 < p) : ∃ L, IsIntegersLattice p L := by
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by
      simp [sqrtNegNat_sq]⟩
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := ⟨⟩
  let x : ℚ⟮sqrtNegNat p⟯ := ⟨sqrtNegNat p, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hx : x ^ 2 = -(p : ℚ⟮sqrtNegNat p⟯) := by
    apply Subtype.ext
    simp [x, sqrtNegNat_sq]
  have : IsTotallyComplex ℚ⟮sqrtNegNat p⟯ := isTotallyComplex_of_sq_eq_neg hp hx
  obtain ⟨L, hL⟩ := exists_isIdealLattice (finrank_adjoin_sqrtNegNat_eq_two hp) 1
  exact ⟨L, (isIntegersLattice_iff hp (finrank_adjoin_sqrtNegNat_eq_two hp) hx L).mpr hL⟩

end Lattice

section Consequences

variable {p : ℕ}

private theorem valuation_algebraMap_unit_eq_one' {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (w : Rˣ) :
    IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
      (algebraMap R K w) = 1 := by
  apply le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _)
  have h1 : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K w) *
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K ↑w⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [← h1]
  exact mul_le_of_le_one_right zero_le (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _)

theorem HasMinimalDiscriminant.hasGoodReductionOutside {F : Type} [Field F] [NumberField F]
    {A : WeierstrassCurve F} (h : HasMinimalDiscriminant A (-(p : F) ^ 3)) :
    HasGoodReductionOutside p A := by
  intro v hv
  obtain ⟨C, u, hmin, hΔ⟩ := h v
  refine ⟨C, { toIsMinimal := hmin, goodReduction := ?_ }⟩
  have hpu : IsUnit (p : v.valuationSubringAtPrime F) := by
    have := IsLocalization.map_units (M := v.asIdeal.primeCompl) (v.valuationSubringAtPrime F)
      ⟨(p : 𝓞 F), hv⟩
    simpa using this
  obtain ⟨w, hw⟩ := u.isUnit.mul (hpu.pow 3).neg
  have hΔ' : (C • A).Δ = algebraMap (v.valuationSubringAtPrime F) F (w : v.valuationSubringAtPrime F) := by
    rw [hw, hΔ, map_mul, map_neg, map_pow, map_natCast]
    rfl
  rw [hΔ']
  exact valuation_algebraMap_unit_eq_one' w

variable {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F}

theorem IsGoodCMCurve.numberField (h : IsGoodCMCurve p F A) : NumberField F := by
  obtain ⟨hF, -⟩ := h
  exact hF

theorem IsGoodCMCurve.isElliptic (h : IsGoodCMCurve p F A) : A.IsElliptic := by
  obtain ⟨-, hA, -⟩ := h
  exact hA

theorem IsGoodCMCurve.field_eq (h : IsGoodCMCurve p F A) {L : PeriodPair}
    (hL : IsIntegersLattice p L) : F = ℚ⟮(latticeCurve L).j⟯ := by
  obtain ⟨_, _, L₀, hL₀, hF, _⟩ := h
  rw [hF, hL₀.j_eq hL]

theorem CMCurveGoodOutsidePrimeSt.exists_isGoodCMCurve (h : CMCurveGoodOutsidePrimeSt)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) :
    ∃ (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F), IsGoodCMCurve p F A := by
  obtain ⟨F, -, A, hA, -⟩ := h p hp h4 h3
  exact ⟨F, A, hA⟩

end Consequences

section Model

end Model

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

namespace FormalAlgebraisation

def Morphisms : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃! g : X ⟶ Z, ∀ e, b e ≫ g.left = f e

def Schemes : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left),
      (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) →
      (∀ e, IsProper (Y e).hom) →
    ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) →
      RelAmple (Y 0) (N 0) →
      ∃ (X : Over (Spec (CommRingCat.of R))) (M : LB X.left) (b : ∀ e, (Y e).left ⟶ X.left),
        IsProper X.hom ∧ M.IsLB ∧ RelAmple X M ∧
        (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧
        ∀ e, LBIso (N e) (M.pull (b e))

end FormalAlgebraisation

def FormalAlgebraisation : Prop :=
  FormalAlgebraisation.Morphisms ∧ FormalAlgebraisation.Schemes

namespace FormalAlgebraisation

variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}

theorem Morphisms.existsUnique_thick (H : Morphisms) (hI : IsAdicComplete I R)
    (X Z : Over (Spec (CommRingCat.of R))) [hX : IsProper X.hom] [hZ : IsProper Z.hom]
    (f : ∀ e, (thickObj R I e X).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst X.hom (thick R I e) ≫ X.hom)
    (hc : ∀ e, thickMap R I e X ≫ f (e + 1) = f e) :
    ∃! g : X ⟶ Z, ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = f e :=
  H R I hI X Z hX inferInstance inferInstance inferInstance (fun e => thickObj R I e X)
    (fun e => thickMap R I e X) (fun e => pullback.fst X.hom (thick R I e))
    (fun _ => IsPullback.of_hasPullback _ _)
    (fun _ => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) f
    (fun e => (hf e).trans pullback.condition) hc

theorem Morphisms.hom_ext (H : Morphisms) (hI : IsAdicComplete I R)
    {X Z : Over (Spec (CommRingCat.of R))} [IsProper X.hom] [IsProper Z.hom] {g g' : X ⟶ Z}
    (h : ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = pullback.fst X.hom (thick R I e) ≫ g'.left) :
    g = g' :=
  (H.existsUnique_thick hI X Z (fun e => pullback.fst X.hom (thick R I e) ≫ g'.left)
    (fun e => by rw [Category.assoc, Over.w])
    (fun e => by
      rw [← Category.assoc]
      exact congrArg (· ≫ g'.left) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)))).unique
    h (fun _ => rfl)

theorem Morphisms.exists_iso (H : Morphisms) (hI : IsAdicComplete I R)
    {X X' : Over (Spec (CommRingCat.of R))} [hX : IsProper X.hom] [hX' : IsProper X'.hom]
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {b : ∀ e, (Y e).left ⟶ X.left}
    {b' : ∀ e, (Y e).left ⟶ X'.left}
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (hb' : ∀ e, IsPullback (b' e) (Y e).hom X'.hom (thick R I e))
    (hβ' : ∀ e, β e ≫ b' (e + 1) = b' e) :
    ∃ g : X ≅ X', (∀ e, b e ≫ g.hom.left = b' e) ∧
      ∀ g' : X ⟶ X', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom := by
  obtain ⟨g, hg, hu⟩ := H R I hI X X' hX inferInstance inferInstance inferInstance Y β b hb hβ b'
    (fun e => (hb' e).w) hβ'
  obtain ⟨k, hk, -⟩ := H R I hI X' X hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b
    (fun e => (hb e).w) hβ
  refine ⟨⟨g, k, ?_, ?_⟩, hg, hu⟩
  · exact (H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b
      (fun e => (hb e).w) hβ).unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hg, hk]) (fun e => Category.comp_id _)
  · exact (H R I hI X' X' hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b'
      (fun e => (hb' e).w) hβ').unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hk, hg]) (fun e => Category.comp_id _)

end FormalAlgebraisation

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def IrreducibleAdmissibleGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsAdmissible π

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def StandardFunctorsFiniteLength : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) (d : Fin r → ℕ),
    (∀ a, 0 < d a) →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (∑ a, d a)) k) V),
      IsSmooth π → HasFiniteLength π → HasFiniteLength (jac (m := fun a => Fin (d a)) finSigmaFinEquiv π)) ∧
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W),
      IsSmooth ρ → HasFiniteLength ρ → HasFiniteLength (parInd (m := fun a => Fin (d a)) finSigmaFinEquiv ρ)

end GlobalTheory.Published

end
end

