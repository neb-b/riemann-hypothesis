module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow.TwoFibres

open GlobalTheory.ZM

theorem unitS_spMap_eq {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitS_spMap_comp {o R R' : Type} [CommRing o] [CommRing R] [CommRing R'] (β : o →+* R) (i : R →+* R')
    (u : oˣ) : unitS (spMap i ≫ spMap β) u = unitOn (Units.map (i.comp β).toMonoidHom u) := by
  rw [SpreadLevel.unitS_comp, unitS_spMap_eq β]
  exact (unitS_spMap_eq i _).trans (congrArg unitOn (Units.ext rfl))

def ofLevel {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) : TObj g k PEmpty b s where
  A := P.A
  ab := P.isAb
  dim := hg ▸ P.smoothDim
  L := P.L
  isLB := P.isLB
  rigid := P.rigid
  sym := P.sym
  ample := P.ample
  ktriv := P.ktriv
  pt := levelBasis l hg
  torsion := fun i => l.torsion _
  bij := by
    intro K' _ _ x y hy
    subst hg
    haveI : NeZero k := ⟨hk.ne'⟩
    obtain ⟨c, hc⟩ := l.span K' x y hy
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
    · simp only [levelBasis_rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (c _).2]
      exact hc
    · have e := l.indep K' x (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hc.symm)
      funext i
      have := congrArg (fun d => ((d i : ℕ) : ZMod k)) e
      simpa using this
  pairing := by
    intro i j
    subst hg hze
    exact l.pairing i j
  act := fun e => e.elim
  hom := fun e => e.elim

theorem ofLevel_lab {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) (a : Ix g k) : (ofLevel hk b s P hg l hze).lab a = levelPoint l hg a := by
  subst hg
  rfl

theorem ofLevel_hasTh {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k ^ 2) (b : TBase o (k ^ 2)) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ}
    (l : Level P (k ^ 2) ze) (hze : ze = unitS s b.ζ) (w : Ix g (k ^ 2) → K)
    (h : IsThetaPt P k (levelPoint l hg) fun a => Ex.fnOf (w a)) :
    (ofLevel hk b s P hg l hze).HasTh (𝟙 _) w := by
  have hx : (fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫
      (ofLevel hk b s P hg l hze).lab a) = levelPoint l hg := by
    funext a
    have e : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; rfl
    rw [e, Category.id_comp, ofLevel_lab]
  subst hg
  exact (congrArg (fun x => IsThetaPt P k x (fun a => Ex.fnOf (w a))) hx).mpr h

theorem linComb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {m : ℕ} (x' : Fin m → (Out.baseOver S' ⟶ G'))
    (x : Fin m → (Out.baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = f ≫ (x i).left) (c : Fin m → ℕ) :
    (Out.linComb x' c).left ≫ φ = f ≫ (Out.linComb x c).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e : ∀ i, pushHom h (Out.baseOver S') (x' i) = preHom U (x i) := fun i =>
    Over.OverMorphism.ext (hx i)
  have := congrArg (fun z => z.left) ((SpreadLevel.map_linComb (pushHom h (Out.baseOver S')) x' c).trans
    ((congrArg (fun z => Out.linComb z c) (funext e)).trans (SpreadLevel.map_linComb (preHom U) x c).symm))
  exact this

end GlobalTheory.MBLow.TwoFibres

namespace GlobalTheory.MBLow

open GlobalTheory.ZM GlobalTheory.MBLow.TwoFibres

theorem exists_family_of_two_fibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  intro g n hn hodd
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨j₀, H⟩ := exists_tObj_of_veryDense hL hL2 g PEmpty (fun e => e.elim) 0 n hn hodd
  refine ⟨j₀, fun j hj o _ _ ζ W _ _ _ _ β v K₀ K₁ _ _ _ _ i₀ i₁ hW P₀ P₁ h₀ h₁ l₀ l₁ hT₀ hT₁ => ?_⟩
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hζ : IsPrimitiveRoot ζ ((n ^ j) ^ 2) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (Units.map (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv.hom.toMonoidHom).comp
      (Units.map (i₀.comp β).toMonoidHom)) l₀.prim ?_
    exact (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv).1).comp
      (Units.map_injective (i₀.comp β).injective)
  let b : TBase o ((n ^ j) ^ 2) :=
    { ζ := ζ
      unit := (Nat.cast_ne_zero.2 hk.ne').isUnit
      prim := fun K _ β' => (IsPrimitiveRoot.coe_units_iff.2 hζ).map_of_injective β'.injective }
  let t₀ := ofLevel hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm
  let t₁ := ofLevel hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm
  have hS₀ : t₀.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hS₁ : t₁.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hh₀ : t₀.HasTh (𝟙 _) (fun a => i₀ (v a)) :=
    ofLevel_hasTh hk b _ P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm _ hT₀
  have hh₁ : t₁.HasTh (𝟙 _) (fun a => i₁ (v a)) :=
    ofLevel_hasTh hk b _ P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm _ hT₁
  have hvd : VeryDense (objPrimes b (fun e : PEmpty => e.elim) 0 β v) := by
    intro q f hq hf
    rcases hW q hq with rfl | rfl
    · exact ⟨_, ⟨K₀, inferInstance, inferInstance, i₀, t₀, rfl, hS₀, hh₀⟩, hq, le_rfl, hf⟩
    · exact ⟨_, ⟨K₁, inferInstance, inferInstance, i₁, t₁, rfl, hS₁, hh₁⟩, hq, le_rfl, hf⟩
  obtain ⟨t, -, ht⟩ := H j hj o b W β v hvd
  obtain ⟨φ₀, hp₀, hL₀, hpt₀, -⟩ := ht K₀ i₀ t₀ hS₀ hh₀
  obtain ⟨φ₁, hp₁, hL₁, hpt₁, -⟩ := ht K₁ i₁ t₁ hS₁ hh₁
  haveI := t.ab.comm
  refine ⟨t.pol, t.lab, φ₀, φ₁, rfl, fun a => DenseBasis.linComb_pow_eq_one t.pt t.torsion _, hp₀, hp₁, hL₀, hL₁,
    fun a => ?_, fun a => ?_⟩
  · rw [← ofLevel_lab hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm a]
    exact linComb_push hp₀ t₀.pt t.pt hpt₀ _
  · rw [← ofLevel_lab hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm a]
    exact linComb_push hp₁ t₁.pt t.pt hpt₁ _

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.CdvrLiftCp

theorem mem_int_iff' {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem norm_p_lt_one' {p : ℕ} [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem mem_range_of_norm_le {p : ℕ} [Fact p.Prime] {W L : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (kL : L →+* ℂ_[p])
    (hW : ∀ w, ‖kL (algebraMap W L w)‖ ≤ 1) (x : L) (hx : ‖kL x‖ ≤ 1) : x ∈ Set.range (algebraMap W L) := by
  by_contra hxr
  have hx0 : x ≠ 0 := by rintro rfl; exact hxr ⟨0, map_zero _⟩
  have hunit : ∀ u : Wˣ, ‖kL (algebraMap W L u)‖ = 1 := by
    intro u
    have h1 : kL (algebraMap W L u) * kL (algebraMap W L ↑u⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a1 := hW u
    have a2 := hW ↑u⁻¹
    nlinarith [norm_nonneg (kL (algebraMap W L u)), norm_nonneg (kL (algebraMap W L ↑u⁻¹))]
  obtain ⟨y, hy⟩ : IsLocalization.IsInteger W x⁻¹ :=
    (ValuationRing.isInteger_or_isInteger W x).resolve_left (fun ⟨a, ha⟩ => hxr ⟨a, ha⟩)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hx0 (inv_eq_zero.1 hy.symm)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hxr
    refine ⟨↑u⁻¹, ?_⟩
    rw [hyu, pow_zero, mul_one] at hy
    rw [map_units_inv, hy, inv_inv]
  have hy1 : ‖kL (algebraMap W L y)‖ = 1 := by
    have h1 : kL x * kL (algebraMap W L y) = 1 := by rw [← map_mul, hy, mul_inv_cancel₀ hx0, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a2 := hW y
    nlinarith [norm_nonneg (kL x), norm_nonneg (kL (algebraMap W L y))]
  have hϖ1 : ‖kL (algebraMap W L ϖ)‖ = 1 := by
    rw [hyu, map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hy1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 hy1
  have hall : ∀ w : W, w ≠ 0 → ‖kL (algebraMap W L w)‖ = 1 := by
    intro w hw
    obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    rw [map_mul, map_mul, norm_mul, hunit, map_pow, map_pow, norm_pow, hϖ1, one_pow, one_mul]
  have hp : kL (algebraMap W L (p : W)) = (p : ℂ_[p]) := by simp
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpW : (p : W) ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hp
    exact hp0 hp.symm
  have := hall _ hpW
  rw [hp] at this
  exact absurd this (ne_of_lt norm_p_lt_one')

end GlobalTheory.CdvrLiftCp

namespace GlobalTheory.CdvrLiftCp

theorem exists_cdvr_lift : ∀ (p : ℕ) [Fact p.Prime] (T : CDVR), T.FinRes → ∀ (kO : T.V →+* 𝓞_ℂ_[p]) (k : T.Fr →+* ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L] (kL : L →+* ℂ_[p]), (∀ a, kL (algebraMap T.Fr L a) = k a) → ∃ (T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr) (ψ : L ≃+* T'.Fr) (kO' : T'.V →+* 𝓞_ℂ_[p]), T'.FinRes ∧ Function.Injective kO' ∧ (∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a)) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iF a) ∧ (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap T'.V T'.Fr a))) ∧ ∀ (A : Type) [CommRing A] (f : A →+* L), (∀ a, ‖kL (f a)‖ ≤ 1) → ∃ fO : A →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (fO a) = ψ (f a) := by
  intro p _ T hT kO k hk L _ _ _ kL hkL
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  let iF : T.Fr →+* FractionRing W := ψ.toRingHom.comp (algebraMap T.Fr L)
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := by
    intro w
    change (FractionRing.algEquiv W L).symm (algebraMap W L w) = _
    exact AlgEquiv.commutes _ w
  have hψs : ∀ w : W, ψ.symm (algebraMap W (FractionRing W) w) = algebraMap W L w := by
    intro w
    rw [← hψ, RingEquiv.symm_apply_apply]
  have hφ : ∀ a, iF (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change ψ (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, hψ]
  haveI : Algebra.IsIntegral T.V W := Algebra.IsIntegral.of_finite T.V W
  have hint : ∀ w : W, kL (algebraMap W L w) ∈ 𝓞_ℂ_[p] := by
    intro w
    have hw : IsIntegral T.V w := Algebra.IsIntegral.isIntegral w
    have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = (kL.comp (algebraMap W L)).comp (algebraMap T.V W) := by
      ext a
      change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = kL (algebraMap W L (algebraMap T.V W a))
      rw [hk, ← hkL, ← RingHom.comp_apply (algebraMap W L), ← RingHom.comp_apply (algebraMap T.Fr L), hc]
    have h1 : IsIntegral 𝓞_ℂ_[p] (kL (algebraMap W L w)) := IsIntegral.map_of_comp_eq kO _ hcomp hw
    exact (PadicComplexInt.integers p).mem_of_integral h1
  have hW : ∀ w : W, ‖kL (algebraMap W L w)‖ ≤ 1 := fun w => (mem_int_iff' _).1 (hint w)
  let kO' : W →+* 𝓞_ℂ_[p] := (kL.comp (algebraMap W L)).codRestrict 𝓞_ℂ_[p] hint
  have hkO' : ∀ w, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' w) = kL (algebraMap W L w) := fun w => rfl
  refine ⟨T', algebraMap T.V W, iF, ψ, kO', ?_, ?_, fun a => (hφ a).symm, fun a => rfl, ?_, ?_⟩
  · haveI : Finite (IsLocalRing.ResidueField T.V) := hT
    exact Module.finite_of_finite (IsLocalRing.ResidueField T.V) (M := IsLocalRing.ResidueField W)
  · intro a b hab
    have h1 := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) hab
    rw [hkO', hkO'] at h1
    exact IsFractionRing.injective W L (kL.injective h1)
  · intro a
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap W (FractionRing W) a))
    rw [hkO', hψs]
  · intro A _ f hf
    have hmem : ∀ a, f a ∈ (algebraMap W L).range := fun a => mem_range_of_norm_le kL hW (f a) (hf a)
    let e : W ≃+* (algebraMap W L).range :=
      RingEquiv.ofBijective (algebraMap W L).rangeRestrict
        ⟨fun a b h => IsFractionRing.injective W L (congrArg Subtype.val h), (algebraMap W L).rangeRestrict_surjective⟩
    refine ⟨e.symm.toRingHom.comp (f.codRestrict _ hmem), fun a => ?_⟩
    change algebraMap W (FractionRing W) (e.symm (f.codRestrict _ hmem a)) = ψ (f a)
    have h2 : algebraMap W L (e.symm (f.codRestrict _ hmem a)) = f a := by
      have h3 : e (e.symm (f.codRestrict _ hmem a)) = f.codRestrict _ hmem a := e.apply_symm_apply _
      exact congrArg Subtype.val h3
    rw [← hψ, h2]

end GlobalTheory.CdvrLiftCp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionPoint
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

set_option autoImplicit false

namespace GlobalTheory.FinDesc

theorem spField_pt_eq (K : Type) [Field K] (a b : Sp K) : a = b := by
  have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem exists_finite_subext_point : ∀ (X S : Scheme.{0}) (s : X ⟶ S), LocallyOfFiniteType s → ∀ (K₀ K : Type) [Field K₀]
    [Field K] [Algebra K₀ K], Algebra.IsAlgebraic K₀ K → ∀ (y : Sp K ⟶ X) (z : Sp K₀ ⟶ S),
    y ≫ s = spMap (algebraMap K₀ K) ≫ z → ∃ (L : IntermediateField K₀ K) (yL : Sp L ⟶ X), FiniteDimensional K₀ L ∧
      spMap (algebraMap L K) ≫ yL = y ∧ yL ≫ s = spMap (algebraMap K₀ L) ≫ z := by
  intro X S s hs K₀ K _ _ _ halg y z hyz
  classical
  let pb : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hpt : ∀ a : Sp K₀, z a = s (y pb) := fun a => by
    have e := congrArg (fun h : Sp K ⟶ S => h pb) hyz
    simp only [Scheme.Hom.comp_apply] at e
    rw [e, spField_pt_eq K₀ a]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show s (y pb) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hgV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show y pb ∈ s ⁻¹ᵁ U from hqU)
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  have hry : Set.range y ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [spField_pt_eq K a pb]
    exact hgV
  have hrz : Set.range z ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt a]
    exact hqU
  have hy₁ := IsOpenImmersion.lift_fac hV'.fromSpec y hry
  have hz₁ := IsOpenImmersion.lift_fac hU'.fromSpec z hrz
  rw [← Spec.map_preimage (IsOpenImmersion.lift hV'.fromSpec y hry)] at hy₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec z hrz)] at hz₁
  set φ := Spec.preimage (IsOpenImmersion.lift hV'.fromSpec y hry) with hφ
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec z hrz) with hψ
  have key : s.appLE U V hVU ≫ φ = ψ ≫ CommRingCat.ofHom (algebraMap K₀ K) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, hy₁, hz₁]
    exact hyz
  have hft := LocallyOfFiniteType.finiteType_appLE s hU' hV' hVU
  let _ := (s.appLE U V hVU).hom.toAlgebra
  obtain ⟨T, hT⟩ := hft.out
  let L : IntermediateField K₀ K := IntermediateField.adjoin K₀ ((T.image φ.hom : Finset K) : Set K)
  have hfin : FiniteDimensional K₀ L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
  have hmem : ∀ b : Γ(X, V), φ.hom b ∈ L := by
    intro b
    have hb : b ∈ Algebra.adjoin Γ(S, U) (T : Set Γ(X, V)) := by rw [hT]; exact Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
    | algebraMap a =>
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [RingHom.algebraMap_toAlgebra, e]
      exact L.algebraMap_mem _
    | add b c _ _ hb hc => rw [map_add (f := _)]; exact L.add_mem hb hc
    | mul b c _ _ hb hc => rw [map_mul]; exact L.mul_mem hb hc
  let φL : Γ(X, V) →+* L := φ.hom.codRestrict L hmem
  refine ⟨L, Spec.map (CommRingCat.ofHom φL : Γ(X, V) ⟶ CommRingCat.of L) ≫ hV'.fromSpec, hfin, ?_, ?_⟩
  · rw [← hy₁, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp]
    congr 1
  · have key' : s.appLE U V hVU ≫ CommRingCat.ofHom φL = ψ ≫ CommRingCat.ofHom (algebraMap K₀ L) := by
      ext a
      have e := congrArg (fun h => h.hom a) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e ⊢
      exact e
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec s hU' hV' hVU, ← Category.assoc, ← Spec.map_comp, key',
      Spec.map_comp, ← hz₁, spMap]
    simp only [Category.assoc]

end GlobalTheory.FinDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

theorem functionFieldMap_germToFunctionField {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ X') [IsDominant f] (V : X'.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) [Nonempty U]
    [Nonempty V] (s : Γ(X', V)) :
    functionFieldMap f (X'.germToFunctionField V s) = X.germToFunctionField U (f.appLE V U e s) := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hfx : f (genericPoint X) ∈ V := e hx
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') hfx, functionFieldMap_algebraMap,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx]
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply f V _ hfx s).trans
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE e) _ hx (f.app V s)).symm

theorem exists_functionFieldMap_eq_of_invariant (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W]
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q]
    (h : IsAffineQuotient ρ q) (u : X.functionFieldˣ) (hu : ∀ γ, fnAct ρ γ u = u) :
    ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  classical
  have := Fintype.ofFinite Γ
  have := h.isAffineHom
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  haveI : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := (show IsAffineOpen V from hV).preimage q
  obtain ⟨x, hx⟩ := q.denseRange.exists_mem_open V.isOpen ⟨_, hyV⟩
  haveI : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  have hst := h.preimage_le V
  haveI (γ : Γ) : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  let σ : Γ → Γ(X, q ⁻¹ᵁ V) →+* Γ(X, q ⁻¹ᵁ V) := fun γ ↦ ((ρ γ).asIso.hom.appLE _ _ (hst γ)).hom
  have hσ (γ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) :
      functionFieldMap (ρ γ).asIso.hom (algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField s) =
        algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField (σ γ s) :=
    functionFieldMap_germToFunctionField _ _ _ (hst γ) s
  have hσ1 (s : Γ(X, q ⁻¹ᵁ V)) : σ 1 s = s := by
    have e1 : (ρ 1).asIso.hom = 𝟙 X := by rw [map_one]; rfl
    change (ρ 1).asIso.hom.appLE _ _ (hst 1) s = s
    simp only [e1]
    exact congr($(X.presheaf.map_id (Opposite.op (q ⁻¹ᵁ V))) s)
  have hσmul (γ δ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : σ δ (σ γ s) = σ (γ * δ) s := by
    have e2 : (ρ (γ * δ)).asIso.hom = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom := by rw [map_mul]; rfl
    change (ρ δ).asIso.hom.appLE _ _ (hst δ) ((ρ γ).asIso.hom.appLE _ _ (hst γ) s) =
      (ρ (γ * δ)).asIso.hom.appLE _ _ (hst (γ * δ)) s
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, e2]
  set e := algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField with he_def
  have einj : Function.Injective e := IsFractionRing.injective _ _
  have hfu (δ : Γ) : functionFieldMap (ρ δ).asIso.hom (u : X.functionField) = u :=
    congrArg Units.val (hu δ)
  obtain ⟨a, t, ht, hat⟩ := IsFractionRing.div_surjective (A := Γ(X, q ⁻¹ᵁ V)) (u : X.functionField)
  have ht0 : e t ≠ 0 := by
    rw [Ne, ← map_zero e]
    exact fun h0 ↦ nonZeroDivisors.ne_zero ht (einj h0)
  let N := ∏ γ, σ γ t
  have hN (δ : Γ) : σ δ N = N := by
    simp only [N, map_prod, hσmul]
    exact Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun _ ↦ rfl)
  have hNe : e N ≠ 0 := by
    simp only [N, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun γ _ ↦ ?_
    rw [← hσ]
    exact (map_ne_zero _).mpr ht0
  let c := a * ∏ γ ∈ Finset.univ.erase 1, σ γ t
  have hc : e c = u * e N := by
    have hsplit : N = t * ∏ γ ∈ Finset.univ.erase 1, σ γ t := by
      simp only [N]
      rw [← Finset.mul_prod_erase Finset.univ (fun γ ↦ σ γ t) (Finset.mem_univ 1), hσ1]
    rw [← he_def] at hat
    rw [hsplit]
    simp only [c, map_mul]
    rw [← hat]
    field_simp
  have hcinv (δ : Γ) : σ δ c = c := by
    apply einj
    rw [← hσ, hc, map_mul, hfu, hσ, hN]
  obtain ⟨bc, hbc⟩ := h.mem_range_app V c fun δ ↦ ⟨hst δ, hcinv δ⟩
  obtain ⟨bN, hbN⟩ := h.mem_range_app V N fun δ ↦ ⟨hst δ, hN δ⟩
  have hq (b : Γ(W, V)) : functionFieldMap q (W.germToFunctionField V b) = e (q.app V b) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact functionFieldMap_germToFunctionField q V (q ⁻¹ᵁ V) le_rfl b
  have hbN0 : W.germToFunctionField V bN ≠ 0 := by
    intro h0
    apply hNe
    rw [← hbN, ← hq, h0, map_zero]
  have hbc0 : W.germToFunctionField V bc ≠ 0 := by
    intro h0
    apply mul_ne_zero u.ne_zero hNe
    rw [← hc, ← hbc, ← hq, h0, map_zero]
  refine ⟨Units.mk0 (W.germToFunctionField V bc / W.germToFunctionField V bN)
    (div_ne_zero hbc0 hbN0), Units.ext ?_⟩
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_div₀, hq, hbc, hbN, hc]
  field_simp

end GlobalTheory.OrbitSep
end
end

