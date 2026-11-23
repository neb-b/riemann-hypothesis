module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleTrivializingTorsionAbelianSchem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFinrankEqNormPow
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.OActDeg

def endHom {k : Type} [Field k] (X : GlobalTheory.AV.AbVar k) (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) X.X) :
    𝓞 F →+* CategoryTheory.End X where
  toFun c := End.of (GlobalTheory.AV.AbVar.Hom.mk (A := X) (B := X) (ρ.act c) (h := ρ.hom c))
  map_one' := by
    refine End.ext (Subtype.ext ?_)
    exact ρ.one
  map_mul' a b := by
    refine End.ext (Subtype.ext ?_)
    change ρ.act (a * b) = ρ.act b ≫ ρ.act a
    rw [mul_comm, ρ.mul]
  map_zero' := by
    refine End.ext (Subtype.ext ?_)
    change ρ.act 0 = 1
    have h := ρ.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  map_add' a b := by
    refine End.ext (Subtype.ext ?_)
    exact ρ.add a b

open Polynomial GlobalTheory.AV.AbVar in
theorem isFinite_and_finrank_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  intro k _ _ A _ hA F _ _ ρ l d hl hl0 hcard c hc
  let X : GlobalTheory.AV.AbVar k := GlobalTheory.TateHondaBridge.toAbVar A hA
  have h2 := GlobalTheory.abMulN_holds k A X.dim l hA X.smooth hl0
  rw [hcard] at h2
  have hdim : 2 * X.dim = d * Module.finrank ℚ F :=
    (Nat.pow_right_injective hl.two_le h2).symm
  let actionHom := endHom X F ρ
  let f := actionHom c
  let m := minpoly ℤ c
  have hi : IsIntegral ℤ c := NumberField.RingOfIntegers.isIntegral c
  have hm : m.Monic := minpoly.monic hi
  have hp : Prime m := (minpoly.irreducible hi).prime
  have hf : aeval f m = 0 := by
    have h := Polynomial.hom_eval₂ m (algebraMap ℤ (𝓞 F)) actionHom c
    rw [← aeval_def, show aeval c m = 0 from minpoly.aeval ℤ c, map_zero,
      Subsingleton.elim (actionHom.comp (algebraMap ℤ (𝓞 F))) (algebraMap ℤ _), ← aeval_def] at h
    exact h.symm
  have ⟨e, he, hdeg⟩ : ∃ e : ℕ, e * m.natDegree = 2 * X.dim ∧
      (deg f.asHom : ℤ) = m.coeff 0 ^ e := by
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨-, -, -, hfin, hrank⟩ := tl_free_finrank k l hl0 X
    have hchar (g : End X) :
        (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
      obtain ⟨⟨hmonic, hdegree, heval⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k X g
      have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
        k l hl0 X g ((charpoly g).map (algebraMap ℤ ℚ)) (hmonic.map _)
        (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hdegree])
        (fun n => by simpa using congrArg (algebraMap ℤ ℚ) (heval n))
      rw [← h, Polynomial.map_map,
        show (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
    have hdet : LinearMap.det (vmap l f.asHom) = (deg f.asHom : ℚ_[l]) := by
      have hneg : (-f).asHom = -f.asHom := map_neg (End.addEquiv (X := X)) f
      have hv : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
        simp only [hneg, vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
      have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec k X (-f)).1.2.2 0
      rw [Int.cast_zero, zero_sub, neg_neg] at hev
      rw [hv, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hchar (-f),
        Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrank, pow_mul, neg_one_sq, one_pow]
      simp
    have hinj : Function.Injective (algebraMap ℤ ℚ_[l]) := RingHom.injective_int _
    let ψ : End X →+* Module.End ℚ_[l] (Vl l X) :=
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l X)).toRingHom.comp (tend l X)
    have hT : aeval (vmap l f.asHom) m = 0 := by
      change aeval (ψ f) m = 0
      have h := Polynomial.hom_eval₂ m (algebraMap ℤ (End X)) ψ f
      rw [← aeval_def, hf, map_zero,
        Subsingleton.elim (ψ.comp (algebraMap ℤ (End X))) (algebraMap ℤ _), ← aeval_def] at h
      exact h.symm
    have hdvd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank (vmap l f.asHom) (m.map (algebraMap ℤ ℚ_[l]))
      (by rw [aeval_map_algebraMap]; exact hT)
    rw [← hchar f, ← Polynomial.map_pow] at hdvd
    obtain ⟨⟨hmonic, hdegree, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k X f
    rw [Polynomial.map_dvd_map _ hinj hmonic] at hdvd
    obtain ⟨i, -, hassociated⟩ := (dvd_prime_pow hp _).1 hdvd
    have hpow : charpoly f = m ^ i := Polynomial.eq_of_monic_of_associated hmonic (hm.pow i) hassociated
    refine ⟨i, ?_, ?_⟩
    · rw [← hdegree, hpow, hm.natDegree_pow]
    · have h := LinearMap.det_eq_sign_charpoly_coeff (vmap l f.asHom)
      rw [hdet, ← hchar f, coeff_map, hrank, pow_mul, neg_one_sq, one_pow, _root_.one_mul, hpow,
        coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero] at h
      apply Int.cast_injective (α := ℚ_[l])
      rw [Int.cast_natCast, h, eq_intCast, Int.cast_pow]
  obtain ⟨r, hr, hnorm⟩ := norm_natAbs_eq_minpoly_coeff_zero_pow c
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hi
  have her : e = d * r := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [he, hdim, ← hr, _root_.mul_assoc]
  have hdeg' : deg f.asHom = (m.coeff 0).natAbs ^ e := by
    have h := congrArg Int.natAbs hdeg
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at h
  have hval : deg f.asHom = (Algebra.norm ℤ c).natAbs ^ d := by
    rw [hdeg', hnorm, ← pow_mul, her, mul_comm]
  have hiso : IsIsogeny f.asHom := by
    classical
    by_contra h
    have hzero : deg f.asHom = 0 := by rw [deg, ite_eq_right h]
    rw [hdeg'] at hzero
    exact minpoly_int_coeff_zero_ne_zero c hc (Int.natAbs_eq_zero.1 (pow_eq_zero_iff'.1 hzero).1)
  refine ⟨hiso.1, ?_⟩
  classical
  rw [← hval]
  unfold GlobalTheory.AV.AbVar.deg
  rw [ite_eq_left hiso]
  rfl

end GlobalTheory.AV.OActDeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyRepresentableFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

theorem eq_one_iff_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (z : T ⟶ G') :
    z = 1 ↔ z.left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e1 : (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
    show (T.hom ≫ η[G'].left) ≫ φ = _
    rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  constructor
  · rintro rfl; exact e1
  · intro hz
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hz, e1]
    · rw [Over.w, Over.w]

theorem comp_pow_hom {S : Scheme.{0}} {T H A : Over S} [GrpObj A] (z : T ⟶ H) (f : H ⟶ A) (n : ℕ) :
    z ≫ f ^ n = (z ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih]

theorem exists_quot_quasiInv {Y : Scheme.{0}} [IsLocallyNoetherian Y] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀]
    (H : Over Y) [GrpObj H] (i : H ⟶ A₀) (k : ℕ) (hA : IsAbelianScheme A₀) (hi : IsMonHom i) (hm : Mono i)
    (hf : IsFinite H.hom) (he : Etale H.hom) (hk : i ^ k = 1) :
    ∃ (B : Over Y) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧
      IsQuasiInv k ψ ψ' ∧ ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  obtain ⟨B, gB, q, hB, hqm, hqfin, hqflat, hqsurj, hq⟩ :=
    GlobalTheory.IwLevel.quotGlobal_holds Y A₀ H i hA hi hm hf inferInstance
  have hcB : IsCommMonObj B := hB.comm
  have hker : ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ q = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
    intro T x
    constructor
    · intro h
      have h' : x ≫ q = (1 : T ⟶ A₀) ≫ q := by rw [h, MonObj.one_comp]
      refine ⟨hq.lift x 1 h' ≫ fst H A₀, ?_⟩
      have h1 := hq.lift_fst x 1 h'
      rw [comp_mul, hq.lift_snd, _root_.mul_one] at h1
      rw [Category.assoc, h1]
    · rintro ⟨y, rfl⟩
      have := lift y (1 : T ⟶ A₀) ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have hK := GlobalTheory.TranslQuotientPow.isMonHom_id_pow A₀ k
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨⟨ψ', hψ', hψ'e⟩, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Y A₀ B A₀ q ((𝟙 A₀) ^ k)
    hqm hK hqflat hqsurj hqc (fun T x hx => by
      obtain ⟨z, rfl⟩ := (hker T x).1 hx
      rw [GlobalTheory.TranslQuotientPow.comp_id_pow, ← comp_pow_hom, hk, comp_one])
  refine ⟨B, gB, hcB, q, ψ', hB, ⟨hqm, hψ', hψ'e, ?_⟩, hker⟩
  rw [← cancel_epi q, reassoc_of% hψ'e, GlobalTheory.TranslQuotientPow.comp_id_pow q k,
    GlobalTheory.TranslQuotientPow.pow_comp_hom q (𝟙 A₀) k, Category.id_comp]

theorem ker_iff_of_pullbacks {S Y T : Scheme.{0}} {g₀ : Y ⟶ S} {A : Over S} {A₀ : Over Y}
    {φ₀ : A₀.left ⟶ A.left} (h₀ : IsPullback φ₀ A₀.hom A.hom g₀)
    {H : Over Y} {i : H ⟶ A₀} {B : Over Y} [GrpObj B] {ψ : A₀ ⟶ B}
    (hker : ∀ (T' : Over Y) (x : T' ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T' ⟶ H, z ≫ i = x)
    {y : T ⟶ Y} {A₁ : Over T} {θ : A₁.left ⟶ A₀.left} (hθ : θ ≫ A₀.hom = A₁.hom ≫ y)
    {B₁ : Over T} [GrpObj B₁] {θ' : B₁.left ⟶ B.left} (hθ' : IsGrpPullback B₁ B y θ') {ψ₁ : A₁ ⟶ B₁}
    (hc : θ ≫ ψ.left = ψ₁.left ≫ θ') (T' : Over T) (g : T' ⟶ A₁) :
    g ≫ ψ₁ = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ θ ≫ φ₀ := by
  have hP : (g.left ≫ θ) ≫ A₀.hom = T'.hom ≫ y := by
    rw [Category.assoc, hθ, ← Category.assoc, Over.w g]
  let P : Over.mk (T'.hom ≫ y) ⟶ A₀ := Over.homMk (g.left ≫ θ) hP
  have e : P ≫ ψ = 1 ↔ (g.left ≫ θ) ≫ ψ.left = T'.hom ≫ y ≫ η[B].left := by
    rw [← Category.assoc T'.hom]
    constructor
    · intro h; exact congrArg Over.Hom.left h
    · intro h; exact Over.OverMorphism.ext h
  rw [eq_one_iff_of_isGrpPullback hθ', Over.comp_left, Category.assoc, ← hc, ← Category.assoc, ← e, hker]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.left, Over.w z, ?_⟩
    have := congrArg Over.Hom.left hz
    rw [Over.comp_left] at this
    rw [← Category.assoc, this]
    rfl
  · rintro ⟨h, hH, hφ⟩
    refine ⟨Over.homMk h hH, Over.OverMorphism.ext ?_⟩
    show h ≫ i.left = g.left ≫ θ
    apply h₀.hom_ext
    · rw [Category.assoc, hφ, Category.assoc]
    · rw [Category.assoc, Over.w i, hH, Category.assoc, hθ, ← Category.assoc, Over.w g]

theorem isogeny_rep : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (B : Over Y.left) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧ IsQuasiInv k ψ ψ' ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsQuasiInv k ψ₁ ψ₁' → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (θ : A₁.left ⟶ A₀.left) (θ' : B₁.left ⟶ B.left), θ ≫ φ₀ = φ₁ ∧ IsGrpPullback A₁ A₀ y θ ∧ IsGrpPullback B₁ B y θ' ∧ θ ≫ ψ.left = ψ₁.left ≫ θ' := by
  intro S _ A _ _ k hA hk0 hk
  obtain ⟨Y, hYf, hYe, hY⟩ := _root_.UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme S A k hA hk0 hk
  refine ⟨Y, hYf, hYe, ?_⟩
  intro A₀ _ _ φ₀ h₀
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  obtain ⟨H, _, i, hi, hm, hHf, hHe, hik, hH⟩ := hY A₀ φ₀ h₀
  have hA₀ : IsAbelianScheme A₀ := by
    exact { comm := inferInstance
            smooth := MorphismProperty.of_isPullback (P := @Smooth) h₀.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) h₀.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₀.1 hA.geomConnected }
  obtain ⟨B, gB, cB, ψ, ψ', hB, hq, hker⟩ := exists_quot_quasiInv A₀ H i k hA₀ hi hm hHf hHe hik
  refine ⟨B, gB, cB, ψ, ψ', hB, hq, ?_⟩
  intro T x A₁ _ _ φ₁ B₁ _ _ ψ₁ ψ₁' h₁ hB₁ hq₁
  have hkT : IsUnit (k : Γ(T, ⊤)) := by
    have := hk.map x.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨hψ₁m, hψ₁'m, e₁, e₂⟩ := hq₁
  have hkill : ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ ψ₁ = 1 → g ^ k = 1 := by
    intro T' g hg
    rw [← GlobalTheory.TranslQuotientPow.comp_id_pow, ← e₁, ← Category.assoc, hg, one_comp]
  have hA₁ : IsAbelianScheme A₁ := by
    exact { comm := inferInstance
            smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 hA.geomConnected }
  obtain ⟨y, ⟨hyx, hyker⟩, hyu⟩ := hH T x A₁ φ₁ B₁ ψ₁ h₁ hB₁ hψ₁m hkill
  have w : φ₁ ≫ A.hom = (A₁.hom ≫ y) ≫ Y.hom := by rw [h₁.1.w, Category.assoc, hyx]
  let θ := h₀.1.lift φ₁ (A₁.hom ≫ y) w
  have hθφ : θ ≫ φ₀ = φ₁ := h₀.1.lift_fst _ _ _
  have hθs : θ ≫ A₀.hom = A₁.hom ≫ y := h₀.1.lift_snd _ _ _
  have hθ : IsGrpPullback A₁ A₀ y θ := IsGrpPullback.cancel h₀ (h₁.congr hyx.symm hθφ.symm) hθs
  obtain ⟨B₂, _, _, θ₂, ψ₂, ψ₂', hB₂, hθ₂, hq₂, hc₂, -⟩ :=
    GlobalTheory.UPel.HT.ES.pullQuasiInv T Y.left y A₀ B k ψ ψ' A₁ θ hB hq hθ
  obtain ⟨hψ₂f, hψ₂e, hψ₂s⟩ := GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv T A₁ B₂ k ψ₂ ψ₂' hA₁ hB₂ hkT hq₂
  haveI := hψ₂f
  haveI := hψ₂e
  have hk₂ := ker_iff_of_pullbacks h₀.1 hker hθs hθ₂ hc₂
  obtain ⟨β, hβi, hβm, hβ⟩ := GlobalTheory.SameKer.exists_iso_of_sameKer T A₁ B₂ B₁ ψ₂ ψ₁' ψ₁ k hB₁ hkT hq₂.1
    hψ₁'m hψ₁m inferInstance hψ₂s inferInstance e₂ (fun T' g => by rw [hyker, hk₂, hθφ])
  refine ⟨y, ⟨hyx, θ, β.left ≫ θ₂, hθφ, hθ, ?_, ?_⟩, ?_⟩
  · haveI := hβi
    haveI : IsMonHom (asIso β).hom := hβm
    exact ((isGrpPullback_of_iso (asIso β)).comp hθ₂).congr (Category.id_comp _) rfl
  · rw [hc₂, ← hβ, Over.comp_left, Category.assoc]
  · rintro y' ⟨hy'x, θ', θ'', hθ'φ, hθ', hθ'', hc'⟩
    apply hyu
    refine ⟨hy'x, fun T' g => ?_⟩
    rw [ker_iff_of_pullbacks h₀.1 hker hθ'.1.w hθ'' hc', hθ'φ]

end GlobalTheory.UPel.HT.ES.IsogRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfPullbackQuasiInverseIsogenyTrivialAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuasiInvPull


open GlobalTheory.CechPic in
theorem lbIso_of_pullback_quasiInverseIsogeny_trivial_axes : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (Q₁ Q₂ : LB (G2 B).left), IsAbelianScheme B → 0 < k →
    IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsAxesTriv B Q₁ → IsAxesTriv B Q₂ →
    LBIso (Q₁.pull (Hecke.sq2 ψ)) (Q₂.pull (Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro Y A B _ _ _ _ k ψ ψ' Q₁ Q₂ hB hk _ hq h₁ h₂ hiso
  obtain ⟨hψ, hψ', -, hc⟩ := hq
  haveI := hψ
  haveI := hψ'
  have o₁ : (1 : B ⟶ B) ≫ (𝟙 B) ^ k = 1 := by
    rw [← hc, ← Category.assoc, GlobalTheory.BirigUniq.one_comp_monHom, GlobalTheory.BirigUniq.one_comp_monHom]
  obtain ⟨hL₁, r₁₁, r₁₂⟩ := h₁
  obtain ⟨hL₂, r₂₁, r₂₂⟩ := h₂
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk
  have pull_comp_left {S : Scheme.{0}} {U V W : Over S} (g : U ⟶ V) (f : V ⟶ W) (c : Pic W.left) :
      pull (g ≫ f).left c = pull g.left (pull f.left c) := by
    rw [Over.comp_left, pull_comp]
  have pic_eq_zero_of_fpqc {S : Scheme.{0}} (X Y Y' : Over S) [GrpObj X] (hX : IsAbelianScheme X)
      (c : Y' ⟶ Y) (hfl : Flat c.left) (hsu : Surjective c.left) (hqc : QuasiCompact c.left)
      (d : Pic (X ⊗ Y).left)
      (h0 : pull (lift (1 : Y ⟶ X) (𝟙 Y)).left d = 0)
      (h1 : pull (lift (fst X Y') (snd X Y' ≫ c)).left d = 0) : d = 0 := by
    obtain ⟨D, hD, rfl⟩ := cls_surj d
    have t := GlobalTheory.RigDesc.triv_of_triv_zero_of_fpqc S X Y Y' hX c hfl hsu hqc D hD
      ((cls_eq_zero_iff (pull_isLB hD _)).1 h0) ((cls_eq_zero_iff (pull_isLB hD _)).1 h1)
    exact (cls_eq_zero_iff hD).2 t
  let d := cls Q₁ hL₁ - cls Q₂ hL₂
  have z₁₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₁
  have z₁₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₁ hL₁) = 0 := (cls_eq_zero_iff (pull_isLB hL₁ _)).2 r₁₂
  have z₂₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₁
  have z₂₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls Q₂ hL₂) = 0 := (cls_eq_zero_iff (pull_isLB hL₂ _)).2 r₂₂
  have d₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left d = 0 := by simp only [d, map_sub, z₁₁, z₂₁, sub_zero]
  have d₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left d = 0 := by simp only [d, map_sub, z₁₂, z₂₂, sub_zero]
  have dψ : pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left d = 0 := by
    have e : pull (Hecke.sq2 ψ) (cls Q₁ hL₁) = pull (Hecke.sq2 ψ) (cls Q₂ hL₂) :=
      (cls_eq_iff (pull_isLB hL₁ _) (pull_isLB hL₂ _)).2 hiso
    simp only [d, map_sub]
    exact sub_eq_zero.2 e

  have dk : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k)).left d = 0 := by
    have : lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) =
        lift (fst B B ≫ ψ') (snd B B ≫ ψ') ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
      rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this, pull_comp_left, dψ, map_zero]

  have hD : pull (lift (fst B B ≫ (𝟙 B) ^ k) (snd B B)).left d = 0 := by
    refine pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) = lift (1 : B ⟶ B) (𝟙 B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [o₁]
      rw [this, d₁]
    · rw [← pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) =
          lift (fst B B ≫ (𝟙 B) ^ k) (snd B B ≫ (𝟙 B) ^ k) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, dk]

  have hQ : pull (lift (snd B B) (fst B B)).left d = 0 := by
    refine pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₂]
    · rw [← pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) =
          lift (snd B B) (fst B B) ≫ lift (fst B B ≫ (𝟙 B) ^ k) (snd B B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, hD, map_zero]
  have hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hd : d = 0 := by
    have H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d := by
      rw [hsw, Over.id_left, pull_id]
    rw [pull_comp_left, hQ, map_zero] at H
    exact H.symm
  exact (cls_eq_iff hL₁ hL₂).1 (sub_eq_zero.1 hd)

end GlobalTheory.QuasiInvPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerLiftUnit


open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.PrinThicken in
theorem ker_pow_eq_one_of_lift : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → ∀ (l : (G2 A₀).left ⟶ (G2 A).left), Geo.Tor.IsSquare i l → ∀ (P₀ : LB (G2 A₀).left) (P : LB (G2 A).left), P₀.IsLB → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → LBIso (P.pull l) P₀ → ∀ (e : ℕ), IsUnit (e : C) → (∀ (T : Over (Sp C₀)) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ A _ _ i hi hA l hl P₀ P hP₀ hP r₁ r₂ hsymm amp hred e he ker₀
  have csymm : cls P hP = GlobalTheory.CechPic.pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsymm
  have wS : (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l = l ≫ (lift (snd A A) (fst A A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hl.1, GlobalTheory.AbDual.lift_left_fst_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_fst, hl.2]
    · rw [Category.assoc, hl.2, GlobalTheory.AbDual.lift_left_snd_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_snd, hl.1]
  have c₀symm : cls P₀ hP₀ = GlobalTheory.CechPic.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left (cls P₀ hP₀) := by
    have e := (cls_eq_iff (pull_isLB hP l) hP₀).2 hred
    rw [cls_pull hP] at e
    rw [← e, ← pull_comp, wS, pull_comp, ← csymm]
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := GlobalTheory.abelianDualCrystal.1 _ A hA
  obtain ⟨lam, hlam, hiff⟩ := GlobalTheory.PoincarePull.exists_hom_triv_iff C A hA D Q q q' _ (pull_isLB hP _) amp P hP r₁ r₂
  haveI := hlam
  have hiff' : ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ≫ lam = 1 := fun T x hx ↦
    (hiff T x).1 ((triv_ev_iff hP _ _).2 ((evc_comm hP csymm _ _).trans ((triv_ev_iff hP _ _).1 hx)))
  have tors₀ : ∀ (T₀ : Over (Sp C₀)) (z : Over.mk (T₀.hom ≫ spMap π) ⟶ A), z ≫ lam = 1 → z ^ e = 1 := by
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ A₀ := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have k₁ : z₀ ^ e = 1 := ker₀ _ z₀ (by
      have e1 := evc_trR hi hi hl.1 hl.2 hP hP₀ hred (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff _ z).2 hz)
      rw [show pushP hi (s := T₀.hom) rfl z₀ = z from Over.OverMorphism.ext hz₀] at e1
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (GlobalTheory.CechPic.pull s) (e1.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP₀ _ _).2 ((evc_comm hP₀ c₀symm _ _).symm.trans e2))
    have hp : ∀ m : ℕ, (z₀ ^ m).left ≫ i = (z ^ m).left := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero]
        exact one_left_comp hi (s := T₀.hom) rfl
      | succ m ih =>
        rw [pow_succ, pow_succ]
        exact mul_left_comp hi (s := T₀.hom) rfl ih hz₀
    apply Over.OverMorphism.ext
    rw [← hp e, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  intro T x hx
  have hx0 : x ≫ lam = 1 := hiff' T x hx
  have hw0 : (x ^ e) ≫ lam = 1 := by rw [pow_comp, hx0, one_pow]
  have hwC : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ (x ^ e) = 1 := fun T₀ j ↦ by
    rw [comp_pow]
    exact tors₀ T₀ (j ≫ x) (by rw [Category.assoc, hx0, MonObj.comp_one])
  let k := equalizer.ι lam (1 : A ⟶ D)
  have hk : k ≫ lam = 1 := by rw [equalizer.condition, MonObj.comp_one]
  let u : 𝟙_ (Over (Sp C)) ⟶ equalizer lam (1 : A ⟶ D) :=
    equalizer.lift 1 (by rw [MonObj.one_comp, MonObj.comp_one])
  have hww : (x ^ e) ^ e = 1 := by
    have h1 := GlobalTheory.T.comp_eq_of_sqZero_agree_pairs C C₀ π hπ hsq (equalizer lam (1 : A ⟶ D)) A (k ^ e) 1
      (fun T₀ y ↦ by
        rw [comp_pow, MonObj.comp_one]
        exact tors₀ T₀ (y ≫ k) (by rw [Category.assoc, hk, MonObj.comp_one]))
      T (equalizer.lift (x ^ e) (by rw [hw0, MonObj.comp_one])) (toUnit T ≫ u)
      (fun T₀ j ↦ by
        rw [← cancel_mono k, Category.assoc, Category.assoc, Category.assoc,
          show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _,
          show u ≫ k = 1 from equalizer.lift_ι _ _, hwC, MonObj.comp_one, MonObj.comp_one])
      (by rw [comp_pow, MonObj.comp_one, Category.assoc, show u ≫ k = 1 from equalizer.lift_ι _ _,
        MonObj.comp_one, one_pow])
    rw [comp_pow, show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _, MonObj.comp_one] at h1
    exact h1
  exact GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial C C₀ π hπ hsq A e he T (x ^ e) hwC hww

end GlobalTheory.KerLiftUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenySquareCompatCompQuasiInvStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (exact GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv  <;> assumption)
end

