module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.CommutingSurjectivity
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem laurent_adjoin_eq_of_image_eq {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (h0 : 0 < Module.finrank ℤ O) :
    Function.Injective (algebraMap (𝓞 F) O) := by
  classical
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hI : Ideal.span {x} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hmem : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : 𝓞 F) ∈ Ideal.span {x} := Ideal.absNorm_mem _
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  have hn0 : Ideal.absNorm (Ideal.span {x}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : O) = 0 := by
    rw [← map_natCast (algebraMap (𝓞 F) O), ← hy, map_mul, hx, mul_zero]
  have h2 : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℤ) • (1 : O) =
      ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℤ) • (0 : O) := by
    rw [smul_zero, zsmul_eq_mul, _root_.mul_one]
    exact_mod_cast h1
  have h3 : (1 : O) = 0 := smul_right_injective O (by exact_mod_cast hn0) h2
  haveI : Subsingleton O := subsingleton_of_zero_eq_one h3.symm
  rw [Module.finrank_zero_of_subsingleton] at h0
  exact lt_irrefl 0 h0

private theorem wachExpansion_smul_compatible {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hr : Module.finrank ℤ O = Module.finrank ℚ F)
    (hinj : Function.Injective (algebraMap (𝓞 F) O)) (x : O) :
    ∃ e : ℤ, e ≠ 0 ∧ ∃ c : 𝓞 F, e • x = algebraMap (𝓞 F) O c := by
  classical
  let b := Module.finBasis ℤ (𝓞 F)
  let v : Option (Fin (Module.finrank ℤ (𝓞 F))) → O :=
    fun o => Option.elim o x (fun i => algebraMap (𝓞 F) O (b i))
  have hcard : ¬ LinearIndependent ℤ v := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hr, RingOfIntegers.rank] at hle
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hcard
  rw [Fintype.sum_option] at hg
  have hmap : algebraMap (𝓞 F) O (∑ j, g (some j) • b j) =
      ∑ j, g (some j) • algebraMap (𝓞 F) O (b j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
  have hg' : g none • x + algebraMap (𝓞 F) O (∑ j, g (some j) • b j) = 0 := by
    rw [hmap]
    simpa [v] using hg
  have hnone : g none ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg'
    have hc0 : ∑ j, g (some j) • b j = 0 := hinj (by rw [hg', map_zero])
    have hall := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun j => g (some j)) hc0
    cases i with
    | none => exact hi h0
    | some j => exact hi (hall j)
  refine ⟨g none, hnone, -(∑ j, g (some j) • b j), ?_⟩
  rw [map_neg, eq_neg_iff_add_eq_zero]
  exact hg'

private theorem surj_comm {F O : Type} [Field F] [NumberField F] [CommRing O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O]
    (hinj : Function.Injective (algebraMap (𝓞 F) O))
    (hs : ∀ x : O, ∃ e : ℤ, e ≠ 0 ∧ ∃ c : 𝓞 F, e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  classical
  intro x
  obtain ⟨e, he, c, hc⟩ := hs x
  obtain ⟨P, hPm, hPx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have hQ : Polynomial.aeval (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hc, algebraMap_int_eq, Int.coe_castRingHom, zsmul_eq_mul]
  rw [hex, Polynomial.aeval_algebraMap_apply] at hQ
  have hQ' : Polynomial.aeval c (P.scaleRoots e) = 0 := hinj (by rw [hQ, map_zero])
  have hQF : Polynomial.aeval (c : F) (P.scaleRoots e) = 0 := by
    have h0 := congrArg (algebraMap (𝓞 F) F) hQ'
    rwa [map_zero, ← Polynomial.aeval_algebraMap_apply] at h0
  have he' : ((e : ℤ) : F) ≠ 0 := by exact_mod_cast he
  have hmul : algebraMap ℤ F e * ((c : F) / e) = (c : F) := by
    rw [eq_intCast]
    field_simp
  have hz : Polynomial.eval₂ (algebraMap ℤ F) ((c : F) / e) P = 0 := by
    have h := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ F) ((c : F) / e) e
    rw [hmul, ← Polynomial.aeval_def, hQF] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by rwa [eq_intCast]))
  let d : 𝓞 F := ⟨(c : F) / e, ⟨P, hPm, hz⟩⟩
  have hed : (e : 𝓞 F) * d = c := by
    apply RingOfIntegers.ext
    show ((e : 𝓞 F) : F) * ((c : F) / e) = (c : F)
    have hcoe : ((e : 𝓞 F) : F) = (e : F) := by
      first
        | simp
        | exact map_intCast (algebraMap (𝓞 F) F) e
    rw [hcoe]
    field_simp
  refine ⟨d, ?_⟩
  apply smul_right_injective O he
  show e • algebraMap (𝓞 F) O d = e • x
  rw [hc, ← hed, map_mul, map_intCast, zsmul_eq_mul]

private theorem exists_finset_adjoin_laurent_preimage {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hr : Module.finrank ℤ O = Module.finrank ℚ F) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  have hpos : 0 < Module.finrank ℤ O := by
    rw [hr]
    exact Module.finrank_pos
  have hinj := laurent_adjoin_eq_of_image_eq (F := F) (O := O) hpos
  have hs := wachExpansion_smul_compatible (F := F) (O := O) hr hinj
  have hcomm : ∀ x y : O, x * y = y * x := by
    intro x y
    obtain ⟨a, ha, c, hc⟩ := hs x
    obtain ⟨b, hb, c', hc'⟩ := hs y
    apply smul_right_injective O (mul_ne_zero ha hb)
    show (a * b) • (x * y) = (a * b) • (y * x)
    calc (a * b) • (x * y) = (a • x) * (b • y) := by rw [smul_mul_smul_comm]
      _ = algebraMap (𝓞 F) O (c * c') := by rw [hc, hc', map_mul]
      _ = algebraMap (𝓞 F) O (c' * c) := by rw [_root_.mul_comm c c']
      _ = (b • y) * (a • x) := by rw [hc, hc', map_mul]
      _ = (a * b) • (y * x) := by rw [smul_mul_smul_comm, _root_.mul_comm b a]
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  exact surj_comm hinj hs

theorem UpperTheory.Gal.Ord.surjO :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  intro p _ D hm
  haveI := D.freeO
  haveI := D.finO
  apply exists_finset_adjoin_laurent_preimage
  rw [D.rankO, hm]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ExistsFunctionalNeZeroProjective
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_functional_ne_zero_projective {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Projective B M] {m : M} (hm : m ≠ 0) : ∃ l : M →ₗ[B] B, l m ≠ 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective B M)
  by_contra hall
  push_neg at hall
  apply hm
  have h0 : s m = 0 := by
    ext a
    simpa using hall (Finsupp.lapply a ∘ₗ s)
  have := LinearMap.congr_fun hs m
  simpa [h0] using this.symm

private theorem exists_point_nonvanishing_reduced (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [IsReduced B] {c : B} (hc : c ≠ 0) :
    ∃ x : B →ₐ[k] k, x c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.NonvanishingPoint.exists_point_nonvanishing_reduced k B hc

theorem UpperTheory.Gal.Ord.dz1 :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B] [Module.Projective B Ω[B⁄k]] (r : B),
      (∀ v : B →ₐ[k] DualNumber k, TrivSqZeroExt.snd (v r) = 0) → KaehlerDifferential.D k B r = 0 := by
  intro k _ _ B _ _ _ _ _ r hv
  by_contra hne
  obtain ⟨l, hl⟩ := exists_functional_ne_zero_projective (B := B) hne
  obtain ⟨x, hx⟩ := exists_point_nonvanishing_reduced k B hl
  let d : B →ₗ[k] k := x.toLinearMap ∘ₗ (l.restrictScalars k) ∘ₗ (KaehlerDifferential.D k B).toLinearMap
  have hd : ∀ b, d b = x (l (KaehlerDifferential.D k B b)) := fun _ => rfl
  let f : B →ₗ[k] DualNumber k :=
    Algebra.linearMap k (DualNumber k) ∘ₗ x.toLinearMap + TrivSqZeroExt.inrHom k k ∘ₗ d
  have hal : ∀ c : k, algebraMap k (DualNumber k) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hfst : ∀ b, TrivSqZeroExt.fst (f b) = x b := fun b => by simp [f, hal]
  have hsnd : ∀ b, TrivSqZeroExt.snd (f b) = d b := fun b => by simp [f, hal]
  let v : B →ₐ[k] DualNumber k := AlgHom.ofLinearMap f
    (by
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hsnd, hd])
    (by
      intro a b
      apply TrivSqZeroExt.ext
      · simp [hfst]
      · simp [hfst, hsnd, hd, Derivation.leibniz, mul_comm, add_comm])
  apply hx
  have := hv v
  simpa [v, hsnd, hd] using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem pow_inj {R : Type*} [CommRing R] [_root_.IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (e : a ^ p = b ^ p) : a = b := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (a - b) b
  rw [sub_add_cancel, e, h] at hr
  have h0 : (a - b) ^ p = 0 := by
    simpa using hr.symm
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)

private theorem step {p : ℕ} {A B C : CommRingCat} (u : A ⟶ B) (v : A ⟶ C) (FB : B ⟶ B) (FC : C ⟶ C)
    (r : B ⟶ C) (hB : ∀ x, FB x = x ^ p) (hC : ∀ x, FC x = x ^ p)
    (hU : v ≫ FC = (u ≫ FB) ≫ r) (a : A) : (u ≫ r).hom a ^ p = v.hom a ^ p := by
  have ha := ConcreteCategory.congr_hom hU a
  simp only [ConcreteCategory.comp_apply, hB, hC, map_pow] at ha
  simpa using ha.symm

private theorem frob_epi (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X]
    (h : (p : Γ(X, ⊤)) = 0) : Epi (GlobalTheory.VB.frob X p h) := by
  have hV (V : X.Opens) : (p : Γ(X, V)) = 0 := by
    have := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h
    simpa using this
  refine ⟨fun {Y} f g e => ?_⟩
  have hx (x : X) : f x = g x := by
    have := congrArg (fun φ : X ⟶ Y => φ x) e
    simpa [GlobalTheory.VB.frob, GlobalTheory.SS.FrobField.absFrob,
      GlobalTheory.SS.FrobField.absPre] using this
  refine Scheme.Hom.ext (by ext x; exact hx x) fun U => ?_
  have hU := Scheme.Hom.congr_app e.symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hU
  ext a
  apply pow_inj (Fact.out : p.Prime) (hV _)
  exact step (p := p) (f.app U) (g.app U) ((GlobalTheory.VB.frob X p h).app (f ⁻¹ᵁ U))
    ((GlobalTheory.VB.frob X p h).app (g ⁻¹ᵁ U)) _ (GlobalTheory.VB.frob_app p h _) (GlobalTheory.VB.frob_app p h _) hU a

theorem UpperTheory.Gal.Ord.epi :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0), Epi (GlobalTheory.VB.frob X p h) ∧ ∀ j, Epi (frobN p X h j) := by
  intro p _ X _ h
  have hF := frob_epi p X h
  refine ⟨hF, fun j => ?_⟩
  induction j with
  | zero => exact (inferInstance : Epi (𝟙 X))
  | succ j ih =>
    have : Epi (frobN p X h j) := ih
    exact epi_comp (GlobalTheory.VB.frob X p h) (frobN p X h j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdPull
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem UpperTheory.Gal.Ord.eq_one_of_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') (x₀ : Over.mk y' ⟶ G) (hx : x₀.left = (1 : T ⟶ G').left ≫ φ) : x₀ = 1 := by
  subst hy
  have h2 := h.2 T 1 1 x₀ x₀ hx hx
  have hsq : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, _root_.mul_one, hx]
  exact mul_eq_left.mp hsq

private theorem UpperTheory.Gal.Ord.one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') : (1 : Over.mk y' ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk y').hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    exact hy
  have e := eq_one_of_left h T hy (Over.homMk ((1 : T ⟶ G').left ≫ φ) hw) rfl
  rw [← e]
  rfl

private theorem UpperTheory.Gal.Ord.killedBy_iff {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}
    (m : ObjMap o' o f) (v : Ideal (𝓞 D.F)) (T : Over S') {y' : T.left ⟶ S} (hy : T.hom ≫ f = y')
    (x : T ⟶ o'.A) (x₀ : Over.mk y' ⟶ o.A) (hx : x₀.left = x.left ≫ m.φ) :
    KilledBy o v x₀ ↔ KilledBy o' v x := by
  have key : ∀ c : D.O, (x₀ ≫ o.act.act c).left = (x ≫ o'.act.act c).left ≫ m.φ := by
    intro c
    rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, m.act c]
  unfold KilledBy
  constructor
  · intro H a ha
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [← key, H a ha]
      exact one_left m.cart T hy
    · simp only [Over.w]
  · intro H a ha
    apply eq_one_of_left m.cart T hy
    rw [key, H a ha]

theorem UpperTheory.Gal.Ord.ordPull :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F))
      (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (s₀ : Sp k ⟶ Sp R) (o₀ : Obj b N s₀), ObjMap o₀ o y → IsWOrd o₀ w (𝟙 (Sp k)) → IsWOrd o w y := by
  intro p _ D R _ b N S s o w k _ _ y s₀ o₀ m h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rw [← h4]
  have hy : (Over.mk (𝟙 (Sp k))).hom ≫ y = y := by simp
  apply Nat.card_congr
  exact
    { toFun := fun g =>
        ⟨Over.homMk (m.cart.1.lift g.1.left (𝟙 _) (by simp)) (by rw [IsPullback.lift_snd]; rfl),
          (killedBy_iff m w _ hy _ g.1 (m.cart.1.lift_fst _ _ _).symm).mp g.2⟩
      invFun := fun g =>
        ⟨Over.homMk (g.1.left ≫ m.φ) (by rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; simp),
          (killedBy_iff m w _ hy g.1 _ rfl).mpr g.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        apply m.cart.1.hom_ext
        · simp
        · simp }
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RadicalStalk
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem radical_quot (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (m : Ideal R) [m.IsMaximal] : (m.map (algebraMap R B)).IsRadical := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : _root_.IsReduced ((R ⧸ m) ⊗[R] B) := _root_.GlobalTheory.isReduced_of_smooth_over_field (R ⧸ m) _
  have e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m
  haveI : _root_.IsReduced (B ⧸ m.map (algebraMap R B)) :=
    isReduced_of_injective e.toRingEquiv.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr this

private theorem radical_loc (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (M : Submonoid B)
    [IsLocalization M A] (I : Ideal B) (hI : I.IsRadical) : (I.map (algebraMap B A)).IsRadical := by
  intro a ⟨n, hn⟩
  have hn' : a ^ (n + 1) ∈ I.map (algebraMap B A) := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hn
  obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq M a
  obtain ⟨⟨i, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hn'
  have hu : IsLocalization.mk' A b u * algebraMap B A u = algebraMap B A b := IsLocalization.mk'_spec A b u
  have e1 : algebraMap B A (b ^ (n + 1) * t) = algebraMap B A (i * u ^ (n + 1)) := by
    simp only [map_mul, map_pow]
    rw [← ht, ← hu]
    ring
  obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := M) e1
  have hy : (d : B) * t * b ∈ I := by
    apply hI
    refine ⟨n + 1, ?_⟩
    have e2 : ((d : B) * t * b) ^ (n + 1) = ((d : B) * t) ^ n * ((d : B) * (b ^ (n + 1) * t)) := by ring
    rw [e2, hd]
    exact I.mul_mem_left _ (I.mul_mem_left _ (I.mul_mem_right _ i.2))
  refine (IsLocalization.mem_map_algebraMap_iff M A).mpr
    ⟨⟨⟨_, hy⟩, u * d * t⟩, ?_⟩
  simp only [Submonoid.coe_mul, map_mul]
  rw [← hu]
  ring

private theorem radical_stalk (R : Type) [CommRing R] (m : Ideal R) [m.IsMaximal] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X) (r : CommRingCat.of R ⟶ X.presheaf.stalk z)
    (hr : Spec.map r = X.fromSpecStalk z ≫ s) : (m.map r.hom).IsRadical := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hsm : Smooth (hU.fromSpec ≫ s) := inferInstance
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hρs : ρ.hom.Smooth := by
    rw [← hρ] at hsm
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm
  have e : r = ρ ≫ X.presheaf.germ U z hzU := by
    apply Spec.map_injective
    rw [hr, Spec.map_comp, hρ, ← hU.fromSpecStalk_eq_fromSpecStalk hzU]
    simp [IsAffineOpen.fromSpecStalk]
  letI := ρ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, U) := hρs
  have h1 := radical_quot R Γ(X, U) m
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have h2 := radical_loc Γ(X, U) (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl _ h1
  rw [Ideal.map_map] at h2
  rw [e]
  exact h2

private theorem kills_max (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X)
    (hmax : ∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z)
    (T : Type) [CommRing T] (φ : X.presheaf.stalk z ⟶ CommRingCat.of T) (c : R →+* T)
    (h : Spec.map φ ≫ X.fromSpecStalk z ≫ s = Spec.map (CommRingCat.ofHom c))
    (hc : ∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) :
    ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z), φ.hom x = 0 := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (X.fromSpecStalk z ≫ s)
  have hrc : r ≫ φ = CommRingCat.ofHom c := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr, h]
  have hrad := radical_stalk R (IsLocalRing.maximalIdeal R) X s z r hr
  have hprime : ∀ P : Ideal (X.presheaf.stalk z), P.IsPrime →
      (IsLocalRing.maximalIdeal R).map r.hom ≤ P → P = IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    intro P hP hJ
    let y : Spec (X.presheaf.stalk z) := ⟨P, hP⟩
    have h1 : X.fromSpecStalk z y ⤳ z := by
      have : X.fromSpecStalk z y ∈ Set.range (X.fromSpecStalk z) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : s.base (X.fromSpecStalk z y) = IsLocalRing.closedPoint R := by
      have e : s.base (X.fromSpecStalk z y) = (Spec.map r).base y := by rw [hr]; rfl
      rw [e]
      apply PrimeSpectrum.ext
      have hle : IsLocalRing.maximalIdeal R ≤ P.comap r.hom := Ideal.map_le_iff_le_comap.mp hJ
      exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap r.hom).ne_top hle).symm
    have h3 := hmax _ h2 h1
    have h4 : y = IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      (X.fromSpecStalk z).isEmbedding.injective (h3.trans Scheme.fromSpecStalk_closedPoint.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  intro x hx
  have hxJ : x ∈ (IsLocalRing.maximalIdeal R).map r.hom := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun {P} hP => ?_
    rw [hprime P hP.2 hP.1]
    exact hx
  have hker : (IsLocalRing.maximalIdeal R).map r.hom ≤ RingHom.ker φ.hom := by
    refine Ideal.map_le_iff_le_comap.mpr fun y hy => ?_
    have e : φ.hom (r.hom y) = c y := congrArg (fun f => f.hom y) hrc
    exact (RingHom.mem_ker).mpr (e.trans (hc y hy))
  exact hker hxJ

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.gen :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] (z : X), s.base z = IsLocalRing.closedPoint R →
      (∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (T : Type) [CommRing T] [IsLocalRing T] (v : Sp T ⟶ X) (c : R →+* T),
      v.base (IsLocalRing.closedPoint T) = z → v ≫ s = spMap c → (∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) →
      ∃ τ : X.residueField z →+* T, spMap τ ≫ X.fromSpecResidueField z = v := by
  intro R _ _ _ X s _ z _ hmax T _ _ v c hv hvs hc
  subst hv
  have hφ : Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) ≫ X.fromSpecStalk _ = v :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of T) v
  have hk := kills_max R X s _ hmax T (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) c
    (by rw [← Category.assoc, hφ]; exact hvs) hc
  refine ⟨Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk, ?_⟩
  have e : X.residue _ ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk) =
      Scheme.stalkClosedPointTo (R := CommRingCat.of T) v := by
    ext x
    rfl
  show Spec.map _ ≫ Spec.map (X.residue _) ≫ X.fromSpecStalk _ = v
  rw [← Spec.map_comp_assoc]
  exact (congrArg (fun g => Spec.map g ≫ X.fromSpecStalk _) e).trans hφ
end

