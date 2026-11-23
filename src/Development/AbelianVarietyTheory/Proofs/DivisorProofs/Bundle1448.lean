module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeTateFunctionalEquation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfActsTriviallyAbelianVarietyAlgClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ActTrivialInj

theorem exists_nat_eq_mul {F : Type} [Field F] [NumberField F] {O : Type} [CommRing O] [Algebra O F]
    [IsFractionRing O F] {x : O} (hx : x ≠ 0) : ∃ n : ℕ, n ≠ 0 ∧ ∃ r : O, (n : O) = x * r := by
  set y := algebraMap O F x with hydef
  have hy : y ≠ 0 := by
    intro h
    apply hx
    apply IsFractionRing.injective O F
    rw [map_zero]
    exact h
  have hint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have hp0 : (minpoly ℚ y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy
  set q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ y) with hqdef
  have hq : Polynomial.aeval y q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) (minpoly ℚ y) (minpoly.aeval ℚ y)
  obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ y)
  set c := q.coeff 0 with hcdef
  have hc : c ≠ 0 := by
    intro h
    have h' := congrArg (fun P => P.coeff 0) hb
    simp only [Polynomial.coeff_map, Polynomial.coeff_smul] at h'
    rw [← hcdef, h, map_zero, eq_comm, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact nonZeroDivisors.ne_zero hb0 h'
    · exact hp0 h'
  have hO : Polynomial.aeval x q = 0 := by
    apply IsFractionRing.injective O F
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact hq
  have key := congrArg (Polynomial.aeval x) (Polynomial.X_mul_divX_add q)
  rw [hO, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, ← hcdef, algebraMap_int_eq, eq_intCast] at key
  have hc' : (c : O) = x * -(Polynomial.aeval x q.divX) := by linear_combination key
  refine ⟨c.natAbs, Int.natAbs_ne_zero.2 hc, ?_⟩
  have hn : ((c.natAbs : ℕ) : O) = ((|c| : ℤ) : O) := by rw [← Int.natCast_natAbs, Int.cast_natCast]
  rcases abs_choice c with h | h
  · exact ⟨-(Polynomial.aeval x q.divX), by rw [hn, h, hc']⟩
  · exact ⟨Polynomial.aeval x q.divX, by rw [hn, h, Int.cast_neg, hc']; ring⟩

theorem eq_zero_of_act_pullback_eq_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (x : O), (OAct.pullback (spMap (algebraMap K (AlgebraicClosure Ω))) A α).act x = 1 → x = 0 := by
  rintro K Ω _ _ _ _ A _ _ hA ⟨d, hd, hsm⟩ l _ hl F _ _ O _ _ _ α x hx
  by_contra hx0
  have hl' : l.Prime := Fact.out
  set L := AlgebraicClosure Ω
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with htdef
  have hgp := isGrpPullback_pullback A t
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have h1 : ∀ y : ptOver K L ⟶ A, y ≫ α.act x = 1 := by
    intro y
    obtain ⟨v, rfl⟩ := e.surjective y
    have hv : e (v ≫ (OAct.pullback t A α).act x) = e v ≫ α.act x := by
      apply Over.OverMorphism.ext
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc]
      congr 1
      exact pullback.lift_fst _ _ _
    rw [← hv, hx, comp_one, map_one]
  obtain ⟨n, hn0, r, hr⟩ := exists_nat_eq_mul (F := F) hx0
  have h0 : α.act 0 = 1 := by
    have h00 := α.add 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (_root_.mul_one _).symm)
  have hnat : ∀ m : ℕ, ∀ y : ptOver K L ⟶ A, y ≫ α.act (m : O) = y ^ m := by
    intro m y
    induction m with
    | zero => rw [Nat.cast_zero, h0, comp_one, pow_zero]
    | succ m ih => rw [Nat.cast_succ, α.add, comp_mul, ih, α.one, Category.comp_id, pow_succ]
  have hall : ∀ y : ptOver K L ⟶ A, y ^ n = 1 := by
    intro y
    haveI := α.hom r
    rw [← hnat, hr, α.mul, ← Category.assoc, h1, one_comp]
  obtain ⟨v, m, hlm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl'.ne_one
  have hsub : ∀ y : ptOver K L ⟶ A, y ^ (l ^ (v + 1)) = 1 → y ^ (l ^ v) = 1 := by
    intro y hy
    have e1 : (y ^ l ^ v) ^ l = 1 := by rw [← pow_mul, ← pow_succ]; exact hy
    have e2 : (y ^ l ^ v) ^ m = 1 := by rw [← pow_mul, ← hnm]; exact hall y
    have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl').2 hlm
    have e3 := pow_gcd_eq_one.2 ⟨e1, e2⟩
    rwa [hcop.gcd_eq_one, pow_one] at e3
  have hlK : ∀ k : ℕ, ((l ^ k : ℕ) : K) ≠ 0 := fun k => by rw [Nat.cast_pow]; exact pow_ne_zero _ hl
  have cN := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ (v + 1)) (hlK _)
  have cv := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ v) (hlK _)
  have hfin : Finite {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [cv]; exact pow_ne_zero _ (pow_ne_zero _ hl'.ne_zero))
  have hle := Nat.card_le_card_of_injective
    (fun y : {y : ptOver K L ⟶ A // y ^ (l ^ (v + 1)) = 1} =>
      (⟨y.1, hsub y.1 y.2⟩ : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1}))
    (fun a b h => Subtype.ext (congrArg (fun z : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} => z.1) h))
  rw [cN, cv] at hle
  have hlt : (l ^ v) ^ (2 * d) < (l ^ (v + 1)) ^ (2 * d) :=
    Nat.pow_lt_pow_left (Nat.pow_lt_pow_right hl'.one_lt (Nat.lt_succ_self v)) (by omega)
  omega

end GlobalTheory.ActTrivialInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDifferentialKernelZeroGerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.KerGermInj

open GlobalTheory.AbLaw

theorem gs_id {P : Scheme.{0}} (O : P.Opens) (y : P) (hy : y ∈ O) (a : Γ(P, O)) :
    gs (𝟙 P) y O a = (P.presheaf.germ O y hy).hom a := by
  rw [gs_eq _ y O hy]; rfl

theorem gs_comp {Y Z X : Scheme.{0}} (f : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ h) z U a = (f.stalkMap z).hom (gs h (f z) U a) := by
  rw [← gs_pull f h z U hU, gs_eq f z (h ⁻¹ᵁ U) hU, gs_eq h (f z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply f (h ⁻¹ᵁ U) z hU _).symm

theorem fromSpecStalk_comp {R : Type} [CommRing R] {T : Scheme.{0}} (t : T ⟶ Sp R) (x : T) :
    T.fromSpecStalk x ≫ t =
      Spec.map (CommRingCat.ofHom ((T.presheaf.germ ⊤ x trivial).hom.comp (GlobalTheory.FormsLocus.cstT t))) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.FormsLocus.cstT]

theorem eq_zero : ∀ (R : Type) [CommRing R] (X T X' : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (Q : GlobalTheory.AbLaw.Perf f M) (t : T ⟶ Sp R) (φ : X' ⟶ X) (p : X' ⟶ T), IsPullback φ p f t → ∀ e : Fin Q.a → Γ(T, ⊤), (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)).mulVec e = 0 → (∀ (z : X') (i : Q.I), φ z ∈ Q.W i → ∑ k, gs p z ⊤ (e k) * gs φ z (Q.W i) (Q.u k i) = 0) → e = 0 := by
  intro R _ X T X' f M Q t φ p hpb e he hz
  funext k
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro x hx
  change (T.presheaf.germ ⊤ x hx).hom (e k) = (T.presheaf.germ ⊤ x hx).hom 0
  rw [map_zero]
  let ψ : Γ(T, ⊤) →+* T.presheaf.stalk x := (T.presheaf.germ ⊤ x hx).hom
  let ρ : R →+* T.presheaf.stalk x := ψ.comp (GlobalTheory.FormsLocus.cstT t)
  let g := T.fromSpecStalk x
  let fst := pullback.fst p g
  let snd := pullback.snd p g
  let π := fst ≫ φ
  have hsq : IsPullback π snd f (Spec.map (CommRingCat.ofHom ρ)) := by
    have hg : g ≫ t = Spec.map (CommRingCat.ofHom ρ) := fromSpecStalk_comp t x
    have h3 := (IsPullback.of_hasPullback p g).paste_horiz hpb
    rw [hg] at h3
    exact h3
  obtain ⟨E, hE⟩ := Q.sec _ ρ _ π snd hsq
  have hv : (Q.D₀.map ρ).mulVec (fun k => ψ (e k)) = 0 := by
    funext j
    have h1 := RingHom.map_mulVec ψ (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)) e j
    rw [he, Pi.zero_apply, map_zero, Matrix.map_map] at h1
    exact h1.symm
  have hloc : ∀ w : {v : Fin Q.a → T.presheaf.stalk x // (Q.D₀.map ρ).mulVec v = 0},
      (∀ i, ∑ k, cst snd (π ⁻¹ᵁ Q.W i) (w.1 k) * (π.app (Q.W i)).hom (Q.u k i) = 0) → E w = 0 := by
    intro w hw
    have hcov : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := Q.iSup_preimage (π := π)
    refine sec_eq_zero_of_local (L := M.pull π) (fun i => π ⁻¹ᵁ Q.W i) hcov
      (fun i => (fun _ => Q.ch i : (M.pull π).ι)) (fun i => le_pull M π (Q.le i)) (E w) ?_
    intro i
    exact (hE w i).trans (hw i)
  have h0 : E ⟨0, by rw [Matrix.mulVec_zero]⟩ = 0 :=
    hloc _ fun i => Finset.sum_eq_zero fun k _ => by
      have hc0 : cst snd (π ⁻¹ᵁ Q.W i) 0 = 0 := map_zero _
      exact (congrArg (· * _) hc0).trans (zero_mul _)
  have h1 : E ⟨fun k => ψ (e k), hv⟩ = 0 := by
    refine hloc _ fun i => ?_
    apply fn_ext
    intro y hy
    have hyi : φ (fst y) ∈ Q.W i := hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [gs_id _ y hy, gs_id _ y hy, map_zero, map_sum]
    simp only [map_mul]
    have hu : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs φ (fst y) (Q.W i) (Q.u k i)) := by
      intro k
      rw [← gs_id _ y hy, gs_pull (𝟙 _) π y (Q.W i) hyi, Category.id_comp]
      exact gs_comp fst φ y (Q.W i) hyi _
    have hc : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k)) := by
      intro k
      have hcond : fst ≫ p = snd ≫ g := pullback.condition
      have hA := congrArg (fun h => h.hom (e k)) (Scheme.fromSpecStalk_appTop (X := T) (x := x))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hA
      rw [← gs_id _ y hy, ← gs_comp fst p y ⊤ trivial, hcond]
      refine Eq.trans ?_ (gs_pull snd g y ⊤ trivial (e k))
      refine Eq.trans ?_ (congrArg (gs snd y (g ⁻¹ᵁ ⊤)) hA.symm)
      refine Eq.trans ?_ (gs_res snd y _ (show snd y ∈ g ⁻¹ᵁ ⊤ from trivial) _).symm
      refine Eq.trans (gs_res (𝟙 _) y le_top hy _) ?_
      refine Eq.trans (gs_pull (𝟙 _) snd y ⊤ trivial _) ?_
      rw [Category.id_comp]
      rfl
    have hsum : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) *
        ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k) * gs φ (fst y) (Q.W i) (Q.u k i)) := fun k => by
      rw [hc k, hu k, map_mul]
    simp only [hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hz (fst y) i hyi, map_zero]
  have h2 := congrFun (congrArg Subtype.val (E.injective (h1.trans h0.symm))) k
  exact h2

end GlobalTheory.KerGermInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdeal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sections_eqLocus_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom →
    ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R,
      ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first
  | exact @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | (apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFraction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem injective_ringHom_genericStalk_integralScheme (C : Scheme.{0}) [IsIntegral C] (q : C) (hq : q = genericPoint C)
    {A : Type} [CommRing A] [Nontrivial A] (φ : C.presheaf.stalk q →+* A) : Function.Injective φ := by
  subst hq
  exact RingHom.injective (φ : C.functionField →+* A)

theorem exists_fraction_genericStalk_germ_affineOpen (C : Scheme.{0}) [IsIntegral C] (V : C.Opens) (hV : IsAffineOpen V)
    (q : C) (hq : q = genericPoint C) (hqV : q ∈ V) (s : C.presheaf.stalk q) :
    ∃ a b : Γ(C, V), b ≠ 0 ∧ s * C.presheaf.germ V q hqV b = C.presheaf.germ V q hqV a := by
  subst hq
  haveI : Nonempty V := ⟨⟨_, hqV⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen (X := C) V hV
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (S := C.functionField) (nonZeroDivisors Γ(C, V)) s
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  have := IsLocalization.mk'_spec (S := C.functionField) a b
  rw [← hab]
  exact this

theorem germ_appLE_eq_stalkMap_germ_specField {K : Type} [Field K] (C : Scheme.{0}) (x : Sp K ⟶ C) (V : C.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (p : Sp K) (hp : x p ∈ V) (c : Γ(C, V)) :
    (Sp K).presheaf.germ ⊤ p (by simp) (x.appLE V ⊤ h c) = x.stalkMap p (C.presheaf.germ V (x p) hp c) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE]
  simp

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isGen_evAt_frac : ∀ (K : Type) [Field K] (C : Scheme.{0}) [IsIntegral C] (x : Sp K ⟶ C), IsGen x →
    ∀ V : C.Opens, (V : Set C).Nonempty → ∃ h : ⊤ ≤ x ⁻¹ᵁ V, Function.Injective (evAt x h) ∧
      (IsAffineOpen V → ∀ z : K, ∃ a b : Γ(C, V), b ≠ 0 ∧ z * evAt x h b = evAt x h a) := by
  intro K _ C _ x hx V hV
  haveI : IsDominant x := hx.1
  haveI : IsPreimmersion x := hx.2
  have hsub : ∀ p q : Sp K, p = q := fun p q => Subsingleton.elim (α := PrimeSpectrum K) p q
  have hgen : ∀ p : Sp K, x p = genericPoint C := by
    intro p
    apply ((genericPoint_spec C).eq _).symm
    rw [isGenericPoint_def]
    have hr : Set.range x = {x p} := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        rw [hsub q p]
        rfl
      · rintro rfl
        exact ⟨p, rfl⟩
    rw [← hr]
    exact x.denseRange.closure_range
  have hmem : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have h : ⊤ ≤ x ⁻¹ᵁ V := by
    intro p _
    show x p ∈ V
    rw [hgen p]
    exact hmem
  obtain ⟨p⟩ : Nonempty (Sp K) := ⟨(⊥ : PrimeSpectrum K)⟩
  have hp : x p ∈ V := by rw [hgen p]; exact hmem
  refine ⟨h, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : x.appLE V ⊤ h c = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of K)).inv.hom hc
      simpa [evAt] using this
    have h2 := germ_appLE_eq_stalkMap_germ_specField C x V h p hp c
    rw [h1, map_zero] at h2
    have h3 : C.presheaf.germ V (x p) hp c = 0 :=
      injective_ringHom_genericStalk_integralScheme C (x p) (hgen p) (x.stalkMap p).hom (by rw [← h2, map_zero])
    exact germ_injective_of_isIntegral (X := C) (x p) hp (by rw [h3, map_zero])
  · intro hA z
    obtain ⟨s, hs⟩ := x.stalkMap_surjective p
      ((Sp K).presheaf.germ ⊤ p (by simp) ((Scheme.ΓSpecIso (.of K)).inv.hom z))
    obtain ⟨a, b, hb, hab⟩ := exists_fraction_genericStalk_germ_affineOpen C V hA (x p) (hgen p) hp s
    refine ⟨a, b, hb, ?_⟩
    have e := congrArg (x.stalkMap p).hom hab
    rw [map_mul, hs, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← map_mul] at e
    have e2 := germ_injective_of_isIntegral (X := Sp K) p (by simp) e
    have e3 := congrArg (Scheme.ΓSpecIso (.of K)).hom.hom e2
    simpa [evAt] using e3

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalk
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef

theorem evAt_eq_comp {R : Type} [CommRing R] {X : Scheme.{0}} (b : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) :
    CommRingCat.ofHom (evAt b h) = b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := rfl

theorem evAt_spMap_comp (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)) :
    evAt (spMap φ ≫ b) h' f = φ (evAt b h f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE (spMap φ) b U ⊤ ⊤ h le_rfl
  have e3 : (spMap φ).appLE ⊤ ⊤ le_rfl = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (spMap φ ≫ b).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ := by
    rw [← e2, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_comp (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)) :
    evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE b g V U ⊤ e h
  have e4 : (b ≫ g).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      g.appLE V U e ≫ b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_res (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)) :
    evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f := by
  have e2 := Scheme.Hom.map_appLE b h' (homOfLE e).op
  have e4 : X.presheaf.map (homOfLE e).op ≫ b.appLE U' ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem top_le_iff_closedPoint_mem (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X)
    (U : X.Opens) : ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U := by
  refine ⟨fun h => h (Set.mem_univ _), fun hb q _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum R)).map b.continuous).mem_open U.2 hb

theorem eq_of_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (he : evAt b h = evAt b' h') : b = b' := by
  have k0 : b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b'.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← evAt_eq_comp, ← evAt_eq_comp, he]
  have k : b.appLE U ⊤ h = b'.appLE U ⊤ h' := (cancel_mono _).1 k0
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec b hU (isAffineOpen_top (Sp R)) h
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec b' hU (isAffineOpen_top (Sp R)) h'
  rw [k] at e1
  have e3 := e1.symm.trans e2
  rw [IsAffineOpen.fromSpec_top] at e3
  exact (cancel_epi _).1 e3

theorem exists_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens) (hU : IsAffineOpen U)
    (φ : Γ(X, U) →+* R) : ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, h, ?_⟩
  have e1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) hU.fromSpec U ⊤ ⊤ hfs le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : CommRingCat.ofHom (evAt (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) h) =
      CommRingCat.ofHom φ := by
    rw [evAt_eq_comp, ← e2, e1, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_assoc _
  exact congrArg CommRingCat.Hom.hom e4

theorem evAt_fromSpecStalk' (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R)
    (U : X.Opens) (hp : p ∈ U) :
    ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U,
      ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f =
        φ (X.presheaf.germ U p hp f) := by
  have h0 : ⊤ ≤ X.fromSpecStalk p ⁻¹ᵁ U := fun q _ =>
    ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum _)).map (X.fromSpecStalk p).continuous).mem_open U.2
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hp)
  refine ⟨fun q _ => h0 (Set.mem_univ _), fun s => ?_⟩
  have e1 : (X.fromSpecStalk p).appLE U ⊤ h0 = X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (Category.comp_id _))
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) (X.fromSpecStalk p) U ⊤ ⊤ h0 le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p).appLE U ⊤ (fun q _ => h0 (Set.mem_univ _)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = X.presheaf.germ U p hp ≫ CommRingCat.ofHom φ := by
    rw [← e2, e1, e3, Category.assoc, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact congrArg (_ ≫ ·) ((Scheme.ΓSpecIso (X.presheaf.stalk p)).inv_hom_id_assoc _)
  exact congrArg (fun ψ => ψ.hom s) e4

theorem evAt_calculus : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)), evAt (spMap φ ≫ b) h' f = φ (evAt b h f)) ∧ (∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)), evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f)) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)), evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f) ∧ (∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U : X.Opens), ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U), evAt b h = evAt b' h' → b = b') ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ φ : Γ(X, U) →+* R, ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R) (U : X.Opens) (hp : p ∈ U), ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U, ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f = φ (X.presheaf.germ U p hp f)) :=
  ⟨evAt_spMap_comp, evAt_comp, evAt_res, top_le_iff_closedPoint_mem, eq_of_evAt_eq, exists_evAt_eq,
    evAt_fromSpecStalk'⟩

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω)) (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, (∀ σ ∈ H, specAut σ ≫ x = x) → ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left, spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_fixedField_point | exact GlobalTheory.Published.AbVarRed.exists_fixedField_point | (intros; apply GlobalTheory.Published.AbVarRed.exists_fixedField_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTateFE
section
theorem GlobalTheory.Top.heckeTateFE : GlobalTheory.Published.HeckeTateFunctionalEquation :=
  GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation
end

