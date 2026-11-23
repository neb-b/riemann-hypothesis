module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowKillsOnCompactOfLocal
section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem pow_kills_on_compact_of_local : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens), IsCompact (W : Set S) → ∀ (s c : Γ(S, W)), (∀ y ∈ W, ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0) → ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom (s ^ n * c) = 0 := by
  intro S Φ W hW s c h
  have h' : ∀ y : W, ∃ (V : S.Opens) (hV : V ≤ W), y.1 ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 :=
    fun y => h y.1 y.2
  choose V hV hyV n hn using h'
  obtain ⟨F, hF⟩ := hW.elim_finite_subcover (fun y : W => (V y : Set S)) (fun y => (V y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩)
  refine ⟨∑ y ∈ F, n y, fun T t hΦ => ?_⟩
  apply TopCat.Presheaf.section_ext T.sheaf (t ⁻¹ᵁ W)
  intro x hx
  have hxW : t.base x ∈ (W : Set S) := hx
  obtain ⟨y, hyF, hxy⟩ := Set.mem_iUnion₂.1 (hF hxW)
  have hle : t ⁻¹ᵁ V y ≤ t ⁻¹ᵁ W := fun z hz => hV y hz
  have hxV : x ∈ t ⁻¹ᵁ V y := hxy
  have hN : n y ≤ ∑ y ∈ F, n y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyF
  have key : (T.presheaf.map (homOfLE hle).op).hom ((t.app W).hom (s ^ (∑ y ∈ F, n y) * c)) = 0 := by
    have e := congrArg (fun φ => φ.hom (s ^ (∑ y ∈ F, n y) * c)) (t.naturality (homOfLE (hV y)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    have e2 : s ^ (∑ y ∈ F, n y) * c = s ^ (∑ y ∈ F, n y - n y) * (s ^ n y * c) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]
    refine Eq.trans ?_ (e.symm.trans ?_)
    · rfl
    · rw [e2, map_mul, map_mul, hn y T t hΦ, mul_zero]
  have := congrArg (T.presheaf.germ (t ⁻¹ᵁ V y) x hxV).hom key
  rw [TopCat.Presheaf.germ_res_apply, map_zero] at this
  exact this.trans (map_zero _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLinearIndependentOfIsFractionRing
section
open scoped Matrix
open IntermediateField

namespace GlobalTheory

theorem exists_pow_linearIndependent_of_isFractionRing (O F : Type) [CommRing O] [Field F]
    [NumberField F] [Algebra O F] [IsFractionRing O F] :
    ∃ α : O, LinearIndependent ℚ (fun i : Fin (Module.finrank ℚ F) => algebraMap O F (α ^ (i : ℕ))) := by
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O) γ
  have hfin : Finite (IntermediateField ℚ F) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ F ⟨γ, hγ⟩
  obtain ⟨t, t', htt, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun t : ℕ => ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯)
  have h1 : algebraMap O F x + (t : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := mem_adjoin_simple_self _ _
  have h2 : algebraMap O F x + (t' : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := by
    rw [he]; exact mem_adjoin_simple_self _ _
  set L := ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ with hL
  have hyL : algebraMap O F y ∈ L := by
    have hd : ((t : F) - t') * algebraMap O F y ∈ L := by
      have := L.sub_mem h1 h2
      convert this using 1; ring
    have htt' : ((t : F) - t') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast htt)
    have hc : ((t : F) - t') ∈ L := L.sub_mem (L.natCast_mem t) (L.natCast_mem t')
    have := L.mul_mem (L.inv_mem hc) hd
    rwa [← mul_assoc, inv_mul_cancel₀ htt', one_mul] at this
  have hxL : algebraMap O F x ∈ L := by
    have := L.sub_mem h1 (L.mul_mem (L.natCast_mem t) hyL)
    simpa using this
  have hγL : γ ∈ L := hxy ▸ L.div_mem hxL hyL
  have htop : L = ⊤ := by
    rw [eq_top_iff, ← hγ, adjoin_simple_le_iff]; exact hγL
  refine ⟨x + t • y, ?_⟩
  have ha : algebraMap O F (x + t • y) = algebraMap O F x + (t : F) * algebraMap O F y := by
    rw [map_add (f := _), map_nsmul, nsmul_eq_mul]
  have hint : IsIntegral ℚ (algebraMap O F (x + t • y)) := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly ℚ (algebraMap O F (x + t • y))).natDegree = Module.finrank ℚ F := by
    rw [← adjoin.finrank hint, ha, ← hL, htop, finrank_top']
  have h' := (linearIndependent_pow (K := ℚ) (algebraMap O F (x + t • y))).comp
    (Fin.cast hdeg.symm) (Fin.cast_injective _)
  have hf : (fun i : Fin (Module.finrank ℚ F) => algebraMap O F ((x + t • y) ^ (i : ℕ))) =
      (fun i : Fin (minpoly ℚ (algebraMap O F (x + t • y))).natDegree =>
        algebraMap O F (x + t • y) ^ (i : ℕ)) ∘ Fin.cast hdeg.symm := by
    ext i; simp [map_pow]
  rw [hf]; exact h'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulAppEqZeroNearOfRepresented
section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

private theorem app_comp_ι_eq_zero_iff {T S : Scheme.{0}} (U : S.Opens) (g : T ⟶ U) (V : U.toScheme.Opens) (x : Γ(S, U.ι ''ᵁ V)) :
    ((g ≫ U.ι).app (U.ι ''ᵁ V)).hom x = 0 ↔ (g.app V).hom x = 0 := by
  have e : (g ≫ U.ι).app (U.ι ''ᵁ V) = g.app V ≫ T.presheaf.map (eqToHom (by simp)).op := by
    simp only [Scheme.Hom.comp_app, Scheme.Opens.ι_app]
    refine (g.naturality (homOfLE (U.ι.preimage_image_eq V).le).op).trans ?_
    congr 2
  rw [e]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

private theorem restrict_app_eq_zero_iff {T S : Scheme.{0}} (f : T ⟶ S) (U : S.Opens) (V : U.toScheme.Opens) (a : Γ(S, U.ι ''ᵁ V)) :
    ((f ∣_ U).app V).hom a = 0 ↔ (f.app (U.ι ''ᵁ V)).hom a = 0 := by
  rw [morphismRestrict_app]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

private theorem app_res_eq_zero {S T : Scheme.{0}} (t : T ⟶ S) {V W : S.Opens} (h : V ≤ W) (b : Γ(S, W))
    (hb : (t.app W).hom b = 0) : (t.app V).hom ((S.presheaf.map (homOfLE h).op).hom b) = 0 := by
  have e := congrArg (fun φ => φ.hom b) (t.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, hb, map_zero]

theorem exists_pow_mul_app_eq_zero_near_of_represented : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → ∀ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), IsClosedImmersion i → (∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∀ (W : S.Opens) (s c : Γ(S, W)), (∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app (S.basicOpen s)).hom ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) = 0) → ∀ y : S, y ∈ U → y ∈ W → ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
  intro S Φ hstab U Z i hi hrep W s c hc y hyU hyW
  have hm : (⟨y, hyU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ W := hyW
  obtain ⟨V', hV'aff, hyV', hV'le⟩ := (Opens.isBasis_iff_nbhd.mp U.toScheme.isBasis_affineOpens) hm
  have hV : U.ι ''ᵁ V' ≤ W := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hx
    exact hV'le hx'
  refine ⟨U.ι ''ᵁ V', hV, ⟨⟨y, hyU⟩, hyV', rfl⟩, ?_⟩
  set V : S.Opens := U.ι ''ᵁ V' with hVdef
  set p : Z ⟶ S := i ≫ U.ι with hpdef
  let cV : Γ(S, V) := (S.presheaf.map (homOfLE hV).op).hom c
  let sV : Γ(S, V) := (S.presheaf.map (homOfLE hV).op).hom s
  have hpre : p ⁻¹ᵁ V = i ⁻¹ᵁ V' := by
    rw [hpdef, Scheme.Hom.comp_preimage, hVdef, U.ι.preimage_image_eq V']
  have hcpt : IsCompact ((p ⁻¹ᵁ V : Z.Opens) : Set Z) := by
    rw [hpre]
    exact QuasiCompact.isCompact_preimage (f := i) _ V'.2 hV'aff.isCompact
  have hΦi : Φ Z p := (hrep Z i).2 ⟨𝟙 _, Category.id_comp _⟩
  have h0 := hc Z p hΦi
  have h1 := app_res_eq_zero p (inf_le_right : V ⊓ S.basicOpen s ≤ S.basicOpen s) _ h0
  have hres : (S.presheaf.map (homOfLE (inf_le_left : V ⊓ S.basicOpen s ≤ V)).op).hom cV =
      (S.presheaf.map (homOfLE (inf_le_right : V ⊓ S.basicOpen s ≤ S.basicOpen s)).op).hom
        ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) := by
    simp only [cV, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have key : ∀ (O : Z.Opens) (_ : O = p ⁻¹ᵁ (V ⊓ S.basicOpen s)) (h : O ≤ p ⁻¹ᵁ V),
      (Z.presheaf.map (homOfLE h).op).hom ((p.app V).hom cV) = 0 := by
    rintro O rfl h
    have e := congrArg (fun φ => φ.hom cV) (p.naturality (homOfLE (inf_le_left : V ⊓ S.basicOpen s ≤ V)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.symm.trans ?_
    rw [hres]
    exact h1
  have hO : Z.basicOpen ((p.app V).hom sV) = p ⁻¹ᵁ (V ⊓ S.basicOpen s) := by
    rw [← Scheme.preimage_basicOpen, Scheme.basicOpen_res]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Z hcpt
    ((p.app V).hom cV) ((p.app V).hom sV) (key _ hO _)
  have hpa : (p.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
    rw [map_mul, map_pow, map_mul, map_pow]
    exact hn
  have hia := (app_comp_ι_eq_zero_iff U i V' _).1 hpa
  refine ⟨n, fun T t ht => ?_⟩
  have ht' : Φ _ ((t ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact hstab _ _ t _ ht
  obtain ⟨z, hz⟩ := (hrep _ (t ∣_ U)).1 ht'
  refine (restrict_app_eq_zero_iff t U V' _).1 ?_
  rw [← hz, Scheme.Hom.comp_app]
  exact (congrArg (fun x => (z.app (i ⁻¹ᵁ V')).hom x) hia).trans (map_zero _)
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemAdjoinOfLocalizationAway
section
open Algebra

theorem GlobalTheory.adjoin_mem_of_away_localization {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  have hg : algebraMap A A' (algebraMap R A g) = algebraMap R A' g :=
    (IsScalarTower.algebraMap_apply R A A' g).symm
  have key : ∀ y ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ k : ℕ, ∃ z ∈ Algebra.adjoin R T,
      algebraMap A A' z = algebraMap R A' g ^ k * y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨0, a, Algebra.subset_adjoin ha, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨r0, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A r0, Subalgebra.algebraMap_mem _ r0, ?_⟩
      simp only at hr
      rw [← IsScalarTower.algebraMap_apply R A A', IsScalarTower.algebraMap_apply R R' A', ← hr,
        map_mul, ← IsScalarTower.algebraMap_apply R R' A', map_pow, mul_comm]
    | add x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, algebraMap R A g ^ k2 * z1 + algebraMap R A g ^ k1 * z2, ?_, ?_⟩
      · refine add_mem (mul_mem ?_ hz1) (mul_mem ?_ hz2) <;>
          (rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _)
      · rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, hg, e1, e2]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, z1 * z2, mul_mem hz1 hz2, ?_⟩
      rw [map_mul, e1, e2]; ring
  obtain ⟨k, z, hz, e⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ k * b) = 0 := by
    rw [map_sub, map_mul, map_pow, hg, e, sub_self]
  obtain ⟨⟨_, c, rfl⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  refine ⟨c + k, ?_⟩
  have : algebraMap R A g ^ (c + k) * b = algebraMap R A g ^ c * z := by
    simp only at hc
    rw [mul_sub, sub_eq_zero] at hc
    rw [hc, pow_add]; ring
  rw [this]
  refine mul_mem ?_ hz
  rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _

theorem GlobalTheory.adjoin_mem_of_away_localization' : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  intros R A R' A' _ _ _ _ _ _ _ _ _ _ _ g _ _ T b h
  exact GlobalTheory.adjoin_mem_of_away_localization g T b h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPowMemRangeIncludeRight
section
namespace GlobalTheory.PowerInRangeTensorRight

open TensorProduct

theorem exists_pow_pow_mem_range_includeRight (k K B : Type) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B] (q : ℕ) [ExpChar k q]
    (z : TensorProduct k K B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      AlgHom.range (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k K B) := by
  rcases subsingleton_or_nontrivial (TensorProduct k K B) with hs | hnt
  · exact ⟨0, by rw [Subsingleton.elim (z ^ q ^ 0) 0]; exact zero_mem _⟩
  have : ExpChar (TensorProduct k K B) q :=
    expChar_of_injective_algebraMap (algebraMap k (TensorProduct k K B)).injective q
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x b =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k q x
    refine ⟨n, (AlgHom.mem_range _).mpr ⟨c • b ^ q ^ n, ?_⟩⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, ← hc,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n1, h1⟩ := hx
    obtain ⟨n2, h2⟩ := hy
    refine ⟨n1 + n2, ?_⟩
    have e1 : x ^ q ^ (n1 + n2) = (x ^ q ^ n1) ^ q ^ n2 := by rw [pow_add, pow_mul]
    have e2 : y ^ q ^ (n1 + n2) = (y ^ q ^ n2) ^ q ^ n1 := by rw [pow_add, mul_comm, pow_mul]
    rw [add_pow_expChar_pow, e1, e2]
    exact add_mem (pow_mem h1 _) (pow_mem h2 _)

end GlobalTheory.PowerInRangeTensorRight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSeriesOfNoPoleAwayUniformizerX
section
open scoped LaurentSeries

namespace GlobalTheory.PowerSeriesNoPole

open scoped LaurentSeries in
open PowerSeries in
private lemma C_dvd_iff_map_mk_eq_zero {A : Type} [CommRing A] (ϖ : A) (f : PowerSeries A) :
    C ϖ ∣ f ↔ PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    ext d
    simp [coeff_C_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · intro h
    have hd : ∀ d, ϖ ∣ coeff d f := fun d ↦ by
      have := congrArg (coeff d) h
      simpa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    choose q hq using hd
    refine ⟨mk q, ?_⟩
    ext d
    simp [coeff_C_mul, hq d]

open scoped LaurentSeries in
open PowerSeries in
private lemma prime_C_powerSeries {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (hϖ : Prime ϖ) :
    Prime (C ϖ : PowerSeries A) := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ
  refine ⟨fun h ↦ hϖ.ne_zero (by simpa using congrArg (coeff 0) h), fun hu ↦ hϖ.not_unit ?_,
    fun f g h ↦ ?_⟩
  · simpa using hu.map (constantCoeff (R := A))
  · rw [C_dvd_iff_map_mk_eq_zero, C_dvd_iff_map_mk_eq_zero]
    rw [C_dvd_iff_map_mk_eq_zero, map_mul] at h
    exact mul_eq_zero.mp h


open scoped LaurentSeries in
open PowerSeries in
theorem _root_.GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap (A : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : Irreducible ϖ) (k : A →+* ℂ) (hk : Function.Injective k)
    (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S]
    (ι : S →+* ℂ⸨X⸩)
    (hι : ∀ s : PowerSeries A,
      ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s))
    (v : S) (hv : ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range)
    (hst : ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧
      v * algebraMap _ S t = algebraMap _ S s) :
    ∃ s : PowerSeries A, v = algebraMap _ S s := by
  obtain ⟨s, t, ht, hvt⟩ := hst
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (C ϖ * X : PowerSeries A) v
  rw [← map_pow] at ha
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hu0 : (C ϖ * X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h ↦ hϖ0 (by simpa using congrArg (coeff 0) h)) X_ne_zero
  have hinj : Function.Injective (algebraMap (PowerSeries A) S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hu0)
  have hat : a * t = s * (C ϖ * X) ^ n := by
    apply hinj
    rw [map_mul, map_mul, ← ha, ← hvt]
    ring
  obtain ⟨g, hg⟩ := hv
  have hga : g * PowerSeries.map k ((C ϖ * X) ^ n) = PowerSeries.map k a := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_mul, hg, ← hι, ← hι, ← map_mul, ha]
  have hXa : (X : PowerSeries A) ^ n ∣ a := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    apply hk
    rw [map_zero, ← PowerSeries.coeff_map, ← hga]
    have hdvd : (X : PowerSeries ℂ) ^ n ∣ g * PowerSeries.map k ((C ϖ * X) ^ n) :=
      ⟨g * C (k ϖ) ^ n, by rw [map_pow, map_mul, map_C, map_X, mul_pow]; ring⟩
    exact (PowerSeries.X_pow_dvd_iff.mp hdvd) d hd
  obtain ⟨a₁, rfl⟩ := hXa
  have ha₁ : a₁ * t = (C ϖ) ^ n * s := by
    have hX : (X : PowerSeries A) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [mul_pow] at hat
    linear_combination hat
  have hp : Prime (C ϖ : PowerSeries A) := prime_C_powerSeries hϖ.prime
  obtain ⟨a₂, rfl⟩ := hp.pow_dvd_of_dvd_mul_right n ht ⟨s, ha₁⟩
  refine ⟨a₂, ?_⟩
  have hunit : IsUnit (algebraMap (PowerSeries A) S ((C ϖ * X) ^ n)) :=
    IsLocalization.map_units S (⟨(C ϖ * X) ^ n, n, rfl⟩ : Submonoid.powers (C ϖ * X))
  apply hunit.mul_left_inj.mp
  rw [ha, ← map_mul]
  congr 1
  ring

end GlobalTheory.PowerSeriesNoPole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChange
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_presentation_matrix : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  intro R B M _ _ _ _ _ n m π hπ r hr hP
  let e := TensorProduct.piScalarRight R B B (Fin n)
  let πB : (Fin n → B) →ₗ[B] B ⊗[R] M := (π.baseChange B) ∘ₗ e.symm.toLinearMap
  have hπB : Function.Surjective πB := (LinearMap.lTensor_surjective B hπ).comp e.symm.surjective
  obtain ⟨i, hi⟩ := Module.projective_lifting_property πB LinearMap.id hπB
  let v : Fin n → Fin n → B := fun a => i ((1 : B) ⊗ₜ[R] π (Pi.single a 1))
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R r
  have hex : Function.Exact f π := by
    rw [LinearMap.exact_iff, Fintype.range_linearCombination, hr]
  have hexB := lTensor_exact B hex hπ
  let N : Submodule B (Fin n → B) := Submodule.span B (Set.range fun b l => algebraMap R B (r b l))
  have hker : ∀ y, πB y = 0 → y ∈ N := by
    intro y hy
    have h0 : (π.lTensor B) (e.symm y) = 0 := by
      have := hy
      simp only [πB, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
      rwa [LinearMap.baseChange_eq_ltensor] at this
    obtain ⟨z, hz⟩ := (hexB _).1 h0
    have hy' : y = e (f.lTensor B z) := by rw [hz, LinearEquiv.apply_symm_apply]
    rw [hy']
    clear hz hy' h0 hy
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c =>
        have : e ((f.lTensor B) (x ⊗ₜ c)) = ∑ b, (x * algebraMap R B (c b)) • (fun l => algebraMap R B (r b l)) := by
          ext l
          simp [e, f, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def, Finset.mul_sum,
            Finset.sum_mul, mul_comm, mul_left_comm]
        rw [this]
        exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem ha hb
  have hπv : ∀ a, πB (v a - Pi.single a 1) = 0 := by
    intro a
    have h1 : πB (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := LinearMap.congr_fun hi _
    have h2 : e.symm (Pi.single a 1) = (1 : B) ⊗ₜ[R] (Pi.single a 1 : Fin n → R) := by
      rw [LinearEquiv.symm_apply_eq]
      ext l
      simp [e, Pi.single_apply]
    rw [map_sub, h1]
    simp [πB, h2]
  choose w hw using fun a => (Submodule.mem_span_range_iff_exists_fun B).1 (hker _ (hπv a))
  refine ⟨v, w, fun b l => ?_, fun a l => ?_⟩
  · have hrb : π (r b) = 0 := by
      have : r b ∈ LinearMap.ker π := hr ▸ Submodule.subset_span ⟨b, rfl⟩
      exact this
    have hsum : (1 : B) ⊗ₜ[R] π (r b) = ∑ a, algebraMap R B (r b a) • ((1 : B) ⊗ₜ[R] π (Pi.single a 1)) := by
      conv_lhs => rw [← Finset.univ_sum_single (r b)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, TensorProduct.tmul_sum, algebraMap_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← TensorProduct.tmul_smul, ← map_smul]
      congr 2
      ext j
      simp [Pi.single_apply]
    have h1 : ∑ a, algebraMap R B (r b a) • v a = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, ← map_smul, ← map_sum, ← hsum, hrb, TensorProduct.tmul_zero, map_zero]
    have := congrFun h1 l
    simpa [Finset.sum_apply, Algebra.smul_def] using this
  · have := congrFun (hw a) l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply] at this
    rw [this]
    simp [eq_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNatCastMemPowOfRingHom
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_prime_natCast_mem_pow_of_ringHom :
    ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  intro F H _ _ _ _ f w p n hp
  letI : Algebra F H := f.toAlgebra
  haveI := w.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H) w.asIdeal
  refine ⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot P, ?_⟩
  have hle : w.asIdeal.map (algebraMap (𝓞 F) (𝓞 H)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hP.over
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 H)) hp
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono hle n h1

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeInvariantsFiniteGroupAndFinite
section
namespace GlobalTheory

theorem finiteType_invariants_and_finite (R : Type) [CommRing R] [IsNoetherianRing R]
    (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C']
    (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C')
    (hC : ∀ x, x ∈ C ↔ ∀ σ, act σ x = x) :
    Algebra.FiniteType R C ∧ Module.Finite C C' := by
  letI : MulSemiringAction G C' := MulSemiringAction.compHom C' act
  haveI : Algebra.IsInvariant C C' G := ⟨fun b hb => ⟨⟨b, (hC b).2 fun σ => hb σ⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral C C' := Algebra.IsInvariant.isIntegral C C' G
  haveI : Algebra.FiniteType C C' := Algebra.FiniteType.of_restrictScalars_finiteType R C C'
  haveI hfin : Module.Finite C C' := Algebra.IsIntegral.finite
  refine ⟨⟨fg_of_fg_of_fg (A := R) (B := C) (C := C') Algebra.FiniteType.out
    hfin.fg_top Subtype.val_injective⟩, hfin⟩

end GlobalTheory
end

