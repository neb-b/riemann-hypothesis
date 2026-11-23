module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfIsUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false

namespace GlobalTheory.UPel.HT.ES.KerUPart

theorem exists_elt {O : Type} [CommRing O] (I J : Ideal O) (q : O) (h : IsCoprime I J)
    (hq : I * J ≤ Ideal.span {q}) (E : ℕ) :
    ∃ α : O, (∀ a ∈ I ^ E, ∃ u v, a = u * α + v * q ^ E) ∧ ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ v, α = a + v * q ^ E := by
  have hm : ∀ a ∈ I ^ E, ∀ b ∈ J ^ E, ∃ v, a * b = v * q ^ E := fun a ha b hb => by
    have h1 : a * b ∈ (I * J) ^ E := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    have h2 := Ideal.pow_right_mono hq E h1
    rw [Ideal.span_singleton_pow] at h2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨v, hv.symm⟩
  have hc : ∀ e : ℕ, ∃ a ∈ I ^ e, ∃ b ∈ J ^ E, a + b = 1 := fun e =>
    Ideal.isCoprime_iff_exists.1 (h.pow (m := e) (n := E))
  obtain ⟨α, hα, β, hβ, hαβ⟩ := hc E
  refine ⟨α, fun a ha => ?_, fun e => ?_⟩
  · obtain ⟨v, hv⟩ := hm a ha β hβ
    exact ⟨a, v, by linear_combination hv - a * hαβ⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := hc e
    obtain ⟨v, hv⟩ := hm α hα b hb
    exact ⟨α * a, Ideal.mul_mem_left _ _ ha, v, by linear_combination hv - α * hab⟩

theorem exists_conj {p : ℕ} [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤)
    (hu : uIdeal D r ≤ w) :
    ∃ J : Ideal (𝓞 D.F), IsCoprime (uIdeal D r) J ∧ uIdeal D r * J ≤ Ideal.span {(p : 𝓞 D.F)} := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hM : (D.ω - r) * (D.bar D.ω - r) = ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) := by
    push_cast
    linear_combination hnm - r * htr
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hn
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hn
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, ← hM, Int.cast_one, Int.cast_natCast] at h
    refine hw ((Ideal.eq_top_iff_one w).2 (h ▸ w.add_mem (w.mul_mem_left _ (hu (p_mem_uIdeal D r)))
      (w.mul_mem_left _ (w.mul_mem_right _ (hu (sub_mem_uIdeal D r))))))
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Int.cast_mul, Int.cast_natCast] at hM
  refine ⟨Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r}, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 D.disc_p
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    push_cast at h
    refine Ideal.isCoprime_iff_exists.2 ⟨x * p + y * (D.ω - D.bar D.ω) * (D.ω - r),
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ (p_mem_uIdeal D r)) (Ideal.mul_mem_left _ _ (sub_mem_uIdeal D r)),
      -(y * (D.ω - D.bar D.ω)) * (D.bar D.ω - r),
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_⟩
    linear_combination h + y * (D.ω + D.bar D.ω + D.tr) * htr - 4 * y * hnm
  · rw [uIdeal, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    rintro z (rfl | rfl | rfl | rfl)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · exact Ideal.mem_span_singleton.2 (dvd_mul_left _ _)
    · exact Ideal.mem_span_singleton.2 (hM ▸ dvd_mul_right _ _)

section Grp

variable {S : Scheme.{0}}

theorem comp_mulN {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) : x ≫ mulN A n = x ^ n := by
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem exists_zeroLocus {B Z : Over S} [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (g : Z ⟶ B) (hg : g ^ n = 1) :
    ∃ (Y : Over S) (j : Y ⟶ Z), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ Z), (∃ z, z ≫ j = y) ↔ y ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B hn
  have hsec := GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion B n).hom _
    (Over.w (GlobalTheory.HTTorsRep.torsEta (A := B) n))
  have := GlobalTheory.HTTorsRep.mono_of_unit (GlobalTheory.HTTorsRep.torsEta (A := B) n)
  have := GlobalTheory.HTTorsRep.mono_ι (A := B) n
  have hEta : GlobalTheory.HTTorsRep.torsEta n ≫ torsion.ι B n = η[B] :=
    pullback.lift_fst _ _ _
  let g' : Z ⟶ torsion B n := pullback.lift g (toUnit Z) (by rw [comp_mulN, hg]; rfl)
  have hg' : g' ≫ torsion.ι B n = g := pullback.lift_fst _ _ _
  have hP := (IsPullback.of_hasPullback g' (GlobalTheory.HTTorsRep.torsEta n)).map (Over.forget S)
  refine ⟨pullback g' (GlobalTheory.HTTorsRep.torsEta n), pullback.fst _ _, inferInstance,
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2, fun W y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩
    rw [← hg', Category.assoc, ← Category.assoc (pullback.fst g' _), pullback.condition, Category.assoc,
      hEta, ← Category.assoc, toUnit_unique (z ≫ pullback.snd g' _) (toUnit W)]
    rfl
  · refine ⟨pullback.lift y (toUnit W) ?_, pullback.lift_fst _ _ _⟩
    rw [← cancel_mono (torsion.ι B n), Category.assoc, hg', h, Category.assoc, hEta]
    rfl

theorem exists_subgroup {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C]
    [IsCommMonObj C] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hC : IsAbelianScheme C) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (f : A ⟶ B) (g : A ⟶ C) [IsMonHom f] [IsMonHom g] :
    ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧
      ∀ (T : Over S) (x : T ⟶ A), InSub i x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
  obtain ⟨-, hf, he⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  have := GlobalTheory.HTTorsRep.mono_ι (A := A) n
  have h0 : torsion.ι A n ^ n = 1 := by rw [← comp_mulN, GlobalTheory.HTTorsRep.ι_mulN]; rfl
  obtain ⟨Y, j, hj, hjo, hjc, hY⟩ := exists_zeroLocus hB hn (torsion.ι A n ≫ f)
    (by rw [← MonObj.pow_comp, h0, MonObj.one_comp])
  obtain ⟨K, k, hk, hko, hkc, hK⟩ := exists_zeroLocus hC hn (j ≫ torsion.ι A n ≫ g)
    (by rw [← MonObj.comp_pow, ← MonObj.pow_comp, h0, MonObj.one_comp, MonObj.comp_one])
  have hpts : ∀ (T : Over S) (x : T ⟶ A),
      InSub (k ≫ j ≫ torsion.ι A n) x ↔ x ^ n = 1 ∧ x ≫ f = 1 ∧ x ≫ g = 1 := by
    intro T x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← MonObj.comp_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, h0]
        simp only [MonObj.comp_one]
      · simpa only [Category.assoc] using (hY T (z ≫ k ≫ j)).1 ⟨z ≫ k, Category.assoc _ _ _⟩
      · simpa only [Category.assoc] using (hK T (z ≫ k)).1 ⟨z, rfl⟩
    · rintro ⟨h1, h2, h3⟩
      let y : T ⟶ torsion A n := pullback.lift x (toUnit T) (by rw [comp_mulN, h1]; rfl)
      have hy : y ≫ torsion.ι A n = x := pullback.lift_fst _ _ _
      obtain ⟨z, hz⟩ := (hY T y).2 (by rw [← Category.assoc, hy, h2])
      obtain ⟨u, hu⟩ := (hK T z).2 (by rw [← Category.assoc, hz, ← Category.assoc, hy, h3])
      exact ⟨u, by rw [← Category.assoc, hu, ← Category.assoc, hz, hy]⟩
  have hm : Mono (k ≫ j ≫ torsion.ι A n) := inferInstance
  have hfin : IsFinite K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  have het : Etale K.hom := by rw [← Over.w k, ← Over.w j]; infer_instance
  generalize k ≫ j ≫ torsion.ι A n = i at hpts hm
  obtain ⟨i1, i2, i3⟩ := (hpts K i).1 ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨G, hG⟩ := GlobalTheory.overScheme_grpObj_of_mono_factor S A K i hm
    (by
      have e : (i ⊗ₘ i) ≫ μ[A] = (fst K K ≫ i) * (snd K K ≫ i) := by
        rw [Hom.mul_def]; congr 1
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, i1]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i2]; simp
      · rw [MonObj.mul_comp, Category.assoc, Category.assoc, i3]; simp)
    (by
      have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [e]
      exact (hpts _ _).2 ⟨one_pow _, MonObj.one_comp _, MonObj.one_comp _⟩)
    (by
      have e : i ≫ ι[A] = i⁻¹ := rfl
      rw [e]
      refine (hpts _ _).2 ⟨?_, ?_, ?_⟩
      · rw [inv_pow, i1, inv_one]
      · rw [GrpObj.inv_comp, i2, inv_one]
      · rw [GrpObj.inv_comp, i3, inv_one])
  exact ⟨K, G, i, hG, hm, hfin, het, hpts⟩

end Grp

theorem charZero_of_isUnit {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : Γ(S, ⊤))) (k : Type) [Field k] (x : Sp k ⟶ S) :
    CharZero k := by
  have hpk : (p : k) ≠ 0 := by
    have := hp.map (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
    rw [map_natCast] at this
    exact this.ne_zero
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    by_cases h : ringChar k = p
    · exact hpk (h ▸ h0)
    · have := (b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)).map β
      rw [map_natCast, h0] at this
      exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

theorem exists_kerUPart : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∀ (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → IsTj r w j o o' ψ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) ∧ IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ b N _ _ hm r w j c hw hu _ _ S _ s hp o o' ψ hψ hT
  obtain ⟨⟨E, rfl⟩, hψh, hlin, -, -, ψ', hψ'h, hψψ', -⟩ := hψ
  obtain ⟨J, hJ, hJp⟩ := exists_conj D r w hw.ne_top hu
  obtain ⟨α, hα1, hα2⟩ := exists_elt _ _ _ hJ hJp E
  have hc : IsUnit ((p ^ E : ℕ) : Γ(S, ⊤)) := by rw [Nat.cast_pow]; exact hp.pow E
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : ∀ a, IsMonHom (o'.act.act a) := o'.act.hom
  obtain ⟨K, G, i, hG, hi, hfin, het, hpts⟩ :=
    exists_subgroup o.ab o'.ab o.ab hc ψ (o.act.act (algebraMap (𝓞 D.F) D.O α))
  have hnat : ∀ k : ℕ, o.act.act (k : D.O) = 𝟙 o.A ^ k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]
  have hcomb : ∀ {T : Over S} (x : T ⟶ o.A) (a u v : 𝓞 D.F), x ^ (p ^ E) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1 →
      x ≫ o.act.act (algebraMap (𝓞 D.F) D.O (u * a + v * (p : 𝓞 D.F) ^ E)) = 1 := by
    intro T x a u v h1 h2
    rw [map_add (f := _), map_mul, map_mul, ← Nat.cast_pow, map_natCast, o.act.add, o.act.mul, o.act.mul, hnat,
      MonObj.comp_mul, ← Category.assoc, ← Category.assoc, h2, MonObj.comp_pow, Category.comp_id, h1,
      MonObj.one_comp, MonObj.one_comp, _root_.mul_one]
  have key : ∀ (T : Over S) (x : T ⟶ o.A),
      (x ≫ ψ = 1 ∧ ∃ e : ℕ, ES.KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
    intro T x
    rw [hpts]
    constructor
    · rintro ⟨h1, e, he⟩
      have h0 : x ^ (p ^ E) = 1 := by
        have : x ≫ ψ ≫ ψ' = 1 := by rw [← Category.assoc, h1, MonObj.one_comp]
        rwa [hψψ', MonObj.comp_pow, Category.comp_id] at this
      obtain ⟨a, ha, v, hv⟩ := hα2 e
      refine ⟨h0, h1, ?_⟩
      rw [hv, ← _root_.one_mul a]
      exact hcomb x a 1 v h0 (he a ha)
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h1, E, fun a ha => ?_⟩
      obtain ⟨u, v, rfl⟩ := hα1 a ha
      exact hcomb x α u v h0 h2
  refine ⟨K, G, i, hG, hi, hfin, het, fun a => ?_, ?_, key⟩
  · obtain ⟨h1, e, he⟩ := (key K i).2 ⟨𝟙 _, Category.id_comp _⟩
    refine (key K _).1 ⟨?_, e, fun z hz => ?_⟩
    · rw [Category.assoc, hlin, ← Category.assoc, h1, MonObj.one_comp]
    · rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, he z hz, MonObj.one_comp]
  · refine GlobalTheory.FinEtRank.isIsogDeg_of_card o.A K i hi hfin het _ ?_ fun k _ _ t => ?_
    · refine Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => ?_)
      have h := hu (p_mem_uIdeal D r)
      rw [Ideal.absNorm_eq_zero_iff.1 h0, Ideal.mem_bot] at h
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
    · haveI := charZero_of_isUnit b s hp k t
      obtain ⟨h1, h2⟩ := hT k t
      rw [hm, Nat.one_mul] at h2
      rw [← h2]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
      rw [← key]
      exact ⟨fun h => ⟨h.1, h1 g h.1 h.2⟩, fun h => ⟨h.1, 1, fun a ha => h.2 a (hu (by rwa [pow_one] at ha))⟩⟩

end GlobalTheory.UPel.HT.ES.KerUPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGrpLawAgreesWithAbelianSchemeLaw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartLaw

theorem awayMap_notMem {R : Type} [CommRing R] (g : R) (w : Sp (Localization.Away g)) : g ∉ (awayMap g w).asIdeal := by
  intro h
  have : algebraMap R (Localization.Away g) g ∈ w.asIdeal := h
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this (IsLocalization.Away.algebraMap_isUnit g))

theorem mul_left_comp {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {t : T ⟶ S} {t' : T' ⟶ S} (k : T' ⟶ T)
    (a b : Over.mk t ⟶ H) (a₁ b₁ : Over.mk t' ⟶ H) (ha : a₁.left = k ≫ a.left) (hb : b₁.left = k ≫ b.left) :
    (a₁ * b₁).left = k ≫ (a * b).left := by
  have ht : k ≫ t = t' := by
    have e1 : a.left ≫ H.hom = t := Over.w a
    have e2 : a₁.left ≫ H.hom = t' := Over.w a₁
    rw [← e1, ← e2, ha]; exact (Category.assoc _ _ _).symm
  let κ : Over.mk t' ⟶ Over.mk t := Over.homMk k ht
  have e1 : a₁ = κ ≫ a := Over.OverMorphism.ext ha
  have e2 : b₁ = κ ≫ b := Over.OverMorphism.ext hb
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem lift_open (σ : Setup) (x : Sp σ.R) {T : Scheme.{0}} (c : T ⟶ (σ.C x).G.left) (d : T ⟶ Sp (Localization.Away σ.f))
    (e : c ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) = d ≫ awayMap σ.f) : ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c := by
  refine ⟨IsOpenImmersion.lift (σ.V x).ι c ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (σ.hV x _).2 ?_
  have h1 := awayMap_notMem σ.f (d τ)
  rw [← Scheme.Hom.comp_apply, ← e] at h1
  exact h1

theorem chart_mul_generic (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (s : T ⟶ Sp (FractionRing (σ.C x).R))
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  obtain ⟨l, hl⟩ := lift_open σ x (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) (pullback.snd _ _ ≫ (σ.C x).y) (by
    rw [pullback.condition_assoc, Category.assoc, (σ.C x).hy, σ.hρ])
  have hα : (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
    have := σ.compat x _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rw [Category.id_comp] at this
    rw [this, Category.assoc, E.onV, ← Category.assoc, hl]
  let P : (Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) → (Over.mk s ⟶ (Over.pullback (jK (σ.C x).R)).obj (σ.C x).G) :=
    fun c => Over.homMk (pullback.lift c.left s (Over.w c)) (pullback.lift_snd _ _ _)
  have hP : ∀ c, c.left = (P c).left ≫ pullback.fst (σ.C x).G.hom (jK (σ.C x).R) := fun c => (pullback.lift_fst _ _ _).symm
  have hA : ∀ c (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA → c'.left = (P c).left ≫ (σ.C x).α := by
    intro c c' h
    rw [← cancel_mono E.ιA, ← h, hP c]
    exact (Category.assoc _ _ _).trans ((congrArg ((P c).left ≫ ·) hα.symm).trans (Category.assoc _ _ _).symm)
  have ht : t₂ = s ≫ (σ.C x).y := by
    have e1 : a'.left ≫ σ.A.hom = t₂ := Over.w a'
    have e2 : (P a).left ≫ ((Over.pullback (jK (σ.C x).R)).obj (σ.C x).G).hom = s := Over.w (P a)
    have e3 := (σ.C x).gen.1.w
    rw [← e1, hA a a' ha]
    exact (Category.assoc _ _ _).trans ((congrArg ((P a).left ≫ ·) e3).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (σ.C x).y) e2)))
  subst ht
  have m1 := (σ.C x).gen.2 (Over.mk s) (P a) (P b) a' b' (hA a a' ha) (hA b b' hb)
  have m2 := (isGrpPullback_pullback (σ.C x).G (jK (σ.C x).R)).2 (Over.mk s) (P a) (P b) a b (hP a) (hP b)
  exact (congrArg (· ≫ E.emb x) m2).trans ((Category.assoc _ _ _).trans ((congrArg ((P a * P b).left ≫ ·) hα.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ E.ιA) m1.symm))))

theorem chart_mul_flat (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (t₁ : T ⟶ Sp (σ.C x).R) [Flat t₁]
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk t₁ ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have := E.sep
  obtain ⟨w, -⟩ := E.openIn x
  have p1 : ∀ c : Over.mk t₁ ⟶ (σ.C x).G, (c.left ≫ E.emb x) ≫ E.p = t₁ ≫ spMap (σ.ρ x) := fun c => by
    have e : c.left ≫ (σ.C x).G.hom = t₁ := Over.w c
    rw [Category.assoc, w, ← Category.assoc, e]
  have p2 : ∀ c : Over.mk t₂ ⟶ σ.A, (c.left ≫ E.ιA) ≫ E.p = t₂ ≫ awayMap σ.f := fun c => by
    have e : c.left ≫ σ.A.hom = t₂ := Over.w c
    rw [Category.assoc, E.cartA.w, ← Category.assoc, e]
  have : IsSchemeTheoreticallyDominant (jK (σ.C x).R) :=
    schDom_spec_map _ (IsFractionRing.injective (σ.C x).R (FractionRing (σ.C x).R))
  have : IsSchemeTheoreticallyDominant (pullback.fst t₁ (jK (σ.C x).R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback t₁ (jK (σ.C x).R)).flip
  refine ext_of_schDom E.p (by rw [p1, p2, ← p1 a, ← p2 a', ha]) (pullback.fst t₁ (jK (σ.C x).R)) ?_
  let k := pullback.fst t₁ (jK (σ.C x).R)
  let Q : (Over.mk t₁ ⟶ (σ.C x).G) → (Over.mk (pullback.snd t₁ (jK (σ.C x).R) ≫ jK (σ.C x).R) ⟶ (σ.C x).G) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (Over.w c)).trans pullback.condition))
  let Q' : (Over.mk t₂ ⟶ σ.A) → (Over.mk (k ≫ t₂) ⟶ σ.A) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (Over.w c)))
  have h := chart_mul_generic σ E x _ _ (Q a) (Q b) (Q' a') (Q' b')
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) ha).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) hb).trans (Category.assoc _ _ _).symm))
  rw [mul_left_comp k a b (Q a) (Q b) rfl rfl, mul_left_comp k a' b' (Q' a') (Q' b') rfl rfl] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

theorem chart_mulAgree : ∀ (σ : Setup) (E : Emb σ) (x : Sp σ.R), MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  intro σ E x T t₁ t₂ a b a' b' ha hb
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  have := (σ.C x).semi.smooth
  obtain ⟨w, -⟩ := E.openIn x
  have hl : ∀ (c : Over.mk t₁ ⟶ (σ.C x).G) (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA →
      ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c.left ∧ l ≫ σ.φ x = c'.left := by
    intro c c' h
    obtain ⟨l, hl⟩ := lift_open σ x c.left (c'.left ≫ σ.A.hom) (by
      rw [← w, ← Category.assoc, h, Category.assoc, E.cartA.w, Category.assoc])
    refine ⟨l, hl, ?_⟩
    rw [← cancel_mono E.ιA, Category.assoc, E.onV, ← Category.assoc, hl]
    exact h
  obtain ⟨la, ha1, ha2⟩ := hl a a' ha
  obtain ⟨lb, hb1, hb2⟩ := hl b b' hb
  let q : (σ.V x).toScheme ⟶ Sp (σ.C x).R := (σ.V x).ι ≫ (σ.C x).G.hom
  have hq : la ≫ q = lb ≫ q := by
    have e1 : a.left ≫ (σ.C x).G.hom = t₁ := Over.w a
    have e2 : b.left ≫ (σ.C x).G.hom = t₁ := Over.w b
    simp only [q, ← Category.assoc, ha1, hb1]
    exact e1.trans e2.symm
  have hu : pullback.snd q q ≫ σ.φ x ≫ σ.A.hom = pullback.fst q q ≫ σ.φ x ≫ σ.A.hom := by
    rw [← cancel_mono (awayMap σ.f)]
    simp only [Category.assoc]
    rw [(σ.cart x).w]
    exact (pullback.condition_assoc (f := q) (g := q) _).symm
  let a₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.fst q q ≫ (σ.V x).ι) (Category.assoc _ _ _)
  let b₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.snd q q ≫ (σ.V x).ι)
    ((Category.assoc _ _ _).trans pullback.condition.symm)
  let a₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.fst q q ≫ σ.φ x) (Category.assoc _ _ _)
  let b₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.snd q q ≫ σ.φ x)
    ((Category.assoc _ _ _).trans hu)
  have h := chart_mul_flat σ E x (pullback.fst q q ≫ q) _ a₀ b₀ a₁ b₁
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (pullback.snd q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
  let k := pullback.lift la lb hq
  have k1 : k ≫ pullback.fst q q = la := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd q q = lb := pullback.lift_snd _ _ _
  rw [mul_left_comp k a₀ b₀ a b (ha1.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb1.symm.trans (by rw [← k2]; exact Category.assoc _ _ _)),
    mul_left_comp k a₁ b₁ a' b' (ha2.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb2.symm.trans (by rw [← k2]; exact Category.assoc _ _ _))]
  exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) h).trans (Category.assoc _ _ _).symm)

end GlobalTheory.Desc.ChartLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrimeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S, ∀ (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
        (∏ b, (g b).det) ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.DetInt.det_integral | exact GlobalTheory.DetInt.det_integral | (intros; apply GlobalTheory.DetInt.det_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommRingCatIsPullbackFlatBaseChangeSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commRingCat_isPullback_flat_baseChange_surjective : ∀ (P C₁ C₂ C₀ E E₁ E₂ E₀ : CommRingCat.{0}) (p₁ : P ⟶ C₁) (p₂ : P ⟶ C₂) (q₁ : C₁ ⟶ C₀) (q₂ : C₂ ⟶ C₀), IsPullback p₁ p₂ q₁ q₂ → Function.Surjective q₂.hom → ∀ (g : P ⟶ E) (g₁ : C₁ ⟶ E₁) (g₂ : C₂ ⟶ E₂) (g₀ : C₀ ⟶ E₀) (i₁ : E ⟶ E₁) (i₂ : E ⟶ E₂) (r₁ : E₁ ⟶ E₀) (r₂ : E₂ ⟶ E₀), g.hom.Flat → IsPushout g p₁ i₁ g₁ → IsPushout g p₂ i₂ g₂ → IsPushout g₂ q₂ r₂ g₀ → i₁ ≫ r₁ = i₂ ≫ r₂ → g₁ ≫ r₁ = q₁ ≫ g₀ → IsPullback i₁ i₂ r₁ r₂ := by
  first | exact @GlobalTheory.MilFlat.isPullback_of_flat | exact GlobalTheory.MilFlat.isPullback_of_flat | (intros; apply GlobalTheory.MilFlat.isPullback_of_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.Mean4O.CoverDom

theorem isNormalScheme_G {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) : GlobalTheory.IsNormalScheme V.G := by
  have : GlobalTheory.IsNormalScheme V.X := GlobalTheory.IsNormalScheme.of_pred V.normal
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : ∀ x, IsIso (V.j.stalkMap x) := fun x => isIso_stalkMap_of_flat_of_surjectiveOnStalks V.j x
  exact GlobalTheory.IsNormalScheme.of_isIso_stalkMap V.j

end GlobalTheory.Mean4O.CoverDom
end
end

