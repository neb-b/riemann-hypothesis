module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.AwayTriv
section
open NumberField IsDedekindDomain Neutral.B1

theorem UpperTheory.V.Af.Tw.awayTriv :
    UpperTheory.V.Af.Tw.AwayTriv := by
  intro F B _ _ _ _ _ _ N S hN hinf hS b hbS hbin
  classical
  have k1 : (b : AdeleRing (𝓞 F) F).1 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.mul_inv b)
  have k2 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 * (b : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.inv_mul b)
  have k3 : (b : AdeleRing (𝓞 F) F).2 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv b)
  have k4 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 * (b : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul b)
  let binf : Ideles F := ⟨((b : AdeleRing (𝓞 F) F).1, 1), (((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1, 1),
    Prod.ext k1 (mul_one 1), Prod.ext k2 (mul_one 1)⟩
  let bfin : Ideles F := ⟨(1, (b : AdeleRing (𝓞 F) F).2), (1, ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2),
    Prod.ext (mul_one 1) k3, Prod.ext (mul_one 1) k4⟩
  have hb : b = binf * bfin := by
    apply Units.ext
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  have hfin2 : (↑bfin : AdeleRing (𝓞 F) F).2 = (↑b : AdeleRing (𝓞 F) F).2 := rfl
  have h1 : N binf = 1 := hinf binf rfl
  have h2 : N bfin = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_local N hN bfin rfl ?_
    intro v
    by_cases hv : v ∈ S
    · have hone : Units.map (GlobalTheory.Mem.LocTriv.ev v) bfin = 1 := by
        apply Units.ext
        rw [Units.coe_map, Units.val_one]
        change (↑bfin : AdeleRing (𝓞 F) F).2 v = 1
        rw [hfin2]
        exact hbin v hv
      rw [hone, map_one, map_one]
    · apply hS v hv
      change Valued.v ((↑bfin : AdeleRing (𝓞 F) F).2 v) = 1
      rw [hfin2]
      exact hbS v hv
  rw [hb, map_mul, h1, h2, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ConjPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Af.Tw.conjPlace :
    UpperTheory.V.Af.Tw.ConjPlace := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h g hg w w' A hA hne hun
  haveI : Algebra.IsQuadraticExtension F L := ⟨h⟩
  have hc : Nat.card (L ≃ₐ[F] L) = 2 := (IsGalois.card_aut_eq_finrank F L).trans h
  obtain ⟨t, -, hu⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hc
  have h1 : g.restrictNormal L = t := by
    refine hu _ fun h1 => hg ?_
    refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun y => ?_, AlgEquiv.ext fun _ => rfl⟩
    have := AlgEquiv.restrictNormal_commutes g L y
    rw [h1] at this
    exact this.symm
  have hlift : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (t x) := fun x => by
    rw [← h1]
    exact (AlgEquiv.restrictNormal_commutes g L x).symm
  haveI := w.isPrime
  haveI := w'.isPrime
  haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hun.symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w.asIdeal w'.asIdeal
    (L ≃ₐ[F] L)
  obtain rfl : σ = t := hu σ fun h0 => hne (HeightOneSpectrum.ext (by rw [← hσ, h0, one_smul]))
  have hA' : ∀ x, g.toRingEquiv x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨g • A, fun x => ?_, fun s s' hs => ?_⟩
  · obtain ⟨y, rfl⟩ := MulAction.surjective σ x
    rw [← hσ, Ideal.smul_mem_pointwise_smul_iff, ← hA y, ← val_lt_one hA']
    have h2 : g.toRingEquiv (algebraMap L Ω (y : L)) = algebraMap L Ω ((σ • y : 𝓞 L) : L) := hlift y
    rw [h2]
  · have hss : ∀ x, s' (g x) = g (s x) := fun x => by
      refine (DFunLike.congr_fun hs (g x)).trans ?_
      show g (s (g.symm (g x))) = _
      rw [AlgEquiv.symm_apply_apply]
    have hD : s ∈ Dec (F := L) A → s' ∈ Dec (F := L) (g • A) := fun hs0 => by
      refine mem_Dec.2 ?_
      show resG F L Ω s' • g • A = g • A
      have h3 : resG F L Ω s • A = A := mem_Dec.1 hs0
      rw [hs, ← mul_smul, inv_mul_cancel_right, mul_smul, h3]
    have hle : ∀ y, (g • A).valuation (g y) ≤ 1 → A.valuation y ≤ 1 := fun y hy =>
      (A.valuation_le_one_iff _).2 ((hA' y).1 (((g • A).valuation_le_one_iff _).1 hy))
    refine ⟨fun hI => ⟨hD hI.1, fun x hx => ?_⟩, fun q hF => ⟨hD hF.1, fun x hx => ?_⟩⟩
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_sub]
      exact (val_lt_one hA' _).2 (hI.2 y (hle y hx))
    · obtain ⟨y, rfl⟩ := g.surjective x
      rw [hss, ← map_pow, ← map_sub]
      exact (val_lt_one hA' _).2 (hF.2 y (hle y hx))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.Descend
section
open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

theorem UpperTheory.V.Af.Tw.descend :
    UpperTheory.V.Af.Tw.Descend := by
  unfold UpperTheory.V.Af.Tw.Descend
  intro F Ω B _ _ _ _ _ _ _ _ art hart ψ hψc hdiag hfin
  have hq := hart.quot
  have hker : art.ker ≤ ψ.ker := by
    rw [hart.ker]
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · refine sup_le ?_ ?_
      · rintro _ ⟨k, rfl⟩
        exact hdiag k
      · intro z hz
        unfold infConn at hz
        obtain ⟨w, _, rfl⟩ := hz
        exact hfin _ rfl
    · exact isClosed_singleton.preimage hψc
  let fC : C(Ideles F, Gab F Ω) := ⟨art, hq.continuous⟩
  let gC : C(Ideles F, B) := ⟨ψ, hψc⟩
  have hfact : Function.FactorsThrough gC fC := by
    intro a b hab
    have hab' : a / b ∈ art.ker := by
      rw [MonoidHom.mem_ker, map_div]
      exact div_eq_one.2 hab
    have := hker hab'
    rw [MonoidHom.mem_ker, map_div] at this
    exact div_eq_one.1 this
  have hQ : Topology.IsQuotientMap fC := hq.isQuotientMap
  let κC := hQ.lift gC hfact
  have hκ : ∀ x, κC (art x) = ψ x := fun x => DFunLike.congr_fun (hQ.lift_comp gC hfact) x
  let κ₀ : Gab F Ω →* B := MonoidHom.mk' κC (by
    intro a b
    obtain ⟨x, rfl⟩ := hq.surjective a
    obtain ⟨y, rfl⟩ := hq.surjective b
    rw [← map_mul, hκ, hκ, hκ, map_mul])
  refine ⟨κ₀.comp (GlobalTheory.HeckeGal.toAb F Ω), ?_, ?_⟩
  · exact κC.continuous.comp (by
      first
        | exact QuotientGroup.continuous_mk
        | exact continuous_quot_mk)
  · intro x σ h
    show κC (GlobalTheory.HeckeGal.toAb F Ω σ) = ψ x
    rw [← h, hκ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.FrobInert
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Tw
open scoped Pointwise

section SlopeTestRemainingChoices

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω]

omit [NumberField L] in
private theorem int_mem (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  have hb : IsIntegral ℤ (algebraMap L Ω (x : L)) := x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom
  have h : IsIntegral A (algebraMap L Ω (x : L)) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (int_mem A)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, ⟨hu⟩⟩

private theorem normV_under (w : HeightOneSpectrum (𝓞 L)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

omit [NumberField K] in
private theorem frob_val {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 ∧ (A.valuation x < 1 → A.valuation (σ x) < 1) := by
  have e : σ x = (σ x - x ^ q) + x ^ q := by ring
  have h1 := hσ.2 x hx
  constructor
  · rw [e]
    exact Valuation.map_add_le _ h1.le (by rw [map_pow]; exact pow_le_one₀ zero_le hx)
  · intro h
    rw [e]
    exact Valuation.map_add_lt _ h1 (by rw [map_pow]; exact pow_lt_one₀ zero_le h hq)

omit [NumberField K] in
private theorem frob_sq {A : ValuationSubring Ω} {q : ℕ} (hq : q ≠ 0) {σ : G K Ω} (hσ : IsFrob A q σ) :
    IsFrob A (q ^ 2) (σ * σ) := by
  refine ⟨mul_mem hσ.1 hσ.1, fun x hx => ?_⟩
  have h1 := hσ.2 x hx
  have h2 := (frob_val hq hσ h1.le).2 h1
  have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
  have h3 := hσ.2 (x ^ q) hxq
  have e : (σ * σ) x - x ^ q ^ 2 = σ (σ x - x ^ q) + (σ (x ^ q) - (x ^ q) ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub, sq, pow_mul]; ring
  rw [e]
  exact Valuation.map_add_lt _ h2 h3

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Tw.frobInert :
    UpperTheory.V.Af.Tw.FrobInert := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hU hA σ hσ hn
  obtain ⟨w, hw, hwv⟩ := place_between (L := L) hA
  have : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  have : IsGalois F L := inferInstance
  have hq : normV v ≠ 0 := by
    rw [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hu : w.under (𝓞 F) = v := HeightOneSpectrum.ext hwv.over.symm
  set c : L ≃ₐ[F] L := AlgEquiv.restrictNormalHom L σ with hc
  have hcx : ∀ x : L, algebraMap L Ω (c x) = σ (algebraMap L Ω x) := fun x =>
    AlgEquiv.restrictNormal_commutes σ L x
  have hc1 : c ≠ 1 := fun h => hn ⟨{ σ with
    commutes' := fun x => by
      have := hcx x
      rw [h] at this
      exact this.symm }, rfl⟩
  have := w.isMaximal
  have hcw : c • w.asIdeal = w.asIdeal := by
    have hmax : (c • w.asIdeal).IsMaximal := by
      exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ c)
    refine hmax.eq_of_le w.isPrime.ne_top ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hy |> fun h => (⟨c⁻¹ • y, h, smul_inv_smul c y⟩ : ∃ x ∈ w.asIdeal, c • x = y)
    rw [← hw] at hx ⊢
    have e : algebraMap L Ω ((c • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) := hcx x
    rw [e]
    exact (frob_val hq hσ hx.le).2 hx
  have huniq : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver v.asIdeal → P = w.asIdeal := by
    intro P _ _
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal P (L ≃ₐ[F] L)
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
    by_cases hg1 : g = 1
    · rw [← hg, hg1, one_smul]
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
      rw [← hg, hy g hg1, ← hy c hc1, hcw]
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 2 := by
    have := v.isPrime
    letI : Unique (v.asIdeal.primesOver (𝓞 L)) :=
      ⟨⟨⟨w.asIdeal, w.isPrime, hwv⟩⟩, fun P => Subtype.ext (huniq P.1 P.2.1 P.2.2)⟩
    have hs := Ideal.sum_ramification_inertia_eq_card (p := v.asIdeal) (S := 𝓞 L) (G := L ≃ₐ[F] L)
    rw [Fintype.sum_unique, IsGalois.card_aut_eq_finrank, h2] at hs
    have he := hU w hu
    rw [hu, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2 at hs
    rwa [he, one_mul] at hs
  refine ⟨w, fun u => ⟨fun h => HeightOneSpectrum.ext (huniq _ u.isPrime ⟨by rw [← h]; rfl⟩), fun h => h ▸ hu⟩,
    hw, fun t ht => ?_⟩
  have h3 := frob_sq hq hσ
  rw [← ht] at h3
  rw [normV_under (K := F), hu, hf]
  exact ⟨h3.1, h3.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.GlueExt
section
namespace UpperTheory.V.Af.Tw

private theorem glue_ext {G H B : Type*} [CommGroup G] [CommGroup H] [CommGroup B] (hB : KStar.Choice.IsDiv B)
    (p : G →* H) (f : G →* B) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* B, ∀ x, F (p x) = f x := by
  classical
  obtain ⟨F, hF⟩ := hB.exists_extension p.range
    ((QuotientGroup.lift p.ker f (fun x hx => (MonoidHom.mem_ker).2 (h x ((MonoidHom.mem_ker).1 hx)))).comp
      (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom)
  refine ⟨F, fun x => (hF ⟨p x, x, rfl⟩).trans ?_⟩
  have hx : (QuotientGroup.quotientKerEquivRange p).symm ⟨p x, x, rfl⟩ = (x : G ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
  rfl

private theorem glue_exp (n M l : ℕ) (hM : 0 < M) (hl : l.Prime) :
    ∃ e k : ℕ, e ≡ 1 [MOD n] ∧ 0 < k ∧ (n.Coprime l → k.Coprime l) ∧ M ∣ e * k := by
  by_cases hc : n.Coprime l
  · have hM0 : M ≠ 0 := hM.ne'
    have hco : n.Coprime (l ^ M.factorization l) := Nat.Coprime.pow_right _ hc
    obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hco 1 0
    refine ⟨e, M / l ^ M.factorization l, he1, Nat.ordCompl_pos l hM0,
      fun _ => (Nat.coprime_ordCompl hl hM0).symm, ?_⟩
    have hd : l ^ M.factorization l ∣ e := (Nat.modEq_zero_iff_dvd).1 he0
    calc M = l ^ M.factorization l * (M / l ^ M.factorization l) :=
          (Nat.ordProj_mul_ordCompl_eq_self M l).symm
      _ ∣ e * (M / l ^ M.factorization l) := mul_dvd_mul_right hd _
  · exact ⟨1, M, Nat.ModEq.refl 1, hM, fun h' => absurd h' hc, by simp⟩

theorem glue : Glue := by
  unfold Glue
  intro I J K B _ _ _ _ hB i d c σ U V N g n M l hM hl h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨e, k, he, hk0, hkc, hMk⟩ := glue_exp n M l hM hl
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : J × K × U →* I, ∀ z, p₀ z = i z.1 * d z.2.1 * (z.2.2 : I) :=
    ⟨i.comp (MonoidHom.fst _ _) * d.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
      U.subtype.comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)), fun z => rfl⟩
  have hq : ∀ z, p₀ z = 1 → (z.2.2 : I) / c z.2.2 = d (σ z.2.1 / z.2.1) := by
    intro z hz
    rw [hp₀] at hz
    have hu : (z.2.2 : I) = (i z.1 * d z.2.1)⁻¹ := eq_inv_of_mul_eq_one_right hz
    rw [hu, map_inv, map_mul, h1, h2, map_div]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  obtain ⟨pθ, hpθ⟩ : ∃ pθ : p₀.ker × V →* I,
      ∀ w, pθ w = d (σ (w.1 : J × K × U).2.1 / (w.1 : J × K × U).2.1) * (w.2 : I) :=
    ⟨d.comp ((σ / MonoidHom.id K).comp ((MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp
      (p₀.ker.subtype.comp (MonoidHom.fst _ _))))) * V.subtype.comp (MonoidHom.snd _ _), fun w => rfl⟩
  obtain ⟨fθ, hfθ⟩ : ∃ fθ : p₀.ker × V →* B,
      ∀ w, fθ w = (N (w.1 : J × K × U).1 * g ((w.1 : J × K × U).2.2 : I))⁻¹ :=
    ⟨((N.comp (MonoidHom.fst _ _) * g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _)))).comp (p₀.ker.subtype.comp (MonoidHom.fst _ _)))⁻¹, fun w => rfl⟩
  obtain ⟨θ₁, hθ₁⟩ := glue_ext hB pθ fθ (by
    rintro ⟨⟨⟨a, x, u⟩, hz⟩, v⟩ hw
    rw [hpθ] at hw
    rw [hfθ]
    dsimp only at hw ⊢
    have hz' : p₀ (a, x, u) = 1 := MonoidHom.mem_ker.1 hz
    rw [hp₀] at hz'
    dsimp only at hz'
    have hv : d (σ x / x) = (v : I)⁻¹ := eq_inv_of_mul_eq_one_left hw
    have hσ : σ x = x := h7 x (by rw [hv]; exact inv_mem v.2)
    obtain ⟨a', ha', hN⟩ := h5 x hσ
    have hiu : i (a * a') = (u : I)⁻¹ := by
      rw [map_mul, ha']
      exact eq_inv_of_mul_eq_one_left hz'
    have h4' := h4 (a * a') (by rw [hiu]; exact inv_mem u.2)
    rw [hiu, map_inv, map_mul, hN, mul_one] at h4'
    rw [← h4', inv_mul_cancel, inv_one])
  obtain ⟨θ, hθ⟩ : ∃ θ : I →* B, ∀ y, θ y = θ₁ y ^ e := ⟨(powMonoidHom e).comp θ₁, fun y => rfl⟩
  have hV : ∀ v ∈ V, θ₁ v = 1 := by
    intro v hv
    have h := hθ₁ (1, ⟨v, hv⟩)
    rw [hpθ, hfθ] at h
    simpa using h
  have hZ : ∀ z, p₀ z = 1 → θ (z.2.2 / c z.2.2) = (N z.1 * g z.2.2)⁻¹ := by
    intro z hz
    have h := hθ₁ (⟨z, MonoidHom.mem_ker.2 hz⟩, 1)
    rw [hpθ, hfθ] at h
    dsimp only at h
    simp only [OneMemClass.coe_one, mul_one] at h
    rw [hθ, hq z hz, h]
    have hw : ((N z.1 * g z.2.2)⁻¹) ^ n = 1 := by
      have hmem : d (σ z.2.1 / z.2.1) ∈ U := by
        rw [← hq z hz]
        exact div_mem z.2.2.2 (h3 _ z.2.2.2)
      rw [← h, ← map_pow, ← map_pow, h6 _ hmem, map_one, map_one]
    rw [pow_eq_pow_mod e hw, show e % n = 1 % n from he, ← pow_eq_pow_mod 1 hw, pow_one]
  obtain ⟨f, hf⟩ : ∃ f : J × K × U →* B, ∀ z, f z = N z.1 * (g z.2.2 * θ (z.2.2 / c z.2.2)) :=
    ⟨N.comp (MonoidHom.fst _ _) * (g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _))) * θ.comp ((U.subtype / c.comp U.subtype).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))), fun z => rfl⟩
  obtain ⟨ψ, hψ⟩ := glue_ext hB p₀ f (by
    intro z hz
    rw [hf, hZ z hz, ← mul_assoc, mul_inv_cancel])
  refine ⟨ψ, θ, fun a => ?_, fun x => ?_, fun u hu => ?_, fun v hv => ?_, k, hk0, hkc, fun u hu => ?_⟩
  · have h := hψ (a, 1, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, x, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, 1, ⟨u, hu⟩)
    rw [hp₀, hf] at h
    simpa using h
  · rw [hθ, hV v hv, one_pow]
  · obtain ⟨j, hj⟩ := hMk
    rw [hθ, ← pow_mul, ← map_pow, hj, pow_mul]
    exact hV _ (pow_mem (h8 u hu) j)

end UpperTheory.V.Af.Tw
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.Kron
section
open NumberField IsDedekindDomain in
theorem UpperTheory.V.Af.Tw.kron :
    UpperTheory.V.Af.Tw.Kron := by
  intro K _ _
  refine ⟨NumberField.Units.torsionOrder K, ?_, ?_⟩
  · intro l hl hno
    haveI : Fact (Nat.Prime l) := ⟨hl⟩
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := NumberField.Units.torsion K) l hdvd
    have h1 : IsPrimitiveRoot (g : (𝓞 K)ˣ) l := by
      rw [← hg, ← Subgroup.orderOf_coe]
      exact IsPrimitiveRoot.orderOf _
    have h2 : IsPrimitiveRoot (((g : (𝓞 K)ˣ) : 𝓞 K)) l := IsPrimitiveRoot.coe_units_iff.mpr h1
    have h3 := h2.map_of_injective (f := algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)
    exact hno ⟨_, h3⟩
  · intro y hy hnorm
    have hy' : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((Neutral.B1.diagUnits K y : Neutral.B1.Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1 := hy
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (y : K) (fun v => by
      rw [← GlobalTheory.UpIdeleMod.valued_algebraMap (R := 𝓞 K) v]
      exact le_of_eq (hy' v))
    have hI : IsIntegral ℤ (y : K) := by
      have := NumberField.RingOfIntegers.isIntegral_coe r
      rwa [hr] at this
    obtain ⟨m, hm, hym⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hI hnorm
    have hrm : r ^ m = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_pow, hr, hym, map_one]
    let u : (𝓞 K)ˣ := Units.ofPowEqOne r m hrm hm.ne'
    have hu : u ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨m, hm, Units.ext (by simp [u, hrm])⟩
    rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hu
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hr, ← map_pow]
    have hu' := congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K))) hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hu'
    change (u : 𝓞 K) ^ NumberField.Units.torsionOrder K = 1 at hu'
    have hur : (u : 𝓞 K) = r := Units.val_ofPowEqOne r m hrm hm.ne'
    rw [hur] at hu'
    rw [hu', map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ResOpen
section
open ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af Formalism.ConjugateSelfDual UpperTheory.V.Base

theorem UpperTheory.V.Af.Tw.resOpen :
    UpperTheory.V.Af.Tw.ResOpen := by
  unfold UpperTheory.V.Af.Tw.ResOpen
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _
  have hre : resG F L Ω = UpperTheory.V.Base.galEmb F L Ω := rfl
  obtain ⟨hemb, hop, hidx⟩ := UpperTheory.V.Base.galEmbTop F L Ω
  rw [hre]
  refine ⟨⟨hemb, ?_⟩, ?_⟩
  · rw [← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]
    exact hop
  · rw [UpperTheory.V.Base.range_galEmb]
    exact hidx
end

