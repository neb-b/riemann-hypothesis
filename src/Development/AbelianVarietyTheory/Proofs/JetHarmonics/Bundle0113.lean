module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.DualLattices.UpBrChar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffMoreColumns
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FormTies
open scoped Classical

namespace GlobalTheory.MoreColumns

open GlobalTheory.DatumInverseCharacter

theorem sum_append {A F : Type} [Fintype A] [CommRing F] {n m : ℕ} (f : (Fin n → A) → F) (χ : Fin (n + m) → A → F) :
    ∑ x : Fin (n + m) → A, f (fun b => x (Fin.castAdd m b)) * ∏ b, χ b (x b) =
      (∑ y : Fin n → A, f y * ∏ b, χ (Fin.castAdd m b) (y b)) * ∏ b : Fin m, ∑ a, χ (Fin.natAdd n b) a := by
  rw [← (Fin.appendEquiv n m).sum_comp, Fintype.sum_prod_type, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.prod_univ_add]
  simp [mul_assoc]

theorem zpow_sum {F ι : Type} [Field F] {z : F} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ (∑ i ∈ s, a i) = ∏ i ∈ s, z ^ a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hz, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem char_sum (D : Datum H) {N : ℕ} (hN : 0 < N) {I : Ideal (𝓞 E)}
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {F : Type} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
    [Fintype (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))] (v : D.La) :
    ∑ x : D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La), z ^ D.EF (qRep x) (cHalf H I • v) =
      if v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) then
        (Nat.card (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) : F) else 0 := by
  obtain ⟨hc, hc1⟩ := HalfPairing.cHalf_spec I hI
  have hz0 : z ≠ 0 := hz.ne_zero hN.ne'
  have hmk : ∀ u : D.La, z ^ D.EF (qRep (Submodule.Quotient.mk u :
      D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))) (cHalf H I • v) =
      z ^ D.EF u (cHalf H I • v) := by
    intro u
    refine zpow_congr hN hz.pow_eq_one ?_
    rw [← LinearMap.sub_apply, ← map_sub]
    exact dvd_left D hp hc v ((Submodule.Quotient.eq _).1 (qRep_spec _))
  let χ : AddChar (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) F :=
    { toFun := fun x => z ^ D.EF (qRep x) (cHalf H I • v)
      map_zero_eq_one' := by
        have := hmk 0
        rw [map_zero, LinearMap.zero_apply, zpow_zero] at this
        exact this
      map_add_eq_mul' := fun x y => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [← Submodule.Quotient.mk_add, hmk, hmk, hmk, map_add (f := _), LinearMap.add_apply, zpow_add₀ hz0] }
  have hiff : χ = 0 ↔ v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := by
    constructor
    · intro h
      have h1 : ∀ y, (N : ℤ) ∣ D.EF (cHalf H I • v) y := fun y => by
        have h2 : χ (Submodule.Quotient.mk y) = 1 := by rw [h]; rfl
        have h3 : z ^ D.EF y (cHalf H I • v) = 1 := (hmk y).symm.trans h2
        rw [HalfPairing.ef_swap, dvd_neg]
        exact (hz.zpow_eq_one_iff_dvd _).1 h3
      have hNI : (N : 𝓞 E) ∈ I := by
        have : Ideal.span {(N : 𝓞 E)} ≤ I := hp ▸ (Ideal.mul_le_inf.trans inf_le_left)
        exact this (Ideal.subset_span rfl)
      have h4 := mem_of_modN D hNI (modN_of_dvd D hN h1)
      have : v = cHalf H I • v - (cHalf H I - 1) • v := by rw [sub_smul, one_smul, sub_sub_cancel]
      rw [this]
      exact sub_mem h4 (Submodule.smul_mem_smul hc1 trivial)
    · intro h
      ext x
      exact (hz.zpow_eq_one_iff_dvd _).2 (dvd_right D hp hc _ h)
  have := AddChar.sum_eq_ite χ
  rw [Nat.card_eq_fintype_card]
  simp only [← hiff]
  convert this using 2

theorem coeff_more_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n m : ℕ) (d : DeltaDat Xo c n) (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F), d.IsLev → Dw.p + Dw.q ≤ n → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d) (ph' : (Fin (n + m) → LaJ Xo c d) → c.F) (x₀' : Fin (n + m) → LaJ Xo c d), d.PhiPin ph ψ x₀ → (withCoeff d φ').PhiPin ph' ψ x₀' → ∃ ζ : c.F, IsOfFinOrder ζ ∧ ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) * (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (LaI Xo c d) : c.F) ^ m else 0) := by
  intro E _ _ _ H Dw l Xo c n m d φ' hd hn ψ ph x₀ ph' x₀' hpin hpin'
  obtain ⟨-, huniq, adj, -, hadj⟩ := HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  obtain ⟨ha, hb, hc, hone, hspan, hφ⟩ := hpin
  obtain ⟨ha', hb', hc', hone', hspan', hφ'⟩ := hpin'
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hMb
  have hI0 : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  have hJ0 : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  haveI : Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hJ0
  haveI : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) _ Dw.rank
  obtain ⟨e'⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I _ Dw.rank
  haveI : Finite (LaJ Xo c d) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (LaI Xo c d) := Finite.of_equiv _ e'.toEquiv.symm
  haveI : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (k : LaI Xo c d → LaI Xo c d))
      DFunLike.coe_injective
  have hcard : Nat.card (LaJ Xo c d) = Nat.card (LaI Xo c d) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv, Nat.card_fun, Nat.card_fun,
      Nat.card_congr (Ideal.quotientEquiv d.I _ (H.bar : 𝓞 E ≃+* 𝓞 E) rfl).toEquiv]
  have himg : ∀ {k : ℕ} (hk : Dw.p + Dw.q ≤ k) (x : Fin k → LaJ Xo c d),
      x '' {b | b.val < Dw.p + Dw.q} = Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hk b)) := by
    intro k hk x
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hk b, b.2, rfl⟩
  have hn' : Dw.p + Dw.q ≤ n + m := hn.trans (Nat.le_add_right _ _)
  have hs₀ := (congrArg (Submodule.span (𝓞 E)) (himg hn x₀)).symm.trans hspan
  have hspan₁ : Submodule.span (𝓞 E) (x₀' '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hspan'
  have hb₁ : ∀ x, ph' x ≠ 0 → Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hb'
  have hs₀' := (congrArg (Submodule.span (𝓞 E)) (himg hn' x₀')).symm.trans hspan₁
  obtain ⟨g, hg, -⟩ := huniq _ _ hs₀ hs₀'
  have hy₀ : ph (fun b => x₀' (Fin.castAdd m b)) = (((ψ (adj g))⁻¹ : c.Fˣ) : c.F) := by
    have h1 := hc (adj g) g ((hadj _ _).2 rfl) x₀
    rw [hone, mul_one] at h1
    rw [← h1]
    exact ha _ _ fun b hb => (hg ⟨b.1, hb⟩).symm
  have hph : ∀ x : Fin (n + m) → LaJ Xo c d,
      ph' x = ((ψ (adj g) : c.Fˣ) : c.F) * ph (fun b => x (Fin.castAdd m b)) := by
    intro x
    by_cases hx : Submodule.span (𝓞 E) (Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hn' b))) = ⊤
    · obtain ⟨g', hg', -⟩ := huniq _ _ hs₀' hx
      have h1 : ph' (fun b => g' (x₀' b)) = (((ψ (adj g'))⁻¹ : c.Fˣ) : c.F) * ph' x₀' :=
        hc' (adj g') g' ((hadj _ _).2 rfl) x₀'
      have h2 := hc (adj g') g' ((hadj _ _).2 rfl) (fun b => x₀' (Fin.castAdd m b))
      have h3 : ph' x = ph' (fun b => g' (x₀' b)) := ha' _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      have h4 : ph (fun b => x (Fin.castAdd m b)) = ph (fun b => g' (x₀' (Fin.castAdd m b))) :=
        ha _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      rw [h3, h4, h1, h2, hy₀, hone', mul_one, mul_left_comm, Units.mul_inv, mul_one]
    · have h1 : ph' x = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn' x)).symm.trans (hb₁ x h))
      have h2 : ph (fun b => x (Fin.castAdd m b)) = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn _)).symm.trans (hb _ h))
      rw [h1, h2, mul_zero]
  refine ⟨((ψ (adj g) : c.Fˣ) : c.F),
    (Units.coeHom c.F).isOfFinOrder (ψ.isOfFinOrder (isOfFinOrder_of_finite _)), fun q => ?_⟩
  set z : d.c₂.F := (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd) with hzdef
  have hz : IsPrimitiveRoot z d.pd := by
    have h1 : d.pd ∣ d.l₂.M' := (hM ▸ Dvd.intro_left _ rfl : d.pd ∣ d.l₂.M).trans (Nat.dvd_lcm_left _ _)
    have h2 : 0 < d.l₂.M' := Nat.lcm_pos hM₂ d.l₂.A_pos
    have h0 : IsPrimitiveRoot (zeta d.l₂.M') d.l₂.M' := Complex.isPrimitiveRoot_exp _ h2.ne'
    have h3 : IsPrimitiveRoot (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) d.l₂.M' :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap d.c₂.F ℂ) h0 (algebraMap d.c₂.F ℂ).injective
    exact h3.pow h2 (Nat.div_mul_cancel h1).symm
  have hz0 : z ≠ 0 := hz.ne_zero hpd.ne'
  haveI := Fintype.ofFinite (LaJ Xo c d)
  have h1 : d.eF (φ' q) = ∑ᶠ x : Fin (n + m) → LaJ Xo c d, d.eF (ph' x) *
      z ^ (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b))) := hφ' q
  apply d.eF.injective
  rw [h1, map_mul, map_mul, hφ, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [zpow_sum hz0, hph, map_mul, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_append (fun y => d.eF (ph y)) (fun b a => z ^ Dw.EF (qRep a) (cHalf H d.I • levRep (q b)))]
  congr 1
  simp only [char_sum Dw hpd hIJ hI hz]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_true_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  split_ifs
  · rw [map_pow, map_natCast, ← hcard]
  · rw [map_zero]

end GlobalTheory.MoreColumns
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersLeadingMinorsGeHodgeTate
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_chars_leading_minors_ge :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d s N : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O), Function.Surjective (res w) → ∀ (u : Fin N → PS O 1 d), (∀ k, IsCh F (u k)) → ∀ c : O, c ≠ 0 → (∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range fun k => dl (u k))) → ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, v (algebraMap O C c) ^ s ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  intro C _ v O _ _ hv d s N F w hw u hu c hc hspan
  have hA : ∀ y : Fin s → O,
      c • y ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
    intro y
    obtain ⟨f, rfl⟩ := hw y
    have h1 : (Set.range fun k => res w (dl (u k))) = res w '' (Set.range fun k => dl (u k)) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, ← Submodule.map_span, ← map_smul]
    exact Submodule.mem_map_of_mem (hspan f)
  obtain ⟨t, ht, hmin⟩ := GlobalTheory.exists_leading_minors_ge C v O hv s _ c hc hA
  choose k hk using ht
  refine ⟨fun b => u (k b), fun b => hu _, fun i => ?_⟩
  have hm : (Matrix.of fun a b : Fin (i.val + 1) =>
      ∑ j, w (Fin.castLE i.isLt a) j * dl (u (k (Fin.castLE i.isLt b))) j) =
      Matrix.of fun a b : Fin (i.val + 1) => t (Fin.castLE i.isLt b) (Fin.castLE i.isLt a) := by
    ext a b
    rw [Matrix.of_apply, Matrix.of_apply, ← hk]
    simp [res, Matrix.mulVec, dotProduct]
  rw [hm]
  exact (pow_le_pow_right_of_le_one' (hv.map_le_one c) i.isLt).trans (hmin i)

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_ringHom_ringOfIntegers_lift {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, hf⟩

theorem exists_types_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ (τT : (E →+* ℂ) → (𝓞 E →+* T.V)), (∀ τ a, algebraMap T.V T.Fr (τT τ a) = io (embK c τ a)) ∧ IsTypes X io (fun τ => X.ι.comp (τT τ)) ∧ Function.Injective (fun τ => X.ι.comp (τT τ)) ∧ (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ X.ι (τT τ H.rt) = X.ι (τT τ' H.rt)) ∧ ∀ τ a, τT (ComplexEmbedding.conjugate τ) a = τT τ (H.bar a) := by
  intro E _ _ _ H l c T io p _ X
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ =>
    exists_ringHom_ringOfIntegers_lift (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hT : ∀ τ a, algebraMap X.O X.C (X.ι (σV τ a)) = X.ιF (io (embK c τ a)) := by
    intro τ a
    rw [← X.comp, hσV']
  have key : ∀ τ τ' (a : 𝓞 E), τ (a : E) = τ' (a : E) ↔ X.ι (σV τ a) = X.ι (σV τ' a) := by
    intro τ τ' a
    constructor
    · intro h
      have h1 : embK c τ a = embK c τ' a := by
        apply Subtype.ext
        rw [embK_coe, embK_coe]
        exact h
      have h2 : σV τ a = σV τ' a := hinj (by rw [hσV', hσV', h1])
      rw [h2]
    · intro h
      have h1 : embK c τ a = embK c τ' a :=
        io.injective (X.ιF.injective (by rw [← hT, ← hT, h]))
      exact congrArg (fun z : c.F => (z : ℂ)) h1
  refine ⟨σV, hσV', hT, ?_, fun τ τ' => key τ τ' H.rt, fun τ a => ?_⟩
  · intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    exact (key τ τ' a).2 (RingHom.congr_fun h a)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    exact hinj (by rw [hσV', hσV', h])

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColength
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
open ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CharDepth

theorem det_dvd_det_of_trunc_mem_span {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R)
    (h : ∀ j, (fun a : Fin n => A a.castSucc j) ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    B.det ∣ A.det := by
  choose X hX using fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (h j)
  rw [Matrix.det_succ_row A (Fin.last n)]
  refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
  have e : A.submatrix (Fin.last n).succAbove j.succAbove = B * Matrix.of (fun i k => X (j.succAbove k) i) := by
    ext a k
    have := congrFun (hX (j.succAbove k)) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.submatrix_apply, Fin.succAbove_last, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, Matrix.det_mul]
  exact Dvd.intro _ rfl

theorem minor_dvd_minor {R : Type} [CommRing R] {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (hι : ∀ s (hs : s ≤ g), Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs)
    (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ g) :
    (Matrix.of fun a b : Fin n => M (Fin.castLE (hnm.trans hm) a) (ι (Fin.castLE (hnm.trans hm) b))).det ∣
      (Matrix.of fun a b : Fin m => M (Fin.castLE hm a) (ι (Fin.castLE hm b))).det := by
  induction m, hnm using Nat.le_induction with
  | base => exact dvd_rfl
  | succ m hnm ih =>
    refine (ih (Nat.le_of_succ_le hm)).trans (det_dvd_det_of_trunc_mem_span _ _ fun j => ?_)
    have h := hι m (Nat.le_of_succ_le hm)
    have h2 : (fun a : Fin m => M (Fin.castLE (Nat.le_of_succ_le hm) a) (ι (Fin.castLE hm j))) ∈
        omTr M m (Nat.le_of_succ_le hm) := Submodule.subset_span ⟨_, rfl⟩
    rw [← h] at h2
    exact h2

theorem exists_smul_eq_zero_of_hasLen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) (hx : x ≠ 0) : x ≤ 1 ∧ ∃ c : R, c ≠ 0 ∧ ∀ m : M, c • m = 0 := by
  obtain ⟨m, c, ⟨e⟩, hc⟩ := h
  have hc' : v (algebraMap R C (∏ i, c i)) = x := by rw [map_prod, map_prod, hc]
  refine ⟨hc' ▸ hv.map_le_one _, ∏ i, c i, ?_, fun z => ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hc'
    exact hx hc'.symm
  · apply e.injective
    rw [map_smul, map_zero]
    funext i
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e z i)
    rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right y)

theorem exists_flag_characters (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (d s : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O) (x : NNReal)
    (h : HasAF v F w x) (hx : x ≠ 0) :
    x ≤ 1 ∧ ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, x ≤ v (algebraMap O C
      (Matrix.of fun a b : Fin (i.val + 1) =>
        ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  obtain ⟨N, u, hu, hlen⟩ := h
  obtain ⟨hx1, c, hc, hkill⟩ := exists_smul_eq_zero_of_hasLen hv hlen hx
  refine ⟨hx1, ?_⟩
  let M : Matrix (Fin s) (Fin N) O := fun a k => res w (dl (u k)) a
  have hom : omTr M s le_rfl = Submodule.span O (Set.range fun k => res w (dl (u k))) := rfl
  have hspan : ∀ n (hn : n ≤ s), ∀ y : Fin n → O, c • y ∈ omTr M n hn := by
    intro n hn y
    let y' : Fin s → O := Function.extend (Fin.castLE hn) y 0
    have h1 : c • y' ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hkill _
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun O).2 ⟨r, ?_⟩
    funext a
    have h2 := congrFun hr (Fin.castLE hn a)
    have h3 : y' (Fin.castLE hn a) = y a := (Fin.castLE_injective hn).extend_apply y 0 a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3] at h2 ⊢
    exact h2
  obtain ⟨ι, -, hι⟩ := charThm C v O hv s N M c hc hspan
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  have hfull := char_len hv M ι s le_rfl (hι s le_rfl)
  rw [hom] at hfull
  have hxe := hasLen_unique hv hlen hfull
  refine ⟨fun b => u (ι b), fun b => hu _, fun i => ?_⟩
  have hd := hv.le_of_dvd (minor_dvd_minor M ι hι (i.val + 1) s i.isLt le_rfl)
  rw [← hxe] at hd
  exact hd

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtens
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharDepth


open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ in
theorem isCanonGauge_mapFB_tower {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) {h : PS k 2 d} {R' : Type} [CommRing R'] [Algebra R' k]
    (φ : R →+* R') (hφ : ∀ x, algebraMap R' k (φ x) = algebraMap R k x) (hh : B.IsCanonGauge k h) :
    (FBMap.mapFB φ B).IsCanonGauge k h := by
  have hK : ∀ {n : ℕ} (f : PS R n d), FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
    intro n f
    ext mo
    simp only [MvPowerSeries.coeff_map, hφ]
  have hF : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => hK _
  have hA : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => hK _
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF]; exact (hK _).trans hh.ph1
  · rw [hF]; exact (hK _).trans hh.ph2
  · exact (hK _).trans hh.sy
  · rw [hA]; exact (hK _).trans (hh.ad a)

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_formalBiext_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧
      (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧
      B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X
  letI := io.toAlgebra
  obtain ⟨BT, e1, e2, -, -, -, -, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨-, -, h3, h4⟩ := e7 X.C
  refine ⟨FBMap.mapFB X.ι BT, ?_, fun a => ?_,
    isCanonGauge_mapFB_tower BT X.ι (fun x => (X.comp x).symm) ((h3 _).2 h4)⟩
  · rw [← e1]; rfl
  · rw [← e2]; rfl

end GlobalTheory.CharDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
section
set_option autoImplicit false

namespace GlobalTheory.CharDepth

open IsLocalRing Formalism.L2.Pj

theorem exists_local_extension_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O) (φ : A →+* B) (hφ : Function.Injective φ)
    (hint : φ.IsIntegral) (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_21; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 v hv φ hφ hint ι h_21 hι; exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension)
  | exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | (apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension ..)

theorem ValExt.exists_local_extension :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∀ (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ ι' : T'.V →+* X.O, IsLocalHom ι' ∧ ι'.comp φ = X.ι := by
  intro T T' φ hφ hfin p _ X
  haveI := X.ι_local
  refine exists_local_extension_of_integral X.v X.ints φ hφ hfin.to_isIntegral X.ι ?_
  have h : (algebraMap X.O X.C).comp X.ι = X.ιF.comp (algebraMap T.V T.Fr) := by
    ext x; exact (X.comp x).symm
  rw [h, RingHom.coe_comp]
  exact X.ιF.injective.comp (IsFractionRing.injective T.V T.Fr)

end GlobalTheory.CharDepth
end

