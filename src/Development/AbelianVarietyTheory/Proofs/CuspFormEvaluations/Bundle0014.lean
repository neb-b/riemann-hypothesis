module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TwoMulPowFourDvdCardGeneralLinearGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory


open MvPolynomial in
theorem map_lap_one {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k' 1 τ τ' a a' (MvPolynomial.map f P) = MvPolynomial.map f (lap r n k 1 τ τ' a a' P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
    Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, pderiv_map]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 2
  by_cases h : b = b' <;> simp [Matrix.one_apply, h]


open MvPolynomial in
theorem map_rowShift {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (σ : T) (i i' : Fin (r σ)) (t : k) (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k' σ i i' (f t) (MvPolynomial.map f P) = MvPolynomial.map f (rowShift r n k σ i i' t P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowShift]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p s hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem map_mem_HHa {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (hf : Function.Surjective f) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n k' cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [map_lap_one, h1 τ hτ b b', map_zero]
  · intro σ i i' hi t
    obtain ⟨s, rfl⟩ := hf t
    rw [map_rowShift, h2 σ i i' hi s]
  · intro m hm
    exact h3 m (MvPolynomial.support_map_subset f P hm)

theorem finrank_le_of_span_sup_smul_top {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ} (x : Fin n → M) (I : Ideal R) (hI : I ≠ ⊤)
    (h : Submodule.span R (Set.range x) ⊔ (I • ⊤ : Submodule R M) = ⊤) : Module.finrank R M ≤ n := by
  set N := Submodule.span R (Set.range x) with hN
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (N := N) (N' := ⊤) (P := ⊤) (I := I) Module.Finite.fg_top le_rfl (by rw [h])
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem hr1
  have hmem : ∀ m : M, (r • (LinearMap.id : M →ₗ[R] M)) m ∈ N := fun m =>
    hr (Submodule.smul_mem_pointwise_smul m r ⊤ Submodule.mem_top)
  have hinj : Function.Injective ((r • (LinearMap.id : M →ₗ[R] M)).codRestrict N hmem) := by
    intro u v huv
    have : r • u = r • v := congrArg Subtype.val huv
    exact smul_right_injective M hr0 this
  haveI : Module.Finite R N := Module.Finite.span_of_finite R (Set.finite_range x)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank R N ≤ n := by
    simpa [Set.finrank] using finrank_range_le_card (R := R) x
  exact h1.trans h2

theorem Mfr_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Mfr l ≠ ⊤ := by
  intro h
  have hb : l.Mb = ⊤ := by
    rw [Ideal.eq_top_iff_one] at h ⊢
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 h
    have : y = 1 := H.bar.injective (by simpa using hy1)
    exact this ▸ hy
  have hp := l.prod
  rw [hb, Ideal.map_top, Ideal.top_mul] at hp
  have hn := congrArg Ideal.absNorm hp
  rw [Ideal.absNorm_top, Ideal.absNorm_span_natCast] at hn
  have h3 := l.three_le
  have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  rcases Nat.pow_eq_one.1 hn.symm with h' | h' <;> omega

theorem admissible_columns_le_and_harmonic_map_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → Dw.p + Dw.q ≤ n) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw l Xo c n d
  refine ⟨fun rk x0 hx => ?_, fun a P hP => ?_⟩
  swap
  · have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) := fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    exact map_mem_HHa Dw.mult n f hs _ _ _ P hP
  haveI := Dw.fin
  haveI := Dw.proj
  rw [← Dw.rank]
  refine finrank_le_of_span_sup_smul_top x0 (Mfr l) (Mfr_ne_top l) ?_
  unfold AdmX at hx
  refine top_le_iff.1 (hx.ge.trans ?_)
  exact sup_le_sup_right (Submodule.span_mono (Set.image_subset_range _ _)) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.EtaCard

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem nonempty_equiv_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)] (r : ℕ)
    (hr : Module.finrank O M = r) :
    Nonempty ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O] (Fin r → O ⧸ I)) := by
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ B.equivFun.restrictScalars O⟩

theorem nonempty_aut_equiv (O N : Type) [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (r : ℕ)
    (e : N ≃ₗ[O] (Fin r → O ⧸ I)) : Nonempty ((N ≃ₗ[O] N) ≃ GL (Fin r) (O ⧸ I)) := by
  have hs : Function.Surjective (algebraMap O (O ⧸ I)) := Ideal.Quotient.mk_surjective
  let e1 : (N ≃ₗ[O] N) ≃ ((Fin r → O ⧸ I) ≃ₗ[O ⧸ I] (Fin r → O ⧸ I)) :=
    { toFun := fun g => (e.symm ≪≫ₗ g ≪≫ₗ e).extendScalarsOfSurjective hs
      invFun := fun g => e ≪≫ₗ g.restrictScalars O ≪≫ₗ e.symm
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp }
  exact ⟨e1.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.toEquiv.trans
    Matrix.GeneralLinearGroup.toLin.symm.toEquiv)⟩

theorem span_sup_pow (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) (S : Submodule O M)
    (h : S ⊔ Ideal.span {a} • ⊤ = ⊤) (k : ℕ) : S ⊔ Ideal.span {a ^ k} • ⊤ = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine eq_top_iff.2 (ih.ge.trans (sup_le le_sup_left ?_))
    have h2 := congrArg (fun T : Submodule O M => Ideal.span {a ^ k} • T) h
    simp only [Submodule.smul_sup, ← Submodule.mul_smul, Ideal.span_singleton_mul_span_singleton,
      ← pow_succ] at h2
    exact h2.ge.trans (sup_le_sup_right Submodule.smul_le_right _)

variable (E : Type) [Field E] [NumberField E]

theorem finite_quot (k : ℕ) (hk : k ≠ 0) : Finite (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hk)

theorem card_quot (k : ℕ) : Nat.card (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) = k ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem charP_quot (k : ℕ) : CharP (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) k := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun h => ?_, fun h => Nat.cast_dvd_cast h⟩
  have h2 := map_dvd (Algebra.norm ℤ) h
  rw [← map_natCast (algebraMap ℤ (𝓞 E)), ← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap,
    Algebra.norm_algebraMap, Int.pow_dvd_pow_iff Module.finrank_pos.ne'] at h2
  exact_mod_cast h2

theorem finrank_eq [IsCMField E] : Module.finrank ℚ E = 2 * FD.fdeg E := by
  rw [FD.fdeg, IsTotallyComplex.finrank E]
  omega

theorem card_levGrp_and_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (R : ℕ), 1 < R → Finite (LevGrp Dw (R ^ 4)) ∧ Finite (LatMod Dw R) ∧ Nat.card (LatMod Dw R) = R ^ (2 * FD.fdeg E * (Dw.p + Dw.q)) ∧ Nat.card (LevGrp Dw (R ^ 4)) ≤ R ^ (8 * FD.fdeg E * (Dw.p + Dw.q) ^ 2) ∧ (Odd R → 2 ≤ Dw.p + Dw.q → 2 * R ^ 4 ∣ Nat.card (LevGrp Dw (R ^ 4))) ∧ (∃ x₀ : Fin (Dw.p + Dw.q) → Dw.La, Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤) ∧ ∀ (n : ℕ) (x₀ : Fin n → Dw.La), Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤ → ∀ (y : Fin n → LatMod Dw R) (g : LevGrp Dw (R ^ 4)), Submodule.span (𝓞 E) (Set.range fun b => g (shiftFam R x₀ y b)) = ⊤ := by
  intro E _ _ _ H Dw R hR
  have := Dw.fin
  have := Dw.proj
  have hR0 : R ≠ 0 := by omega
  have := finite_quot E R hR0
  have := finite_quot E (R ^ 4) (pow_ne_zero _ hR0)
  obtain ⟨e1⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {(R : 𝓞 E)}) _ Dw.rank
  obtain ⟨e4⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {((R ^ 4 : ℕ) : 𝓞 E)}) _ Dw.rank
  obtain ⟨g4⟩ := nonempty_aut_equiv _ _ _ _ e4
  refine ⟨Finite.of_equiv _ g4.symm, Finite.of_equiv _ e1.symm.toEquiv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e1.toEquiv, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul]
  · rw [Nat.card_congr g4]
    refine (Nat.card_le_card_of_injective _ Units.val_injective).trans (le_of_eq ?_)
    change Nat.card (Fin (Dw.p + Dw.q) → Fin (Dw.p + Dw.q) → _) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · intro ho h2
    rw [Nat.card_congr g4]
    exact two_mul_pow_four_dvd_card_generalLinearGroup _ R ho (charP_quot E _) hR _ h2
  · choose x₀ hx using fun i => Submodule.Quotient.mk_surjective _ (e1.symm (Pi.single i 1))
    refine ⟨x₀, ?_⟩
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, eq_top_iff]
    intro z _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (e1 z i)
    refine ⟨∑ i, c i • x₀ i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), e1.injective ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.mkQ_apply, hx, LinearEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm]) (by simp), ← hc]
    simp [Algebra.smul_def]
  · intro n x₀ hx y g
    have h1 : Submodule.span (𝓞 E) (Set.range fun b => x₀ b + R • qRep (y b)) ⊔
        Ideal.span {(R : 𝓞 E)} • ⊤ = ⊤ := by
      refine eq_top_iff.2 (hx.ge.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right))
      rintro _ ⟨b, rfl⟩
      have : x₀ b = (x₀ b + R • qRep (y b)) - (R : 𝓞 E) • qRep (y b) := by
        rw [Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial))
    have h2 := span_sup_pow _ _ _ _ h1 4
    rw [← Nat.cast_pow, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp] at h2
    have h3 := congrArg (Submodule.map g.toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3

end GlobalTheory.EtaCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NotIsBlockProdZero
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

theorem poly_ne_zero (K : Type) [Field K] (B : Bk Dw n) : B.poly K ≠ 0 := by
  classical
  unfold Bk.poly
  refine pow_ne_zero _ ?_
  intro h
  let v : LtN Dw n → K := fun l => if ∃ a : Fin B.i, l = ⟨B.τ, Fin.castLE B.hi a, B.col a⟩ then 1 else 0
  have h2 := congrArg (MvPolynomial.eval v) h
  rw [RingHom.map_det, map_zero] at h2
  have : (MvPolynomial.eval v).mapMatrix (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, v, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos ⟨a, rfl⟩, if_pos rfl]
    · rw [if_neg hab, if_neg]
      rintro ⟨d, hd⟩
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at hd
      have h1 : a = d := Fin.castLE_injective _ hd.1
      have h3 : b = d := B.col_inj hd.2
      exact hab (h1.trans h3.symm)
  rw [this, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem not_isBlockProd_zero (K : Type) [Field K] : ¬ IsBlockProd (0 : MvPolynomial (LtN Dw n) K) := by
  rintro ⟨nb, bs, -, h⟩
  exact Finset.prod_ne_zero_iff.2 (fun j _ => poly_ne_zero Dw n K (bs j)) h.symm

end GlobalTheory.BlockThInhab
end
end

