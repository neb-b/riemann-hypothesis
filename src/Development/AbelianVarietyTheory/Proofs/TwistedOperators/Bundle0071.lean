module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0475

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryDivisorsExistDiscretelyValued
section
noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.InertZeta

theorem elementaryDivisors_exist_discretely_valued : Smith := by
  intro L _ _ ϖ n hϖ g hg
  have hv0 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.exp_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hv0 (by rw [h, map_zero])
  have hnt : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, hv0, by rw [hϖ]; decide⟩
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  let G : GL (Fin n) L := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.2 hg)
  obtain ⟨c, hc0, hcg, -⟩ := P.glint_exists_denom (n := Fin n) A G
  obtain ⟨d, -, k₁, h₁, k₂, h₂, e⟩ := P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ hϖ0
    (fun x hx => by
      have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      refine ⟨-WithZero.log (Valued.v x), ?_⟩
      rw [hϖ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hx']) G c hc0 hcg
  refine ⟨d, k₁, (k₁⁻¹ : GL (Fin n) L), k₂, (k₂⁻¹ : GL (Fin n) L), P.cartan_entries_of_mem _ _ h₁,
    P.cartan_entries_of_mem _ _ (inv_mem h₁), P.cartan_entries_of_mem _ _ h₂,
    P.cartan_entries_of_mem _ _ (inv_mem h₂), k₁.inv_mul, k₂.mul_inv, ?_⟩
  exact e

end GlobalTheory.InertZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisOfIsQuadraticExtension
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem exists_basis_of_isQuadraticExtension (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] :
    ∃ (δ : K) (e : Module.Basis (Fin 2) K L), ¬ IsSquare δ ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ := by
  have hr : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have : IsGalois K L := inferInstance
  have hc : Nat.card (L ≃ₐ[K] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
  have : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[K] L)
  have h2 : σ * σ = 1 := by
    have := pow_card_eq_one' (x := σ)
    rwa [hc, pow_two] at this
  obtain ⟨δ, b, hδ, h0, -, h1⟩ := GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr
    (fun x => by simpa using congrArg (fun f : L ≃ₐ[K] L => f x) h2)
    (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext fun x => h x))
  exact ⟨δ, b, hδ, h0, h1⟩

theorem exists_completion_hom_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

theorem normTheorem : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L], NormTheorem K L := by
  intro K L _ _ _ _ _ _ t
  obtain ⟨δ, e, hδ, h0, h1⟩ := exists_basis_of_isQuadraticExtension K L
  have : FiniteDimensional K L := Module.Finite.of_basis e
  refine ⟨fun h => ⟨fun v => toUnits_mem_normGroup _ h, fun w => toUnits_mem_normGroup _ h⟩, ?_⟩
  rintro ⟨hf, hi⟩
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ ⟨0, by simp⟩
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt K δ t hδ0 t.ne_zero
    (fun σ => by
      obtain ⟨w, f, hw⟩ := exists_completion_hom_real σ
      obtain ⟨a, b, hab⟩ := (mem_normGroup_iff_form e h0 h1).1 (hi w)
      refine ⟨f a, f b, ?_⟩
      have h3 : algebraMap K w.Completion t = a ^ 2 - algebraMap K w.Completion δ * b ^ 2 := hab
      rw [← hw, ← hw, h3, map_sub, map_mul, map_pow, map_pow])
    (fun v => (mem_normGroup_iff_form e h0 h1).1 (hf v))
  refine mem_globalNorms_iff.2 ⟨a • e 0 + b • e 1, ?_⟩
  rw [hab]
  refine GlobalTheory.QuadNormBase.norm_of_basis e δ h0 ?_ a b
  rw [h1, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.QuadSymbol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceOfValuationRing
section
open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.EmbeddingPlace

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FinitePlace.mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def,
    NNReal.coe_le_one]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

open NumberField IsDedekindDomain in
private theorem valuation_le_one_iff_exists_eq_mul_inv_of_notMem {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) (x : L) :
    v.valuation L x ≤ 1 ↔
      ∃ a, ∃ s ∉ v.asIdeal, x = algebraMap R L a * (algebraMap R L s)⁻¹ := by
  rw [← Valuation.mem_valuationSubring_iff,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← ValuationSubring.mem_toSubring, HeightOneSpectrum.valuationSubringAtPrime_toSubring,
    Subalgebra.mem_toSubring]
  simp only [Localization.subalgebra.ofField]
  change (∃ a s, ∃ (_ : s ∈ v.asIdeal.primeCompl),
      x = algebraMap R L a * (algebraMap R L s)⁻¹) ↔ _
  exact ⟨fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩, fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩⟩

open NumberField IsDedekindDomain in
private theorem exists_heightOneSpectrum_range_iff_finitePlace_le_one {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0)
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) (ι : K →+* FractionRing O) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal ∧
      ∀ x : K, ι x ∈ (algebraMap O (FractionRing O)).range ↔ FinitePlace.mk la x ≤ 1 := by
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hint : ∀ y : 𝓞 K, IsIntegral O (ι (algebraMap (𝓞 K) K y)) := fun y =>
    IsIntegral.map_of_comp_eq (algebraMap ℤ O) ι (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe y)
  let ψ : 𝓞 K →+* O :=
    { toFun := fun y => IsIntegralClosure.mk' O (ι (algebraMap (𝓞 K) K y)) (hint y)
      map_one' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_mul' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_zero' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_add' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk']) }
  have hψ : ∀ y : 𝓞 K, algebraMap O (FractionRing O) (ψ y) = ι (algebraMap (𝓞 K) K y) :=
    fun y => IsIntegralClosure.algebraMap_mk' O _ (hint y)
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal O).comap ψ
  have hpP : (p : 𝓞 K) ∈ P := Ideal.mem_comap.mpr (by rw [map_natCast]; exact hpO)
  have hPne : P ≠ ⊥ := by
    intro h
    have hp0 := hpP
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hp0
    exact hp hp0
  have hunitP : ∀ s : 𝓞 K, s ∉ P → IsUnit (ψ s) := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.mp hs
  let la : HeightOneSpectrum (𝓞 K) :=
    { asIdeal := P, isPrime := Ideal.IsPrime.comap ψ, ne_bot := hPne }
  refine ⟨la, hpP, fun x => ?_⟩
  rw [_root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff]
  constructor
  · rintro ⟨o, ho⟩
    by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hy : la.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    obtain ⟨a, s, hs, hxa⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x⁻¹).mp hy.le
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hs (zero_mem _)
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr this
    have hsa : algebraMap (𝓞 K) K a = x⁻¹ * algebraMap (𝓞 K) K s := by
      rw [hxa, inv_mul_cancel_right₀ hs0]
    have hvs : la.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact le_antisymm (la.intValuation_le_one s)
        (not_lt.mp fun h => hs ((la.intValuation_lt_one_iff_mem s).mp h))
    have hva : la.intValuation a < 1 := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      change la.valuation K (algebraMap (𝓞 K) K a) < 1
      rw [hsa, map_mul, hvs, mul_one]
      exact hy
    have ha : ψ a ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mem_comap.mp ((la.intValuation_lt_one_iff_mem a).mp hva)
    have heq : o * ψ a = ψ s := hinj (by
      rw [map_mul, ho, hψ, hψ, hsa, map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
        map_one, one_mul])
    have hunit : IsUnit (o * ψ a) := by
      rw [heq]
      exact hunitP s hs
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_mul_isUnit_right hunit)
  · intro h
    obtain ⟨a, s, hs, rfl⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x).mp h
    refine ⟨ψ a * ↑(hunitP s hs).unit⁻¹, ?_⟩
    rw [map_mul, map_units_inv, IsUnit.unit_spec, hψ, hψ, map_mul, map_inv₀]


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.EmbeddingPlace.exists_place : ∀ (D : _root_.Formalism.BasicNotions.D7) (Ks : Type) [Field Ks] [NumberField Ks] (i : D.ntw.Tw) (ι : Ks →+* FractionRing (D.ntw.O i)), ∃ la : HeightOneSpectrum (𝓞 Ks), ((D.ntw.l i : ℕ) : 𝓞 Ks) ∈ la.asIdeal ∧ ∀ x : Ks, ι x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range ↔ FinitePlace.mk la x ≤ 1 := by
  intro D Ks _ _ i ι
  haveI := D.ntw.domO i
  haveI := D.ntw.dvrO i
  exact exists_heightOneSpectrum_range_iff_finitePlace_le_one (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero (D.ntw.O_l i) ι

end GlobalTheory.EmbeddingPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryBlockDiagonalLeviElement
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem _root_.GlobalTheory.InertZeta.leviExists : _root_.GlobalTheory.InertZeta.LeviExists := by
  intro L _ _ ϖ σ q N hq a g₀
  obtain ⟨-, -, hσϖ, hv, -⟩ := hq
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.SatakeWeyl.embExists L σ (N + 2) N _root_.GlobalTheory.InertZeta.mid
    _root_.GlobalTheory.InertZeta.mid_injective _root_.GlobalTheory.InertZeta.mid_rev
  obtain ⟨h1, h2⟩ := hι g₀
  set d : Fin (N + 2) → L := fun i => if i = 0 then ϖ ^ a else if i = Fin.last (N + 1) then ϖ ^ (-a) else 1
  have hd : ∀ i, σ (d i) * d i.rev = 1 := by
    intro i
    rcases _root_.GlobalTheory.InertZeta.idx_cases i with rfl | ⟨k, rfl⟩ | rfl
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, mul_inv_cancel₀ (zpow_ne_zero a hϖ)]
    · simp [d, ← _root_.GlobalTheory.InertZeta.mid_rev, _root_.GlobalTheory.InertZeta.mid_ne_zero,
        _root_.GlobalTheory.InertZeta.mid_ne_last]
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, inv_mul_cancel₀ (zpow_ne_zero a hϖ)]
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.SatakeWeyl.exists_mat (σ := σ) (Matrix.diagonal d) (by
    ext i j
    unfold _root_.Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, _root_.Formalism.UG.P.fIwasawa_antiJ]
    split_ifs with h
    · subst h
      simpa using hd i
    · simp)
  have h0 : (0 : Fin (N + 2)) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_zero k hk
  have hl : Fin.last (N + 1) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_last k hk
  have hm : _root_.GlobalTheory.SatakeWeyl.mat (D * ι g₀) =
      Matrix.diagonal d * _root_.GlobalTheory.SatakeWeyl.mat (ι g₀) := by
    rw [← hD]
    rfl
  refine ⟨D * ι g₀, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hm, Matrix.diagonal_mul]
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    by_cases hi : i ∈ Set.range _root_.GlobalTheory.InertZeta.mid
    · by_cases hj : j ∈ Set.range _root_.GlobalTheory.InertZeta.mid
      · obtain ⟨k, rfl⟩ := hi
        obtain ⟨l, rfl⟩ := hj
        simp [_root_.GlobalTheory.InertZeta.blk_mid] at hij
      · rw [h2 i j (Or.inr hj), Matrix.one_apply_ne hne, mul_zero]
    · rw [h2 i j (Or.inl hi), Matrix.one_apply_ne hne, mul_zero]
  · rw [hm, Matrix.diagonal_mul, h2 0 0 (Or.inl h0), Matrix.one_apply_eq, mul_one]
    simp [d]
  · rw [hm, Matrix.diagonal_mul, h2 _ _ (Or.inl hl), Matrix.one_apply_eq, mul_one]
    simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero]
  · intro i j
    rw [hm, Matrix.diagonal_mul, h1]
    simp [d, _root_.GlobalTheory.InertZeta.mid_ne_zero, _root_.GlobalTheory.InertZeta.mid_ne_last]

end GlobalTheory.InertZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisors
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem relIndex_pi_univ {ι : Type} [Fintype ι] {G : Type} [AddCommGroup G] (I J : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ J).relIndex (AddSubgroup.pi Set.univ I) = ∏ a, (J a).relIndex (I a) := by
  classical
  let φ : (AddSubgroup.pi Set.univ I) →+ ∀ a, (I a ⧸ (J a).addSubgroupOf (I a)) :=
    { toFun := fun x a => QuotientAddGroup.mk (⟨(x : ι → G) a, x.2 a (Set.mem_univ a)⟩ : I a)
      map_zero' := by funext a; rfl
      map_add' := fun x y => by funext a; rfl }
  have hsurj : Function.Surjective φ := by
    intro c
    choose y hy using fun a => QuotientAddGroup.mk_surjective (c a)
    refine ⟨⟨fun a => (y a : G), fun a _ => (y a).2⟩, ?_⟩
    funext a
    show QuotientAddGroup.mk (⟨(y a : G), _⟩ : I a) = c a
    rw [← hy a]
  have hker : φ.ker = (AddSubgroup.pi Set.univ J).addSubgroupOf (AddSubgroup.pi Set.univ I) := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h a _
      have := congrFun h a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf] at this
      exact this
    · intro h
      funext a
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf]
      exact h a (Set.mem_univ a)
  unfold AddSubgroup.relIndex AddSubgroup.index
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, Nat.card_pi]

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def scaledInt (c : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft c)

theorem mem_scaledInt {c x : L} : x ∈ scaledInt c ↔ c * x ∈ intL L := Iff.rfl

theorem mulLeft_surjective {c : L} (hc : c ≠ 0) : Function.Surjective (AddMonoidHom.mulLeft c) :=
  fun y => ⟨c⁻¹ * y, by simp [AddMonoidHom.mulLeft, mul_inv_cancel_left₀ hc]⟩

theorem mulLeft_injective {c : L} (hc : c ≠ 0) : Function.Injective (AddMonoidHom.mulLeft c) :=
  fun x y h => mul_left_cancel₀ hc h

theorem relIndex_scaledInt {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : ℕ) :
    (intL L).toAddSubgroup.relIndex (scaledInt (ϖ ^ d)) = q ^ (2 * d) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have h1 : (intL L).toAddSubgroup.relIndex (scaledInt ϖ) = q ^ 2 := by
    have hm : ((scaledInt ϖ).map (AddMonoidHom.mulLeft ϖ)) = (intL L).toAddSubgroup :=
      AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective h0) _
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_injective h0), hm]
    exact intIndex L ϖ σ q hU
  induction d with
  | zero =>
    have : scaledInt (ϖ ^ 0) = (intL L).toAddSubgroup := by
      ext x; simp [mem_scaledInt]
    rw [this, AddSubgroup.relIndex_self]; simp
  | succ d ih =>
    have hle1 : (intL L).toAddSubgroup ≤ scaledInt (ϖ ^ d) := fun x hx =>
      mul_mem (pow_mem hϖ d) hx
    have hle2 : scaledInt (ϖ ^ d) ≤ scaledInt (ϖ ^ (d + 1)) := fun x hx => by
      rw [mem_scaledInt] at hx ⊢
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact mul_mem hϖ hx
    have hc : scaledInt (ϖ ^ (d + 1)) = (scaledInt ϖ).comap (AddMonoidHom.mulLeft (ϖ ^ d)) := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_scaledInt]
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact Iff.rfl
    have hstep : (scaledInt (ϖ ^ d)).relIndex (scaledInt (ϖ ^ (d + 1))) = q ^ 2 := by
      rw [hc, scaledInt, AddSubgroup.relIndex_comap,
        AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective (pow_ne_zero d h0)), h1]
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih, hstep]
    ring

end

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem intV_vecMul {r : Fin n → L} {M : Matrix (Fin n) (Fin n) L} (hr : r ∈ intV L n) (hM : IsInt M) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  simp only [Matrix.vecMul, dotProduct]
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)

theorem preLat_diagonal (ϖ : L) (d : Fin n → ℕ) :
    preLat (Matrix.diagonal fun i => ϖ ^ d i) = AddSubgroup.pi Set.univ fun i => scaledInt (ϖ ^ d i) := by
  ext r
  rw [mem_preLat, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_scaledInt, Matrix.vecMul_diagonal, mul_comm (r _)]

theorem latIndex_diagonal {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : Fin n → ℕ) :
    (intV L n).relIndex (preLat (Matrix.diagonal fun i => ϖ ^ d i)) = q ^ (2 * ∑ i, d i) := by
  rw [preLat_diagonal, intV, relIndex_pi_univ]
  simp only [relIndex_scaledInt hU, Finset.mul_sum, Finset.prod_pow_eq_pow_sum]

theorem relIndex_preLat_mul {A D a a' : Matrix (Fin n) (Fin n) L} (ha : IsInt a) (ha' : IsInt a') (ea : a' * a = 1)
    (hpre : ∀ r, r ∈ preLat A ↔ r ᵥ* a ∈ preLat D) :
    (intV L n).relIndex (preLat A) = (intV L n).relIndex (preLat D) := by
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hf : ∀ r, f r = r ᵥ* a := fun r => rfl
  have hsurj : Function.Surjective f := fun y => ⟨y ᵥ* a', by rw [hf, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : preLat A = (preLat D).comap f := by
    ext r; rw [AddSubgroup.mem_comap, hf]; exact hpre r
  have h2 : intV L n = (intV L n).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hf]
    refine ⟨fun h => intV_vecMul h ha, fun h => ?_⟩
    have := intV_vecMul h ha'
    rwa [Matrix.vecMul_vecMul, ea2, Matrix.vecMul_one] at this
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj, ← h2]

end

theorem latIndex_of_smith : Smith → LatIndex := by
  intro hS L _ _ ϖ σ q n hU A k hA hdet
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hA0 : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hdet; exact WithZero.exp_ne_zero hdet.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hv A hA0
  set D := Matrix.diagonal fun i => ϖ ^ d i with hD
  have ea2 : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb2 : b' * b = 1 := mul_eq_one_comm.1 eb

  have hDint : IsInt D := by
    have : D = a' * (a * D * b) * b' := by
      rw [show a' * (a * D * b) * b' = (a' * a) * D * (b * b') by simp only [Matrix.mul_assoc], ea, eb,
        Matrix.one_mul, Matrix.mul_one]
    rw [this]
    exact (ha'.mul hA).mul hb'
  have hvz : ∀ z : ℤ, Valued.v (ϖ ^ z) = WithZero.exp (-z) := fun z => by
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]; congr 1; simp
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hDint i i
    rw [hD, Matrix.diagonal_apply_eq] at h
    have h' : Valued.v (ϖ ^ d i) ≤ 1 := h
    rw [hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at h'
    omega
  set e : Fin n → ℕ := fun i => (d i).toNat with he
  have hde : ∀ i, d i = (e i : ℤ) := fun i => (Int.toNat_of_nonneg (hd i)).symm
  have hDe : D = Matrix.diagonal fun i => ϖ ^ e i := by
    rw [hD]; congr 1; funext i; rw [hde i, zpow_natCast]

  have hk : k = ∑ i, e i := by
    have hva : Valued.v a.det = 1 := v_det_eq_one ha ha' ea2
    have hvb : Valued.v b.det = 1 := v_det_eq_one hb hb' eb
    rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, hva, hvb, one_mul, mul_one, hDe,
      Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, ← zpow_natCast, hvz, WithZero.exp_inj] at hdet
    exact_mod_cast (neg_inj.1 hdet).symm

  have hpre : ∀ r, r ∈ preLat (a * D * b) ↔ r ᵥ* a ∈ preLat D := fun r => by
    show r ᵥ* (a * D * b) ∈ intV L n ↔ (r ᵥ* a) ᵥ* D ∈ intV L n
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
    refine ⟨fun h => ?_, fun h => intV_vecMul h hb⟩
    have := intV_vecMul h hb'
    rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this
  rw [relIndex_preLat_mul ha ha' ea hpre, hDe, latIndex_diagonal hU, hk]

end GlobalTheory.InertZeta
end
end

