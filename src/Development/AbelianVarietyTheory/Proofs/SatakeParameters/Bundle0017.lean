module

public import Mathlib
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
section
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem tensor_exists_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_eq_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add (f := _)] at h0 h1
  exact ⟨h0, h1⟩

theorem mem_ALint_of_supported_at_split : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L),
    Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 →
    ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) →
    Valued.v (s.proj (L := L) z) ≤ 1 →
    Valued.v (s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 →
    z ∈ ReciprocityTheory.Aut.ALint L := by
  intro L _ _ _ s e he hc z hz hp hq
  have hne : (e : L) ≠ IsCMField.complexConj L (e : L) := by
    intro h
    rw [← h, he] at hc
    exact lt_irrefl _ hc
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), (e : L)] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * ((e : L) - IsCMField.complexConj L (e : L)) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = (e : L) := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have hoff : ∀ w, w ≠ s.v → A w = 0 ∧ B w = 0 := by
    intro w hw
    have h := hz w hw
    rw [hAB] at h
    apply tensor_decomp_eq_zero b
    rw [hb0, hb1]
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have h1 : s.proj (L := L) z = A s.v + s.i (e : L) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L (e : L)) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : Valued.v (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact hc), he]
  have hBv : Valued.v (B s.v) ≤ 1 := by
    have hm : (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) * B s.v =
        s.proj (L := L) z - s.proj (L := L) (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    have hv := congrArg Valued.v hm
    rw [map_mul, hu, one_mul] at hv
    rw [hv]
    exact Valuation.map_sub_le _ hp hq
  have hAv : Valued.v (A s.v) ≤ 1 := by
    have hm : A s.v = s.proj (L := L) z - s.i (e : L) * B s.v := by rw [h1]; ring
    rw [hm]
    refine Valuation.map_sub_le _ hp ?_
    rw [map_mul, he, one_mul]
    exact hBv
  have hAi : ∀ w, A w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hAv
    · rw [(hoff w hw).1]; exact zero_mem _
  have hBi : ∀ w, B w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hBv
    · rw [(hoff w hw).2]; exact zero_mem _
  have hsplit : ((e : L) ⊗ₜ[maximalRealSubfield L] B : ReciprocityTheory.Aut.AL L) =
      ((e : L) ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) *
        ((1 : L) ⊗ₜ[maximalRealSubfield L] B) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [hAB, hsplit]
  refine Subring.add_mem _ (Subring.subset_closure (Or.inr ⟨A, hAi, rfl⟩))
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨B, hBi, rfl⟩)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.Tr

def SplitBy {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) {m : ℕ} (s : Fin m → (V ⟶ Z)) : Prop :=
  ∃ hs : ∀ j, s j ≫ f = y, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
    ∐ (fun _ : Fin m => V) ⟶ pullback f y)

def Splits {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) : Prop :=
  ∃ (m : ℕ) (s : Fin m → (V ⟶ Z)), SplitBy f y s

def splitSieve {Z X S : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) : Sieve S :=
  Sieve.generate (fun V (v : V ⟶ S) => Splits f (v ≫ x))

theorem IsTransfer.apply_of_splitBy (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z}
    (ht : IsTransfer R f t) {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)} (hs : SplitBy f y s) :
    (free R).map (yoneda.map y) ≫ t = ∑ j, (free R).map (yoneda.map (s j)) :=
  ht V y m s hs.1 hs.2

end GlobalTheory.EtC.Tr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGalois
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

theorem exists_int_moved (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (hc : c ≠ 1) : ∃ θ : 𝓞 E, c (θ : E) ≠ (θ : E) := by
  by_contra h
  push_neg at h
  apply hc
  ext z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) z
  simp only [map_div₀, AlgEquiv.one_apply]
  exact congrArg₂ (· / ·) (h a) (h b)

theorem finite_setOf_mem_asIdeal (E : Type) [Field E] [NumberField E] (δ : 𝓞 E) (h : δ ≠ 0) :
    {w : HeightOneSpectrum (𝓞 E) | δ ∈ w.asIdeal}.Finite := by
  have := Ideal.finite_factors (R := 𝓞 E) (I := Ideal.span {δ}) (by simpa using h)
  refine this.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hw

theorem eventually_degOne_moved : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w →
      ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  intro F E _ _ _ _ _ _ c hc
  obtain ⟨θ, hθ⟩ := exists_int_moved F E c hc
  have hint : IsIntegral ℤ (c (θ : E)) := θ.isIntegral_coe.map c.toRingHom.toIntAlgHom
  set θ' : 𝓞 E := ⟨c (θ : E), hint⟩ with hθ'
  have hδ : θ - θ' ≠ 0 := by
    intro h0
    apply hθ
    have := congrArg (fun t : 𝓞 E => (t : E)) h0
    push_cast at this
    exact (sub_eq_zero.mp this).symm
  refine (finite_setOf_mem_asIdeal E (θ - θ') hδ).subset ?_ |> Filter.eventually_cofinite.mpr
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hnot
  apply hw
  intro hdeg
  obtain ⟨u, hu⟩ := hdeg θ
  refine ⟨θ - algebraMap (𝓞 F) (𝓞 E) u, hu, fun y hy hyw => hnot ?_⟩
  have hcu : c ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) := by
    have : ((algebraMap (𝓞 F) (𝓞 E) u : 𝓞 E) : E) = algebraMap F E (u : F) := rfl
    rw [this, AlgEquiv.commutes]
  have hy' : y = θ' - algebraMap (𝓞 F) (𝓞 E) u := by
    apply RingOfIntegers.ext
    rw [hy]
    push_cast
    rw [map_sub, hcu]
    rfl
  have := w.asIdeal.sub_mem hu hyw
  rw [hy'] at this
  convert this using 1
  ring

end GlobalTheory.HeckeSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongrModPowResidueDegreeOneFactors
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory

theorem exists_shift_mod_pow_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (θ : 𝓞 E) (D : 𝓞 F), (∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) → ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ → m ≤ Ideal.span {D} → ∀ (y : 𝓞 E) (N : ℕ), ∃ k : 𝓞 E, k - algebraMap (𝓞 F) (𝓞 E) D * y ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (m ^ N) ∧ ∀ P : HeightOneSpectrum (𝓞 E), ¬ m ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → k ∈ P.asIdeal → DegOne F P := by
  intro F E _ _ _ _ _ θ D hgen m hm hmD y N
  obtain ⟨u, v, huv⟩ := hgen y
  have hmN : m ^ N ≠ ⊥ := pow_ne_zero N hm
  obtain ⟨a, b, ha, hb, -, hcop⟩ := exists_reps_coprime_outside_modulus (𝓞 F) (m ^ N) u v hmN
  refine ⟨algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ, ?_, ?_⟩
  · rw [huv]
    have e : algebraMap (𝓞 F) (𝓞 E) a + algebraMap (𝓞 F) (𝓞 E) b * θ -
        (algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) =
        algebraMap (𝓞 F) (𝓞 E) (a - u) + algebraMap (𝓞 F) (𝓞 E) (b - v) * θ := by
      simp only [map_sub]; ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ ha)
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb))
  · intro P hmP hk
    have hPmax : P.asIdeal.IsMaximal := P.isMaximal
    have hpmax : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal
    have hmNp : ¬ m ^ N ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := fun h =>
      hmP (hpmax.isPrime.le_of_pow_le h)
    have hD : algebraMap (𝓞 F) (𝓞 E) D ∉ P.asIdeal := by
      intro h
      apply hmP
      refine hmD.trans ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      exact h
    have hbP : algebraMap (𝓞 F) (𝓞 E) b ∉ P.asIdeal := by
      intro h
      apply hcop _ hpmax hmNp
      refine ⟨?_, Ideal.mem_comap.mpr h⟩
      rw [Ideal.mem_comap]
      have := P.asIdeal.sub_mem hk (P.asIdeal.mul_mem_right θ h)
      simpa using this
    exact residue_degree_one_of_linear_mem (𝓞 F) (𝓞 E) P.asIdeal θ D a b hpmax hgen hD hbP hk
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrimeStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧ Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by
  first | exact @GlobalTheory.SplitSep.exists_sep | exact GlobalTheory.SplitSep.exists_sep | (intros; apply GlobalTheory.SplitSep.exists_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDoubleCosetAdicCompletionInvMulIntegral
section
open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeLocInt

open Matrix

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem le_exp_neg_one_of_lt {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at hx ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
  exact WithZero.exp_le_exp.2 (by omega)

theorem int_mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) :
    ∀ i j, Valued.v ((M * N) i j) ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ (fun l _ => ?_)
  rw [map_mul]
  exact mul_le_one' (hM i l) (hN l j)

theorem small_mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) < 1) :
    ∀ i j, Valued.v ((M * N) i j) < 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero (fun l _ => ?_)
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hM i l)) (hN l j)

theorem inv_mul_int_of_left_congr {n : ℕ} (ϖ : K) (k : ℕ)
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a a' b b' g g' : GL (Fin n) K)
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hsub : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) K) i j -
      (a' : Matrix (Fin n) (Fin n) K) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) K) =
      (a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K))
    (hg' : (g' : Matrix (Fin n) (Fin n) K) =
      (a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hDD : Formalism.UG.diagJ n ϖ⁻¹ k * Formalism.UG.diagJ n ϖ k = 1 := by
    unfold Formalism.UG.diagJ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp [hϖ0]
  have hinv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hg]
    have e : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K)) =
        ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K)) *
        Formalism.UG.diagJ n ϖ k) * (b : Matrix (Fin n) (Fin n) K) := by
      simp only [Matrix.mul_assoc]
    rw [e, Units.inv_mul, Matrix.mul_one, hDD, Matrix.mul_one, Units.inv_mul]
  have key : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ⁻¹ k *
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) =
      ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 + Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K))) *
        Formalism.UG.diagJ n ϖ k) * (b' : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD,
      add_sub_cancel]
    simp only [Matrix.mul_assoc]
  have hsub' : ∀ i j, Valued.v (((a' : Matrix (Fin n) (Fin n) K) -
      (a : Matrix (Fin n) (Fin n) K)) i j) < 1 := by
    intro i j; rw [Matrix.sub_apply, Valuation.map_sub_swap]; exact hsub i j
  have hN := small_mul hai hsub'
  have hX : ∀ i j, Valued.v ((1 + Formalism.UG.diagJ n ϖ⁻¹ k *
        (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a' : Matrix (Fin n) (Fin n) K) - (a : Matrix (Fin n) (Fin n) K))) *
        Formalism.UG.diagJ n ϖ k) i j) ≤ 1 := by
    intro i j
    rw [Matrix.add_apply]
    apply Valuation.map_add_le
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · simp only [Formalism.UG.diagJ, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [map_mul, map_mul]
      have h1 : Valued.v (if (i : ℕ) < k then ϖ⁻¹ else 1) ≤ WithZero.exp (1 : ℤ) := by
        split_ifs
        · rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg]
        · rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
      have h2 : Valued.v (if (j : ℕ) < k then ϖ else 1) ≤ 1 := by
        split_ifs
        · rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
        · rw [map_one]
      have h3 := le_exp_neg_one_of_lt (hN i j)
      calc _ ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul' (mul_le_mul' h1 h3) h2
        _ = 1 := by rw [mul_one, ← WithZero.exp_add]; simp
  rw [Units.val_mul, hinv, hg', key]
  exact int_mul (int_mul hbi hX) hb'

end GlobalTheory.HeckeLocInt

namespace GlobalTheory

theorem hecke_loc_inv_mul_int : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F) (k : ℕ), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (a a' b b' g g' : GL (Fin n) (v.adicCompletion F)), (∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) → (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  intro F _ _ v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'
  exact HeckeLocInt.inv_mul_int_of_left_congr ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hsub hg hg'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentity
section
open GlobalTheory.LatHecke

namespace GlobalTheory.HeckeSeries

open Classical

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem mem_subIdx_sub_iff {n k : ℕ} (hk : k ≤ n) {L M' M : Lat O K r}
    (hM' : M' ∈ subElem k L) :
    M ∈ subIdx (n - k) M' ↔ M ∈ subIdx n L ∧ M.1 ≤ M'.1 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := hM'
  have hq : 0 < qRes O := lt_of_lt_of_le two_pos two_le_qRes
  have hpow : qRes O ^ n = qRes O ^ (n - k) * qRes O ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  constructor
  · rintro ⟨h3, h4⟩
    refine ⟨⟨h3.trans h1, ?_⟩, h3⟩
    rw [← AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h3 h1, h4, h2, hpow]
  · rintro ⟨⟨-, h4⟩, h5⟩
    refine ⟨h5, ?_⟩
    have h := AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup M'.1.toAddSubgroup
      L.1.toAddSubgroup h5 h1
    rw [h4, h2, hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq k) h

theorem heckeElem_heckeAll_eq {E : Type} [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E)
    {n k : ℕ} (hk : k ≤ n) (L : Lat O K r) :
    heckeElem k (heckeAll (n - k) φ) L = ∑ M ∈ (subIdx_finite n L).toFinset,
      ((((subElem_finite k L).toFinset.filter (fun M' => M.1 ≤ M'.1)).card : ℂ)) • φ M := by
  rw [heckeElem_eq_sum]
  have h : ∀ M' ∈ (subElem_finite k L).toFinset, heckeAll (n - k) φ M' =
      ∑ M ∈ (subIdx_finite n L).toFinset, if M.1 ≤ M'.1 then φ M else 0 := by
    intro M' hM'
    rw [heckeAll_eq_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext M
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact mem_subIdx_sub_iff hk ((Set.Finite.mem_toFinset _).1 hM')
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem heckeSeries_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r),
    1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) •
      heckeElem k (heckeAll (n - k) φ) L = 0 := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ n L hn
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [heckeElem_heckeAll_eq φ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) L])]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun M hM => ?_
  rw [← Finset.sum_smul]
  have hM' : M ∈ subIdx n L := (Set.Finite.mem_toFinset _).1 hM
  have h := _root_.GlobalTheory.LatHecke.sum_alt_card_subElem_ge O K r n L M hn hM'
  convert zero_smul ℂ (φ M) using 2
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext M'
  simp

end GlobalTheory.HeckeSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLeStatement
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_integral_cocycles_rational_coboundaries_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  first | exact @GlobalTheory.cocycle_bound_length_le | exact GlobalTheory.cocycle_bound_length_le | (intros; apply GlobalTheory.cocycle_bound_length_le <;> assumption)
end

