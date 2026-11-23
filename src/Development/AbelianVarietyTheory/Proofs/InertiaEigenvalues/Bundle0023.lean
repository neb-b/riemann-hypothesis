module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatrices
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

theorem finite_classes_mod_pow (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
    (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (N : ℕ) :
    ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K),
      ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O),
        algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) →
        ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
          x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  classical
  have hfin : Finite (O ⧸ Ideal.span {ϖ ^ (2 * N)}) :=
    IsLocalRing.finite_quotient_iff.mpr
      ⟨2 * N, by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  haveI := Fintype.ofFinite (Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}))
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hϖ.ne_zero
  let lift : O ⧸ Ideal.span {ϖ ^ (2 * N)} → O := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hlift : ∀ c, Ideal.Quotient.mk _ (lift c) = c := fun c =>
    (Ideal.Quotient.mk_surjective c).choose_spec
  let rep : Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}) →
      Matrix (Fin r ⊕ Fin t) (Fin r) K :=
    fun c => (algebraMap O K (ϖ ^ N))⁻¹ • (c.map lift).map (algebraMap O K)
  refine ⟨Finset.univ.image rep, fun x z hxz => ?_⟩
  have hdiff : ∀ i j, ∃ a : O, a * ϖ ^ (2 * N) = z i j - lift (Ideal.Quotient.mk _ (z i j)) :=
    fun i j => Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp (hlift _).symm)
  choose w hw using hdiff
  refine ⟨rep (z.map (Ideal.Quotient.mk _)), Finset.mem_image_of_mem _ (Finset.mem_univ _), Matrix.of w, ?_⟩
  ext i j
  have hx := congrFun (congrFun hxz i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, map_pow] at hx
  have hz : lift (Ideal.Quotient.mk _ (z i j)) = z i j - w i j * ϖ ^ (2 * N) := by
    rw [hw]; ring
  simp only [rep, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hz, map_sub,
    map_mul, map_pow, Matrix.of_apply, ← hx]
  field_simp
  ring

end GlobalTheory.GenUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldExistsGeneratorMinpoly
section
open Polynomial

namespace GlobalTheory

theorem finiteField_exists_generator_minpoly (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K]
    [Algebra (ZMod l) K] :
    ∃ (a : K) (p : (ZMod l)[X]), p.Monic ∧ Irreducible p ∧ aeval a p = 0 ∧
      aeval a (derivative p) ≠ 0 ∧ (∀ y : K, ∃ q : (ZMod l)[X], aeval a q = y) ∧
      Nat.card K = l ^ p.natDegree := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : FiniteDimensional (ZMod l) K := Module.Finite.of_finite
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod l) K
  refine ⟨pb.gen, minpoly (ZMod l) pb.gen, minpoly.monic pb.isIntegral_gen,
    minpoly.irreducible pb.isIntegral_gen, minpoly.aeval _ _, ?_, ?_, ?_⟩
  · exact (Algebra.IsSeparable.isSeparable (ZMod l) pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  · intro y
    obtain ⟨q, -, hq⟩ := pb.exists_eq_aeval y
    exact ⟨q, hq.symm⟩
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l) (V := K), ZMod.card, pb.natDegree_minpoly,
      pb.finrank]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldExistsTraceFormDualBasesPowOne
section
namespace GlobalTheory

theorem finiteField_exists_traceForm_dualBases_pow_one :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l],
      ∃ t : k →+ ZMod (l ^ 1), (∀ b, (∀ a, t (a * b) = 0) → b = 0) ∧
        ∃ (n : ℕ) (a e : Fin n → k), ∀ z, z = ∑ j, ((t (a j * z)).val : k) * e j := by
  intro l _ k _ _ _
  rw [pow_one]
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  have hnd := traceForm_nondegenerate (ZMod l) k
  let b := Module.finBasis (ZMod l) k
  let d := (Algebra.traceForm (ZMod l) k).dualBasis hnd b
  refine ⟨(Algebra.trace (ZMod l) k).toAddMonoidHom, ?_, Module.finrank (ZMod l) k, b, d, ?_⟩
  · intro x hx
    apply hnd.1 x
    intro y
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx y
  · intro z
    conv_lhs => rw [← d.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm z (b j)]
    simp only [LinearMap.toAddMonoidHom_coe]
    obtain ⟨c, hc⟩ : ∃ c, Algebra.trace (ZMod l) k (b j * z) = c := ⟨_, rfl⟩
    rw [hc]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvr
section
namespace GlobalTheory

open IsLocalRing

theorem finite_free_compact_adic_dvr
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧
      Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  classical
  let b := Module.Free.chooseBasis O M
  have hΦ : Continuous (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) := by
    have : (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) =
        fun v => ∑ i, v i • b i := by
      funext v; simp
    rw [this]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  let H : (Module.Free.ChooseBasisIndex O M → O) ≃ₜ M :=
    hΦ.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
  have hH : ∀ v, H v = b.equivFun.symm v := fun v => rfl
  have hcpt : CompactSpace M := by
    refine ⟨?_⟩
    have := isCompact_univ.image H.continuous
    rwa [Set.image_univ, H.surjective.range_eq] at this
  refine ⟨hcpt, ?_, ?_⟩
  · have hm : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
      have := (isAdic_iff.mp hadic).1 1
      simpa using this
    let S : Set (Module.Free.ChooseBasisIndex O M → O) :=
      ⋂ i, (fun v => v i) ⁻¹' ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)
    have hS : IsOpen S := isOpen_iInter_of_finite fun i => hm.preimage (continuous_apply i)
    have heq : (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) = H '' S := by
      ext m
      simp only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.lsmul_apply, S,
        Set.mem_image, Set.mem_iInter, Set.mem_preimage, hϖ.maximalIdeal_eq,
        Ideal.mem_span_singleton', hH]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨b.equivFun (ϖ • x), fun i => ⟨b.equivFun x i, ?_⟩, by simp⟩
        simp [mul_comm]
      · rintro ⟨v, hv, rfl⟩
        choose c hc using hv
        refine ⟨b.equivFun.symm c, ?_⟩
        rw [← LinearEquiv.map_smul]
        congr 1
        funext i
        simp [← hc i, mul_comm]
    rw [heq]
    exact H.isOpenMap S hS
  · refine (continuous_const_smul ϖ).isClosedEmbedding ?_
    exact smul_right_injective M hϖ.ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltration
section
namespace GlobalTheory

theorem finite_jumps_inf_filtration (E W : Type) [Field E] [AddCommGroup W] [Module E W]
    (D : Submodule E W) (F : ℤ → Submodule E W) (hD : Module.Finite E ↥D)
    (hF : ∀ a, F (a + 1) ≤ F a) :
    {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  have hanti : Antitone F := antitone_int_of_succ_le hF
  have hfin : ∀ a, Module.Finite E ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := D) inf_le_left
  have key : ∀ a b : ℤ, D ⊓ F (a + 1) ≠ D ⊓ F a → a < b →
      Module.finrank E ↥(D ⊓ F b) < Module.finrank E ↥(D ⊓ F a) := by
    intro a b ha hab
    haveI := hfin a
    apply Submodule.finrank_lt_finrank_of_lt
    have h1 : D ⊓ F b ≤ D ⊓ F (a + 1) := inf_le_inf_left _ (hanti (by omega))
    have h2 : D ⊓ F (a + 1) < D ⊓ F a := lt_of_le_of_ne (inf_le_inf_left _ (hF a)) ha
    exact lt_of_le_of_lt h1 h2
  refine Set.Finite.of_injOn (f := fun a => Module.finrank E ↥(D ⊓ F a))
    (t := Set.Iic (Module.finrank E ↥D)) ?_ ?_ (Set.finite_Iic _)
  · intro a _
    exact Submodule.finrank_mono inf_le_left
  · intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (key a b ha h).ne'
    · exact h
    · exact absurd hab (key b a hb h).ne

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteOfPerfectPairingZmod
section
open Function Cardinal

namespace GlobalTheory

theorem mk_addMonoidHom_le_of_surjective_of_injective {A A' X Y : Type} [AddCommGroup A]
    [AddCommGroup A'] [AddCommGroup X] [AddCommGroup Y] (f : A →+ A') (hf : Surjective f)
    (ι : X →+ Y) (hι : Injective ι) : #(A' →+ X) ≤ #(A →+ Y) := by
  refine mk_le_of_injective (f := fun g => (ι.comp g).comp f) ?_
  intro g h hgh
  ext x
  obtain ⟨a, rfl⟩ := hf x
  exact hι (DFunLike.congr_fun hgh a)

theorem exists_injective_zmod_addMonoidHom {a n : ℕ} (hn : n ≠ 0) (h : a ∣ n) :
    ∃ ι : ZMod a →+ ZMod n, Injective ι := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  haveI : NeZero a := ⟨ha⟩
  refine ⟨ZMod.lift a ⟨zmultiplesHom (ZMod (a * k)) (k : ZMod (a * k)), ?_⟩, ?_⟩
  · simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul]
    rw [← Nat.cast_mul, ZMod.natCast_self]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h2 : ((x.val : ℤ) : ZMod a) = x := by simp
    rw [← h2, ZMod.lift_coe] at hx
    simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul] at hx
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
    have hd : a ∣ x.val := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hk) hx
    have hv : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt x)
    rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_zero]

theorem mk_lt_mk_addMonoidHom_zmod_prime (p : ℕ) [hp : Fact p.Prime] (V : Type) [AddCommGroup V]
    (hV : ∀ x : V, p • x = 0) [Infinite V] : #V < #(V →+ ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod p) V := AddCommGroup.zmodModule hV
  let b := Module.Basis.ofVectorSpace (ZMod p) V
  set ι := Module.Basis.ofVectorSpaceIndex (ZMod p) V
  have hι : Infinite ι := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    haveI := h
    haveI : Finite V := Finite.of_equiv _ b.equivFun.toEquiv.symm
    exact not_finite V
  have hV1 : #V = #ι := by
    rw [b.repr.toEquiv.cardinal_eq, mk_finsupp_of_infinite, max_eq_left]
    exact (lt_aleph0_of_finite _).le.trans (aleph0_le_mk ι)
  have hr : Module.rank (ZMod p) V = #ι := b.mk_eq_rank''.symm
  have h0 : ℵ₀ ≤ Module.rank (ZMod p) V := hr ▸ aleph0_le_mk ι
  have h1 := lift_rank_lt_rank_dual h0
  rw [lift_id, rank_dual_eq_card_dual_of_aleph0_le_rank h0] at h1
  calc #V = Module.rank (ZMod p) V := by rw [hV1, hr]
    _ < #(V →ₗ[ZMod p] ZMod p) := h1
    _ = #(V →+ ZMod p) := ((AddMonoidHom.toZModLinearMapEquiv p).toEquiv.cardinal_eq).symm

theorem mk_lt_mk_addMonoidHom_zmod (n : ℕ) : ∀ (A : Type) [AddCommGroup A],
    (∀ x : A, n • x = 0) → n ≠ 0 → Infinite A → #A < #(A →+ ZMod n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ hA hn hinf
  rcases eq_or_ne n 1 with rfl | h1
  · exfalso
    haveI : Subsingleton A := ⟨fun x y => by
      have hx : x = 0 := by simpa using hA x
      have hy : y = 0 := by simpa using hA y
      rw [hx, hy]⟩
    exact not_finite A
  obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
    ⟨n.minFac, Nat.minFac_prime h1, n / n.minFac, (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm⟩
  haveI := Fact.mk hp
  have hm : m ≠ 0 := right_ne_zero_of_mul hn
  let f : A →+ A := AddMonoidHom.mk' (fun x => p • x) (fun x y => nsmul_add x y p)
  let P : AddSubgroup A := f.range
  have hmul : #A = #(A ⧸ P) * #P := by
    rw [(AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := P)).cardinal_eq, mk_prod,
      lift_id, lift_id]
  have hPle : #P ≤ #A := mk_le_of_injective Subtype.val_injective
  have hQle : #(A ⧸ P) ≤ #A := mk_le_of_surjective (QuotientAddGroup.mk_surjective)
  have hAinf : ℵ₀ ≤ #A := aleph0_le_mk A
  rcases hPle.lt_or_eq with hPlt | hPeq
  · rcases hQle.lt_or_eq with hQlt | hQeq
    · exact absurd hmul (ne_of_gt (mul_lt_of_lt hAinf hQlt hPlt))

    · letI : Infinite (A ⧸ P) := Cardinal.infinite_iff.mpr (hQeq ▸ hAinf)
      have hQp : ∀ y : A ⧸ P, p • y = 0 := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        exact ⟨x, rfl⟩
      obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_right p m)
      calc #A = #(A ⧸ P) := hQeq.symm
        _ < #(A ⧸ P →+ ZMod p) := mk_lt_mk_addMonoidHom_zmod_prime p (A ⧸ P) hQp
        _ ≤ #(A →+ ZMod (p * m)) :=
          mk_addMonoidHom_le_of_surjective_of_injective (QuotientAddGroup.mk' P)
            (QuotientAddGroup.mk_surjective) ι hι

  · letI : Infinite P := Cardinal.infinite_iff.mpr (hPeq ▸ hAinf)
    have hPm : ∀ y : P, m • y = 0 := by
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      show m • (p • x) = 0
      rw [smul_smul, mul_comm, hA x]
    have hlt : m < p * m := by
      have := hp.two_le
      have := Nat.pos_of_ne_zero hm
      nlinarith
    have hP := ih m hlt P hPm hm inferInstance
    obtain ⟨ι, hι⟩ := exists_injective_zmod_addMonoidHom hn (dvd_mul_left m p)
    calc #A = #P := hPeq.symm
      _ < #(P →+ ZMod m) := hP
      _ ≤ #(A →+ ZMod (p * m)) :=
        mk_addMonoidHom_le_of_surjective_of_injective f.rangeRestrict
          f.rangeRestrict_surjective ι hι

theorem finite_of_perfect_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A]
    [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C]
    [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C),
    Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  intro n _ A B C _ _ _ _ _ _ _ b ⟨e⟩ hb hbf
  have key : ∀ (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [AddCommGroup Y]
      [Module (ZMod n) Y] (c : X →ₗ[ZMod n] Y →ₗ[ZMod n] C), Bijective c.flip → Infinite X →
      #X < #Y := by
    intro X Y _ _ _ _ c hc hX
    have h1 : #Y = #(X →+ ZMod n) := by
      have e1 := (LinearEquiv.ofBijective c.flip hc).toEquiv
      have e2 : (X →ₗ[ZMod n] C) ≃ (X →ₗ[ZMod n] ZMod n) :=
        { toFun := fun g => e.toLinearMap ∘ₗ g
          invFun := fun g => e.symm.toLinearMap ∘ₗ g
          left_inv := fun g => by ext; simp
          right_inv := fun g => by ext; simp }
      have e3 := (AddMonoidHom.toZModLinearMapEquiv n (M := X) (M₁ := ZMod n)).toEquiv.symm
      exact (e1.trans (e2.trans e3)).cardinal_eq
    rw [h1]
    refine mk_lt_mk_addMonoidHom_zmod n X (fun x => ?_) (NeZero.ne n) hX
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hbff : Bijective b.flip.flip := by simpa using hb
  have hA : Finite A := by
    by_contra hA
    rw [not_finite_iff_infinite] at hA
    have h1 := key A B b hbf hA
    haveI : Infinite B := Cardinal.infinite_iff.mpr ((aleph0_le_mk A).trans h1.le)
    exact lt_asymm h1 (key B A b.flip hbff inferInstance)
  have hB : Finite B := by
    by_contra hB
    rw [not_finite_iff_infinite] at hB
    have h1 := key B A b.flip hbff hB
    haveI : Infinite A := Cardinal.infinite_iff.mpr ((aleph0_le_mk B).trans h1.le)
    exact not_finite A
  exact ⟨hA, hB⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayama
section
namespace GlobalTheory

theorem finite_quotient_of_complete_nakayama : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  intro R _ ϖ hR T Z _ _ _ _ hT hZ d N hdN s hs
  classical
  choose A C X hACX using hs
  choose limR hlimR using hR
  choose limT hlimT using hT
  have key : ∀ c : Z, ∀ n : ℕ, c = ∑ i ∈ s, (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) • i
      + ϖ ^ n • C^[n] c + d (∑ j ∈ Finset.range n, ϖ ^ j • X (C^[j] c)) := by
    intro c n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, Function.iterate_succ_apply']
      simp only [Finset.sum_range_succ]
      set e := C^[n] c with he
      conv_lhs => rw [hACX e]
      simp only [add_smul, Finset.sum_add_distrib, smul_add, map_add (f := _), map_smul, Finset.smul_sum,
        mul_smul, pow_succ]
      abel
  have hfin : ∀ c : Z, c - (∑ i ∈ s, limR (fun j => A (C^[j] c) i) • i
      + d (limT (fun j => X (C^[j] c)))) = 0 := by
    intro c
    apply hZ
    intro n
    have hk := key c n
    choose b hb using fun i => hlimR (fun j => A (C^[j] c) i) n
    obtain ⟨z, hz⟩ := hlimT (fun j => X (C^[j] c)) n
    refine ⟨C^[n] c - ∑ i ∈ s, b i • i - d z, ?_⟩
    have hα : ∀ i, limR (fun j => A (C^[j] c) i)
        = (∑ j ∈ Finset.range n, ϖ ^ j * A (C^[j] c) i) + ϖ ^ n * b i :=
      fun i => sub_eq_iff_eq_add'.mp (hb i)
    have hY := sub_eq_iff_eq_add'.mp hz
    simp only [hα, hY]
    rw [sub_eq_iff_eq_add]
    refine hk.trans ?_
    simp only [add_smul, Finset.sum_add_distrib, smul_sub, map_add (f := _), map_smul, Finset.smul_sum,
      mul_smul]
    abel
  have h0 : ∀ y : T, N.mkQ (d y) = 0 := by
    intro y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hdN ⟨y, rfl⟩
  refine ⟨⟨s.image N.mkQ, ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨c, rfl⟩ := N.mkQ_surjective q
  have hc := sub_eq_zero.mp (hfin c)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_add (f := _), h0, add_zero, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebra
section
namespace GlobalTheory

theorem finite_sq_eq_one_of_finite_algebra (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A]
    [Algebra k A] [Module.Finite k A] : Set.Finite {x : A | x ^ 2 = 1} := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Finite (TopologicalSpace.Clopens (PrimeSpectrum A)) :=
    Finite.of_injective (fun s : TopologicalSpace.Clopens (PrimeSpectrum A) => (s : Set (PrimeSpectrum A)))
      SetLike.coe_injective
  haveI : Finite {e : A // IsIdempotentElem e} :=
    Finite.of_equiv _ (PrimeSpectrum.isIdempotentElemEquivClopens (R := A)).symm.toEquiv
  set c : A := algebraMap k A (2⁻¹ : k) with hc
  have hc2 : c * 2 = 1 := by
    rw [hc, (map_ofNat (algebraMap k A) 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : k) ≠ 0), map_one]
  have hmap : ∀ x : A, x ^ 2 = 1 → IsIdempotentElem (c * (1 + x)) := by
    intro x hx
    unfold IsIdempotentElem
    have : (c * (1 + x)) * (c * (1 + x)) = c * (c * 2) * (1 + x) := by
      linear_combination (c * c) * hx
    rw [this, hc2, mul_one]
  have hinj : Set.InjOn (fun x : A => c * (1 + x)) {x : A | x ^ 2 = 1} := by
    intro x _ y _ hxy
    have h : (2 : A) * (c * (1 + x)) = 2 * (c * (1 + y)) := by simp only at hxy; rw [hxy]
    have e : ∀ z : A, (2 : A) * (c * (1 + z)) = 1 + z := fun z => by
      rw [← mul_assoc, mul_comm (2 : A) c, hc2, one_mul]
    rw [e, e] at h
    exact add_left_cancel h
  have hfin : Set.Finite {e : A | IsIdempotentElem e} :=
    Set.finite_coe_iff.mp (‹Finite {e : A // IsIdempotentElem e}› :)
  exact Set.Finite.of_finite_image (hfin.subset (by
    rintro _ ⟨x, hx, rfl⟩; exact hmap x hx)) hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsLast
section
namespace GlobalTheory.PowerDifferenceNormInertiaEigenvalues

universe u_1

theorem norm_pow_sub_pow_le {C : Type u_1} [NormedField C] [IsUltrametricDist C] {x y : C}
    (hx : ‖x‖ ≤ (1 : ℝ)) (hy : ‖y‖ ≤ (1 : ℝ)) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)

end GlobalTheory.PowerDifferenceNormInertiaEigenvalues
end

