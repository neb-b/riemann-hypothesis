module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolyringOfIntegralClosureRange
section
open MvPolynomial

namespace GlobalTheory

theorem mem_polyring_of_integral_closure_range : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  intro K _ D y hy t ht ι z hz f hf hft
  choose p hp using hz
  set F := Subfield.closure (Set.range y) with hF
  have hsub : ∀ u : K, u ∈ Subring.closure (Set.range y) ↔ ∃ q : MvPolynomial (Fin D) ℤ, aeval y q = u := by
    intro u
    have e1 : u ∈ Subring.closure (Set.range y) ↔ u ∈ Algebra.adjoin ℤ (Set.range y) := by
      rw [Algebra.adjoin_int]; rfl
    rw [e1, Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hmem : ∀ q : MvPolynomial (Fin D) ℤ, aeval y q ∈ F := by
    intro q
    exact Subfield.subring_closure_le _ ((hsub _).mpr ⟨q, rfl⟩)
  let φ : MvPolynomial (Fin D) ℤ →+* F := (aeval y).toRingHom.codRestrict F hmem
  letI : Algebra (MvPolynomial (Fin D) ℤ) F := φ.toAlgebra
  have hφ : ∀ q, ((algebraMap (MvPolynomial (Fin D) ℤ) F q : F) : K) = aeval y q := fun q => rfl
  have hinj : Function.Injective (aeval y : MvPolynomial (Fin D) ℤ →ₐ[ℤ] K) :=
    algebraicIndependent_iff_injective_aeval.mp hy
  haveI : FaithfulSMul (MvPolynomial (Fin D) ℤ) F := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinj
    rw [← hφ a, ← hφ b, h]
  haveI : IsFractionRing (MvPolynomial (Fin D) ℤ) F := by
    refine IsFractionRing.of_field _ _ ?_
    intro w
    obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.mp w.2
    obtain ⟨a, ha⟩ := (hsub u).mp hu
    obtain ⟨b, hb⟩ := (hsub v).mp hv
    refine ⟨a, b, ?_⟩
    apply Subtype.ext
    simp only [Subfield.coe_div, hφ, ha, hb, huv]
  haveI : IsIntegrallyClosed (MvPolynomial (Fin D) ℤ) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hcomp : (aeval y).toRingHom.comp (bind₁ p).toRingHom = (aeval z).toRingHom := by
    refine RingHom.ext fun q => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_bind₁]
    have : (fun i => aeval y (p i)) = z := funext hp
    rw [this]
  let t' : F := ⟨t, ht⟩
  have hint : IsIntegral (MvPolynomial (Fin D) ℤ) t' := by
    refine ⟨f.map (bind₁ p).toRingHom, hf.map _, ?_⟩
    apply Subtype.val_injective
    have h1 := Polynomial.hom_eval₂ (f.map (bind₁ p).toRingHom) (algebraMap (MvPolynomial (Fin D) ℤ) F) F.subtype t'
    show F.subtype (Polynomial.eval₂ _ t' _) = F.subtype 0
    rw [h1, map_zero]
    have h2 : F.subtype.comp (algebraMap (MvPolynomial (Fin D) ℤ) F) = (aeval y).toRingHom := by
      exact RingHom.ext fun q => rfl
    rw [h2, Polynomial.eval₂_map, hcomp]
    exact hft
  obtain ⟨T₀, hT⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨T₀, by rw [← hφ, hT]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfForallAlgHomEq
section
open scoped TensorProduct

namespace GlobalTheory


open Polynomial in
theorem mem_range_of_forall_algHom_eq :
    ∀ (F K₀ : Type) [Field F] [CharZero F] [Field K₀] [Algebra F K₀], Algebra.IsAlgebraic F K₀ →
      ∀ t : K₀, (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (φ₁ φ₂ : K₀ →ₐ[F] Ω), φ₁ t = φ₂ t) →
        t ∈ Set.range (algebraMap F K₀) := by
  intro F K₀ _ _ _ _ halg t ht
  classical
  have hint : IsIntegral F t := (Algebra.IsAlgebraic.isAlgebraic t).isIntegral
  set Ω := AlgebraicClosure K₀
  have hsep : (minpoly F t).Separable := (minpoly.irreducible hint).separable
  have hsplit : Splits ((minpoly F t).map (algebraMap F Ω)) := IsAlgClosed.splits _
  have hcard := card_rootSet_eq_natDegree (K := Ω) hsep hsplit
  by_contra hnot
  have h1 : (minpoly F t).natDegree ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h
    exact hnot ⟨c, hc⟩
  have hpos := minpoly.natDegree_pos hint
  have hlt : 1 < Fintype.card ((minpoly F t).rootSet Ω) := by omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hlt
  have hK' : ∀ s : K₀, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F Ω)) :=
    fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩
  have ha : aeval (a : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp a.2).2
  have hb : aeval (b : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp b.2).2
  obtain ⟨φa, hφa⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' ha
  obtain ⟨φb, hφb⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' hb
  apply hab
  apply Subtype.ext
  rw [← hφa, ← hφb]
  exact ht Ω φa φb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulOfForallCharPowEqOne
section
namespace GlobalTheory

theorem mem_smul_of_forall_char_pow_eq_one
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (k : ℕ) (hk : (k : F) ≠ 0) (d : X)
    (hd : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd d) = 1) :
    ∃ z : X, d = k • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  by_contra hne
  push_neg at hne
  have hex : ∃ i, ¬ (k : ℤ) ∣ b.repr d i := by
    by_contra h
    push_neg at h
    apply hne (∑ i, (b.repr d i / k) • b i)
    apply b.repr.injective
    ext j
    rw [← natCast_zsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.single_apply, Int.mul_ediv_cancel' (h j)]
  obtain ⟨i, hi⟩ := hex
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (by simp)
  haveI : NeZero (k : F) := ⟨hk⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk0
  let u : Fˣ := Units.mk0 ζ hζ0
  have hu : IsPrimitiveRoot u k := IsPrimitiveRoot.coe_units_iff.mp (by simpa [u] using hζ)
  let τ : Multiplicative X →* Fˣ :=
    (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hτ : ∀ x : X, τ (Multiplicative.ofAdd x) = u ^ (b.repr x i) := by
    intro x; simp [τ]
  have hτk : τ ^ k = 1 := by
    ext x
    show (τ x ^ k : Fˣ).val = (1 : Fˣ).val
    congr 1
    rw [← ofAdd_toAdd x, hτ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hu.pow_eq_one, one_zpow]
  have h1 := hd τ hτk
  rw [hτ] at h1
  exact hi ((hu.zpow_eq_one_iff_dvd _).1 h1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbit
section
open Module

namespace GlobalTheory.GenEigenFinOrbit

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem foldr_eq_prod (χ : End ℂ V → ℂ) (zs : List (End ℂ V)) (v : V) :
    zs.foldr (fun z f => z f - χ z • f) v =
      (zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ z))).prod v := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [ih, Module.End.mul_apply]

theorem map_lt_of_pow_eq_zero {N : Submodule ℂ V} (g : End ℂ V) (K : ℕ)
    (hg : N.map g ≤ N) (hK : ∀ n ∈ N, (g ^ K) n = 0) (hN : N ≠ ⊥) : N.map g < N := by
  refine lt_of_le_of_ne hg fun h => hN ?_
  have hk : ∀ k : ℕ, N.map (g ^ k) = N := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih => rw [pow_succ, Module.End.mul_eq_comp, Submodule.map_comp, h, ih]
  rw [← hk K, eq_bot_iff]
  rintro _ ⟨n, hn, rfl⟩
  simp [hK n hn]

section Family
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)

include hst in
theorem map_prod_le (gs : List (End ℂ V)) (hgs : ∀ g ∈ gs, g ∈ G) : N.map gs.prod ≤ N := by
  induction gs with
  | nil => simp [Module.End.one_eq_id]
  | cons g gs ih =>
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp]
    exact (Submodule.map_mono (ih fun x hx => hgs x (by simp [hx]))).trans
      (hst g (hgs g (by simp)))

include hcomm hst hnil in
theorem finrank_map_prod_le [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) :
    finrank ℂ (N.map gs.prod) ≤ finrank ℂ N - gs.length := by
  induction gs with
  | nil => rw [List.prod_nil, Module.End.one_eq_id, Submodule.map_id]; simp
  | cons g gs ih =>
    have hgs' : ∀ x ∈ gs, x ∈ G := fun x hx => hgs x (by simp [hx])
    have hg : g ∈ G := hgs g (by simp)
    specialize ih hgs'
    set M := N.map gs.prod with hM
    have hMN : M ≤ N := map_prod_le G N hst gs hgs'
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMN
    have hc : Commute g gs.prod :=
      Commute.list_prod_right _ _ fun x hx => hcomm g hg x (hgs' x hx)
    have hMst : M.map g ≤ M := by
      rw [hM, ← Submodule.map_comp, ← Module.End.mul_eq_comp, hc.eq, Module.End.mul_eq_comp,
        Submodule.map_comp]
      exact Submodule.map_mono (hst g hg)
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp, ← hM, List.length_cons]
    by_cases h0 : M = ⊥
    · rw [h0, Submodule.map_bot]; simp
    · have hlt := Submodule.finrank_lt_finrank_of_lt
        (map_lt_of_pow_eq_zero g K hMst (fun n hn => hnil g hg n (hMN hn)) h0)
      omega

include hcomm hst hnil in
theorem map_prod_eq_bot [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) (hlen : finrank ℂ N ≤ gs.length) : N.map gs.prod = ⊥ := by
  haveI : FiniteDimensional ℂ (N.map gs.prod) :=
    Submodule.finiteDimensional_of_le (map_prod_le G N hst gs hgs)
  rw [← Submodule.finrank_eq_zero]
  have := finrank_map_prod_le G N K hcomm hst hnil gs hgs
  omega

include hcomm hst hnil in
theorem exists_common_kernel [FiniteDimensional ℂ N] (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ g ∈ G, g n = 0 := by
  classical
  let Pr : ℕ → Prop := fun l => ∃ gs : List (End ℂ V), (∀ g ∈ gs, g ∈ G) ∧ gs.length = l ∧
    N.map gs.prod ≠ ⊥
  have hex : ∃ l, ¬ Pr l := ⟨finrank ℂ N, fun ⟨gs, hgs, hl, hne⟩ =>
    hne (map_prod_eq_bot G N K hcomm hst hnil gs hgs hl.ge)⟩
  have h0 : Pr 0 := ⟨[], by simp, rfl, by simpa [Module.End.one_eq_id] using hN⟩
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exact absurd (h ▸ Nat.find_spec hex) (not_not.2 h0)
    · exact h
  obtain ⟨gs, hgs, hl, hne⟩ : Pr (Nat.find hex - 1) :=
    not_not.1 (Nat.find_min hex (by omega))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨gs.prod n, map_prod_le G N hst gs hgs ⟨n, hn, rfl⟩, hx0, fun g hg => ?_⟩
  by_contra hne'
  apply Nat.find_spec hex
  refine ⟨g :: gs, ?_, by simp [hl]; omega, ?_⟩
  · intro x hx; simp at hx; rcases hx with rfl | hx; exacts [hg, hgs x hx]
  · intro hbot
    apply hne'
    have : (g :: gs).prod n ∈ N.map (g :: gs).prod := ⟨n, hn, rfl⟩
    rw [hbot] at this
    simpa [Module.End.mul_apply] using this

end Family

theorem sub_pow_coe {U : Submodule ℂ V} (z : End ℂ V) (F : End ℂ U)
    (hF : ∀ u : U, (F u : V) = z u) (c : ℂ) (k : ℕ) (u : U) :
    (((F - c • 1) ^ k) u : V) = ((z - algebraMap ℂ (End ℂ V) c) ^ k) (u : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    simp [hF]

end GlobalTheory.GenEigenFinOrbit

namespace GlobalTheory


open GenEigenFinOrbit in
theorem mem_span_genEigen_of_finiteDimensional_orbit :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V),
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) →
    Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D →
    (∀ (χ' : Module.End ℂ V → ℂ) (u : V),
      u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 →
      (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) →
    ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧
      ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) →
        zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  intro V _ _ A hA X' D ψ hfin hD hX
  set U := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) with hU
  have hUst : ∀ z ∈ A, Set.MapsTo z U U := by
    intro z hz
    have : U.map z ≤ U := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨z * w, A.mul_mem hz hw, rfl⟩
    exact fun u hu => this ⟨u, hu, rfl⟩
  have hψU : ψ ∈ U := Submodule.subset_span ⟨1, A.one_mem, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : A → End ℂ U, ∀ (i : A) (u : U), (f i u : V) = (i : End ℂ V) u :=
    ⟨fun i => (i : End ℂ V).restrict (hUst i i.2), fun _ _ => rfl⟩
  have hcommAll : ∀ i j, Commute (f i) (f j) := by
    intro i j
    show f i * f j = f j * f i
    ext u
    have := congrArg (fun T : End ℂ V => T (u : V)) (hA i i.2 j j.2)
    simpa [Module.End.mul_apply, hf] using this
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcommAll i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  set T := {ψ' | ψ' ∈ U ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D →
        (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} with hT
  have key : ∀ χ : A → ℂ, ∀ x ∈ ⨅ i, (f i).maxGenEigenspace (χ i),
      (x : V) ∈ Submodule.span ℂ T := by
    classical
    intro χ x hx
    set N := (⨅ i, (f i).maxGenEigenspace (χ i)).map U.subtype with hNdef
    have hxN : (x : V) ∈ N := ⟨x, hx, rfl⟩
    have hNU : N ≤ U := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNU
    obtain ⟨χ', hχ'⟩ : ∃ χ' : End ℂ V → ℂ, ∀ z (hz : z ∈ A), χ' z = χ ⟨z, hz⟩ :=
      ⟨fun y => if h : y ∈ A then χ ⟨y, h⟩ else 0, fun z hz => dif_pos hz⟩
    set G : Set (End ℂ V) := {g | ∃ z ∈ A, g = z - algebraMap ℂ _ (χ' z)} with hG
    have hGA : ∀ g ∈ G, g ∈ A := by
      rintro _ ⟨z, hz, rfl⟩
      exact A.sub_mem hz (A.algebraMap_mem _)
    have hcommG : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a :=
      fun a ha b hb => hA a (hGA a ha) b (hGA b hb)
    have hNst : ∀ z ∈ A, N.map z ≤ N := by
      rintro z hz _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨f ⟨z, hz⟩ y, ?_, hf ⟨z, hz⟩ y⟩
      simp only [SetLike.mem_coe, Submodule.mem_iInf] at hy ⊢
      intro i
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommAll i ⟨z, hz⟩) (χ i) (hy i)
    have hstG : ∀ g ∈ G, N.map g ≤ N := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
      exact N.sub_mem (hNst z hz ⟨v, hv, rfl⟩) (N.smul_mem _ hv)
    have hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ finrank ℂ U) n = 0 := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
      have hy' := (Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hy) ⟨z, hz⟩
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
        LinearMap.mem_ker] at hy'
      rw [hχ' z hz, Submodule.subtype_apply, ← sub_pow_coe z (f ⟨z, hz⟩) (hf ⟨z, hz⟩), hy']
      rfl
    by_cases hN : N = ⊥
    · rw [hN, Submodule.mem_bot] at hxN
      rw [hxN]
      exact zero_mem _
    obtain ⟨n, hnN, hn0, hnker⟩ := exists_common_kernel G N (finrank ℂ U) hcommG hstG hnil hN
    have heig : ∀ z ∈ A, z n = χ' z • n := by
      intro z hz
      have := hnker _ ⟨z, hz, rfl⟩
      simpa [sub_eq_zero] using this
    obtain ⟨χ0, hχ0X, hχ0⟩ := hX χ' n (hNU hnN) hn0 heig
    apply Submodule.subset_span
    refine ⟨hNU hxN, χ0, hχ0X, fun zs hlen hzs => ?_⟩
    rw [foldr_eq_prod]
    have hmap : zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ0 z)) =
        zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ' z)) :=
      List.map_congr_left fun z hz => by rw [hχ0 z (hzs z hz)]
    rw [hmap]
    have hbot := map_prod_eq_bot G N (finrank ℂ U) hcommG hstG hnil
      (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z))
      (by
        intro g hg
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
        exact ⟨z, hzs z hz, rfl⟩)
      (by rw [List.length_map, hlen]; exact (Submodule.finrank_mono hNU).trans hD)
    have hmem : (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod (x : V) ∈
        N.map (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod := ⟨_, hxN, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hmem : (⟨ψ, hψU⟩ : U) ∈ ⨆ χ : A → ℂ, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun x : U => (x : V) ∈ Submodule.span ℂ T) hmem key
    (by simp) (fun x y hx hy => by simpa using add_mem hx hy)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMem
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem kerCotangentToTensor_injective_of_formallySmooth (k R F : Type*) [CommRing k] [CommRing R]
    [CommRing F] [Algebra k R] [Algebra k F] [Algebra R F] [IsScalarTower k R F]
    [Algebra.FormallySmooth k F] (hs : Function.Surjective (algebraMap R F)) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R F) := by
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom k R F).kerSquareLift :=
    fun x ↦ by
      obtain ⟨y, rfl⟩ := hs x
      exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hnil : RingHom.ker (IsScalarTower.toAlgHom k R F).kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := k) hs).symm
    ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k F) _ hsurj ⟨2, hnil⟩⟩
  exact Function.LeftInverse.injective (g := l) fun x ↦ congr($hl x)

theorem mem_sq_localization_of_pderiv_mem :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  intro Λ _ _ _ σ _ Q _ hQ x hx hd
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  let R := Localization.AtPrime Q
  let F := ResidueField R
  let k := FractionRing Λ
  have hunit : ∀ a : nonZeroDivisors Λ, IsUnit (algebraMap Λ R a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply Λ (MvPolynomial σ Λ) R]
    exact IsLocalization.map_units R (M := Q.primeCompl)
      ⟨MvPolynomial.C a.1, fun h => nonZeroDivisors.coe_ne_zero a (hQ _ h)⟩
  letI : Algebra k R := (IsLocalization.lift (M := nonZeroDivisors Λ) (S := k) hunit).toAlgebra
  haveI : IsScalarTower Λ k R := IsScalarTower.of_algebraMap_eq
    (fun a => (IsLocalization.lift_eq (M := nonZeroDivisors Λ) (S := k) hunit a).symm)
  letI : Algebra k F := ((algebraMap R F).comp (algebraMap k R)).toAlgebra
  haveI : IsScalarTower k R F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ k F := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply Λ R F, IsScalarTower.algebraMap_apply Λ k R]; rfl)
  haveI : Algebra.EssFiniteType (MvPolynomial σ Λ) R := .of_isLocalization R Q.primeCompl
  haveI : Algebra.EssFiniteType Λ R := .comp Λ (MvPolynomial σ Λ) R
  haveI : Algebra.EssFiniteType R F := .of_surjective (Algebra.ofId R F) residue_surjective
  haveI : Algebra.EssFiniteType Λ F := .comp Λ R F
  haveI : Algebra.EssFiniteType k F := Algebra.EssFiniteType.of_comp Λ k F
  haveI : Algebra.FormallySmooth k F := Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.FormallySmooth Λ k := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors Λ)
  haveI : Algebra.FormallySmooth Λ F := Algebra.FormallySmooth.comp Λ k F
  have hinj := kerCotangentToTensor_injective_of_formallySmooth Λ R F (residue_surjective)
  have hker : RingHom.ker (algebraMap R F) = maximalIdeal R := ker_residue
  have hmem : ∀ p ∈ Q, algebraMap (MvPolynomial σ Λ) R p ∈ RingHom.ker (algebraMap R F) := by
    intro p hp
    rw [hker]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q p).mpr hp
  have hym := hmem x hx
  have hD : KaehlerDifferential.D Λ (MvPolynomial σ Λ) x =
      ∑ s, MvPolynomial.pderiv s x • KaehlerDifferential.D Λ (MvPolynomial σ Λ) (MvPolynomial.X s) := by
    conv_lhs => rw [← (KaehlerDifferential.mvPolynomialBasis Λ σ).sum_repr (KaehlerDifferential.D Λ _ x)]
    simp [KaehlerDifferential.mvPolynomialBasis_repr_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  have h0 : KaehlerDifferential.kerCotangentToTensor Λ R F
      ((RingHom.ker (algebraMap R F)).toCotangent ⟨_, hym⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← KaehlerDifferential.map_D Λ Λ (MvPolynomial σ Λ) R, hD, map_sum, tmul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [LinearMap.map_smul_of_tower, ← algebraMap_smul R, ← smul_tmul, Algebra.smul_def, mul_one,
      RingHom.mem_ker.mp (hmem _ (hd s)), zero_tmul]
  have h2 : algebraMap (MvPolynomial σ Λ) R x ∈ RingHom.ker (algebraMap R F) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h2
  obtain ⟨m, hm, hmx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := R) _ _).mp h2
  exact ⟨m, hm, hmx⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialTensorBaseChangeRingEquiv
section
open IsLocalRing TensorProduct

namespace GlobalTheory

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_tensor_baseChange_ringEquiv :
    ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K]
      [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K],
      Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  intro S B K τ _ _ _ _ _ _ _
  let e : MvPolynomial τ S ⊗[S] B ≃ₐ[MvPolynomial τ S] MvPolynomial τ B :=
    Algebra.IsPushout.equiv S (MvPolynomial τ S) B (MvPolynomial τ B)
  exact ⟨(Algebra.TensorProduct.comm (MvPolynomial τ S) (MvPolynomial τ B) K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[MvPolynomial τ S] K) e.symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange S (MvPolynomial τ S) (MvPolynomial τ S) K B).toRingEquiv.trans
        (Algebra.TensorProduct.comm S K B).toRingEquiv))⟩

end GlobalTheory
end

