module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableUnderOperators
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf30.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qf30.Umon.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) ↦
      Submonoid.closure (Set.range fun (ab : Fin n × Fin n) ↦ E ab.1 ab.2)

noncomputable def UpperTheory.Reformulated.B.Qf30.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qf30.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qf30.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qf30.isoSub.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (lam : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qf30.Umon E, ∃ (v : V), UpperTheory.Reformulated.B.Qf30.IsHWV E lam v ∧ x = (u : V → V) v}

theorem UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  unfold UpperTheory.Reformulated.B.Qf30.isoSub at hx ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨u, hu, v, hv, rfl⟩
    refine Submodule.subset_span ⟨E a b * u, ?_, v, hv, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ c hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Iwa
section
noncomputable def UpperTheory.Reformulated.B.DYhc7.Iwa :
    {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → Prop :=
    fun {G : Type} [Group G] (P K : Subgroup G) ↦ ∀ (g : G), ∃ p ∈ P, ∃ k ∈ K, g = p * k

theorem UpperTheory.Reformulated.B.DYhc7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {K P : Subgroup G},
      IsCompact (↑K : Set G) →
        IsClosed (↑P : Set G) →
          UpperTheory.Reformulated.B.DYhc7.Iwa P K → Topology.IsQuotientMap fun (x : ↥P × ↥K) ↦ (↑x.1 : G) * (↑x.2 : G) := by
  intro G _ _ _ K P hK hP hI
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let h : G × K ≃ₜ G × K :=
    { toFun := fun y => (y.1 * (y.2 : G), y.2)
      invFun := fun y => (y.1 * (y.2 : G)⁻¹, y.2)
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hι : Topology.IsClosedEmbedding (Prod.map (Subtype.val : P → G) (id : K → K)) :=
    hP.isClosedEmbedding_subtypeVal.prodMap Topology.IsClosedEmbedding.id
  have hcl : IsClosedMap (fun x : ↥P × ↥K ↦ (x.1 : G) * (x.2 : G)) := by
    have h1 : IsClosedMap (Prod.fst : G × K → G) := isClosedMap_fst_of_compactSpace
    exact h1.comp (h.isClosedMap.comp hι.isClosedMap)
  refine hcl.isQuotientMap (by fun_prop) ?_
  intro g
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IwahoriEntryBound
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

noncomputable def UpperTheory.Reformulated.B.IwahoriEntryBound.latK :
    (L : Type) → [inst : Field L] → [Valued L (WithZero (Multiplicative ℤ))] → (n : ℕ) → ℕ → Set (Fin n → L) :=
    fun (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n k : ℕ) ↦
      {x : Fin n → L |
        ∀ (i : Fin n),
          if (↑i : ℕ) < k then (Valued.v : L → WithZero (Multiplicative ℤ)) (x i) ≤ (1 : WithZero (Multiplicative ℤ))
          else (Valued.v : L → WithZero (Multiplicative ℤ)) (x i) < (1 : WithZero (Multiplicative ℤ))}

noncomputable def UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL :
    (L : Type) → [inst : Field L] → [Valued L (WithZero (Multiplicative ℤ))] → (n : ℕ) → Subgroup (GL (Fin n) L) :=
    fun (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) ↦
      ⨅ (k : Fin (n + (1 : ℕ))),
        Subgroup.comap Matrix.GeneralLinearGroup.toLin.toMonoidHom
          (MulAction.stabilizer (LinearMap.GeneralLinearGroup L (Fin n → L)) (UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n (↑k : ℕ)))

namespace UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers

private lemma entry_bound {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {h : GL (Fin n) L} (hh : h ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n) (i j : Fin n) :
    (Valued.v ((h : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
    ((j : ℕ) < (i : ℕ) → Valued.v ((h : Matrix (Fin n) (Fin n) L) i j) < 1) := by
  classical
  have hk := (Subgroup.mem_iInf.mp hh) ⟨(j : ℕ) + 1, by omega⟩
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
  have hx : (Pi.single j (1 : L) : Fin n → L) ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1) := by
    intro t
    by_cases ht : t = j
    · subst ht
      simp
    · have : Pi.single (M := fun _ => L) j (1 : L) t = 0 := Pi.single_eq_of_ne ht _
      split_ifs <;> simp [this]
  have hy := Set.smul_mem_smul_set (a := (Matrix.GeneralLinearGroup.toLin.toMonoidHom h)) hx
  have hk' : Matrix.GeneralLinearGroup.toLin.toMonoidHom h • UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1)
      = UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n ((j : ℕ) + 1) := hk
  rw [hk'] at hy
  have key : (Matrix.GeneralLinearGroup.toLin.toMonoidHom h) • (Pi.single j (1 : L) : Fin n → L)
      = (h : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1 := by
    rfl
  rw [key] at hy
  have e : ((h : Matrix (Fin n) (Fin n) L) *ᵥ Pi.single j 1) i = (h : Matrix (Fin n) (Fin n) L) i j := by
    simp [Matrix.mulVec_single_one]
  have hi := hy i
  rw [e] at hi
  constructor
  · split_ifs at hi with hc
    · exact hi
    · exact hi.le
  · intro hlt
    rw [if_neg (by omega)] at hi
    exact hi

end UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers

open UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers in
theorem UpperTheory.Reformulated.B.IwahoriEntryBound.main :
    ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {g : GL (Fin n) L},
      g ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n →
        ∀ (i : Fin n),
          (Valued.v : L → WithZero (Multiplicative ℤ)) ((↑g : Matrix (Fin n) (Fin n) L) i i) =
            (1 : WithZero (Multiplicative ℤ)) := by
  intro L _ _ n g hg i
  classical
  have hg' : g⁻¹ ∈ UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL L n := inv_mem hg
  have hprod : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hii := congrFun (congrFun hprod i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hii
  set a := ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * (g : Matrix (Fin n) (Fin n) L) i i with ha
  have hrest : Valued.v (∑ j ∈ Finset.univ.erase i,
      ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (g : Matrix (Fin n) (Fin n) L) j i) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Valuation.map_mul]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    ·
      have h1 := (entry_bound hg' i j).2 hlt
      have h2 := (entry_bound hg j i).1
      calc _ ≤ Valued.v (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) * 1 := by gcongr
        _ = _ := mul_one _
        _ < 1 := h1
    · have h1 := (entry_bound hg' i j).1
      have h2 := (entry_bound hg j i).2 hlt
      calc _ ≤ 1 * Valued.v ((g : Matrix (Fin n) (Fin n) L) j i) := by gcongr
        _ = _ := one_mul _
        _ < 1 := h2
  have hva : 1 ≤ Valued.v a := by
    by_contra hc
    push Not at hc
    have := Valuation.map_add_lt _ hc hrest
    rw [hii, Valuation.map_one] at this
    exact lt_irrefl _ this
  have hgi := (entry_bound hg i i).1
  have hinv := (entry_bound hg' i i).1
  apply le_antisymm hgi
  calc (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v a := hva
    _ = _ := Valuation.map_mul _ _ _
    _ ≤ 1 * Valued.v ((g : Matrix (Fin n) (Fin n) L) i i) := by gcongr
    _ = _ := one_mul _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KeyLemmaStatement
section
namespace CoprimeTimesDvdPowFactorization

private theorem key (g m : ℕ) (hm : 0 < m) :
    (m / Nat.gcd m (g ^ m)).Coprime g := by
  set d := Nat.gcd m (g ^ m) with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hm
  have hcop : (m / d).Coprime (g ^ m / d) := Nat.coprime_div_gcd_div_gcd hdpos
  apply Nat.coprime_of_dvd
  intro p hp hpc hpg
  have hpn : ¬ p ∣ g ^ m / d := by
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpc hcop) h
  have hdg : d ∣ g ^ m := Nat.gcd_dvd_right _ _
  have hdm : d ∣ m := Nat.gcd_dvd_left _ _
  have hpm : p ^ m ∣ d * (g ^ m / d) := by
    rw [Nat.mul_div_cancel' hdg]
    exact pow_dvd_pow_of_dvd hpg m
  have hcp : Nat.Coprime (p ^ m) (g ^ m / d) :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
  have hpd : p ^ m ∣ d := hcp.dvd_of_dvd_mul_right hpm
  have hall : p ^ m * p ∣ d * (m / d) := Nat.mul_dvd_mul hpd hpc
  rw [Nat.mul_div_cancel' hdm, ← pow_succ] at hall
  have hle : p ^ (m + 1) ≤ m := Nat.le_of_dvd hm hall
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
  have h3 : p ^ m ≤ p ^ (m + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ m)
  omega

end CoprimeTimesDvdPowFactorization

theorem UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main :
    ∀ (g m : ℕ),
    (0 : ℕ) < m → ∃ (c : ℕ) (d : ℕ), m = c * d ∧ c.Coprime g ∧ d ∣ g ^ m := by
  intro g m hm
  refine ⟨m / Nat.gcd m (g ^ m), Nat.gcd m (g ^ m), ?_, CoprimeTimesDvdPowFactorization.key g m hm, Nat.gcd_dvd_right _ _⟩
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Lam0
section
open TensorProduct in
theorem UpperTheory.Reformulated.B.Qf1.lam0 :
    ∀ (O B M : Type) [inst : CommRing O] [IsDomain O] [inst_2 : CommRing B] [inst_3 : Algebra O B]
    [inst_4 : AddCommGroup M] [inst_5 : _root_.Module B M] [Module.Finite B M] (x : B →ₐ[O] O),
    Module.annihilator B M ≤ RingHom.ker x →
      ∃ (lam : M →+ O) (m₀ : M),
        (∀ (a : B) (m : M), (lam : M → O) (a • m) = (x : B → O) a * (lam : M → O) m) ∧ (lam : M → O) m₀ ≠ (0 : O) := by
  intro O B M _ _ _ _ _ _ _ x hx
  classical
  set p : Ideal B := RingHom.ker x with hp
  haveI hpp : p.IsPrime := RingHom.ker_isPrime x
  have hs : (⟨p, hpp⟩ : PrimeSpectrum B) ∈ Module.support B M :=
    Module.mem_support_iff_of_finite.mpr hx
  have hnt : Nontrivial (p.ResidueField ⊗[B] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct (⟨p, hpp⟩ : PrimeSpectrum B)).mp hs
  obtain ⟨v, hv⟩ := exists_ne (0 : p.ResidueField ⊗[B] M)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero p.ResidueField hv
  let g : M →ₗ[B] p.ResidueField :=
    (f.restrictScalars B) ∘ₗ (TensorProduct.mk B p.ResidueField M 1)
  have hg : ∃ m₀, g m₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    have : ∀ w, f w = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb]
      | tmul k m =>
        have h1 : k ⊗ₜ[B] m = k • ((1 : p.ResidueField) ⊗ₜ[B] m) := by
          simp [TensorProduct.smul_tmul']
        have h2 : f ((1 : p.ResidueField) ⊗ₜ[B] m) = 0 := h m
        rw [h1, map_smul, h2, smul_zero]
    exact this v
  obtain ⟨m₀, hm₀⟩ := hg
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := M)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (B ⧸ p)) S
    (fun m => g m)
  let i : (B ⧸ p) →ₗ[B] p.ResidueField := (IsScalarTower.toAlgHom B (B ⧸ p) p.ResidueField).toLinearMap
  have hi : Function.Injective i := IsFractionRing.injective (B ⧸ p) p.ResidueField
  let c : p.ResidueField := algebraMap (B ⧸ p) p.ResidueField b
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let g' : M →ₗ[B] p.ResidueField := c • g
  have hr : ∀ m, g' m ∈ LinearMap.range i := by
    intro m
    have hm : m ∈ Submodule.span B (S : Set M) := hS ▸ Submodule.mem_top
    have : Submodule.span B (S : Set M) ≤ (LinearMap.range i).comap g' := by
      rw [Submodule.span_le]
      intro y hy
      obtain ⟨z, hz⟩ := hb y hy
      refine ⟨z, ?_⟩
      change algebraMap _ _ z = c * g y
      rw [hz, Algebra.smul_def]
    exact this hm
  let h : M →ₗ[B] (B ⧸ p) := LinearMap.codRestrictOfInjective g' i hi hr
  have hh : ∀ m, i (h m) = g' m := fun m =>
    LinearMap.codRestrictOfInjective_comp_apply g' i hi hr m
  let e : (B ⧸ p) →+* O := RingHom.kerLift (x : B →+* O)
  have he : Function.Injective e := RingHom.kerLift_injective (x : B →+* O)
  refine ⟨e.toAddMonoidHom.comp h.toAddMonoidHom, m₀, ?_, ?_⟩
  · intro a m
    change e (h (a • m)) = x a * e (h m)
    rw [map_smul, Algebra.smul_def, map_mul]
    rfl
  · change e (h m₀) ≠ 0
    intro h0
    have h1 : h m₀ = 0 := he (by rw [h0, map_zero])
    have h2 := hh m₀
    rw [h1, map_zero] at h2
    exact mul_ne_zero hc hm₀ h2.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LaurentCharacterLambda
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ), IsUnit (↑q : S) → IsUnit ((Int.castRingHom S : ℤ → S) (↑q : ℤ)) := by
  intro S _ q hq
  rwa [map_natCast]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.lam :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → Localization.Away (↑q : ℤ) →+* S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      IsLocalization.Away.lift (↑q : ℤ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 q hq)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tU :
    (S : Type) → [inst : CommRing S] → (LaurentPolynomial S)ˣ :=
    fun (S : Type) [CommRing S] ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 S,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 S : (LaurentPolynomial S)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.iot :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* LaurentPolynomial S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.lam q hq)) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tU S)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 :
    ∀ (q : ℕ), LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 _

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one :
    ∀ (q : ℕ), LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 _

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tR :
    (q : ℕ) → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ :=
    fun (q : ℕ) ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 q,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one q : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.chi :
    {S : Type} →
      [inst : CommRing S] →
        (q : ℕ) →
          {R : Type} → [inst_1 : CommRing R] → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) → (S →+* R) → LaurentPolynomial S →+* R :=
    fun {S : Type} [CommRing S] (q : ℕ) {R : Type} [CommRing R] (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) ↦
      LaurentPolynomial.eval₂ ψ
        ((Units.map (↑φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →* R) : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ → Rˣ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tR q))

private theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext {S R : Type} [CommRing S] [CommRing R]
    (f g : LaurentPolynomial S →+* R)
    (hC : ∀ a : S, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial S))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.chi_uniq :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) {R : Type} [inst_1 : CommRing R]
      (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) (χ : LaurentPolynomial S →+* R),
      χ.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq) = φ → χ.comp LaurentPolynomial.C = ψ → χ = UpperTheory.Reformulated.B.LaurentCharacterLambda.chi q φ ψ := by
  intro S _ q hq R _ φ ψ χ h1 h2
  apply UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext
  · intro a
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_C, ← h2, RingHom.comp_apply]
  · rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_T, zpow_one, Units.coe_map, ← h1]
    change _ = χ (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq (LaurentPolynomial.T 1))
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.iot, LaurentPolynomial.eval₂_T, zpow_one]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeIffLtColH
section
noncomputable def UpperTheory.Reformulated.B.Qk46.colH :
    {n : Nat} → (Fin n → Int) → Int → Nat :=
    fun {n : Nat} (mu : Fin n → Int) (c : Int) ↦ @Finset.card (Fin n) {m : Fin n | @LE.le Int Int.instLEInt c (mu m)}

theorem UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH :
    ∀ {r : Nat} {μ : Fin r → Int},
      @Antitone (Fin r) Int (@PartialOrder.toPreorder (Fin r) (@Fin.instPartialOrder r))
          (@PartialOrder.toPreorder Int
            (@ConditionallyCompletePartialOrderSup.toPartialOrder Int
              (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup Int
                (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder Int
                  (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Int
                    Int.instConditionallyCompleteLinearOrder)))))
          μ →
        ∀ (c : Int) (m : Fin r),
          Iff (@LE.le Int Int.instLEInt c (μ m)) (@LT.lt Nat instLTNat (@Fin.val r m) (@UpperTheory.Reformulated.B.Qk46.colH r μ c)) := by
  intro r μ h c m
  unfold UpperTheory.Reformulated.B.Qk46.colH
  exact (Tuple.lt_card_ge_iff_apply_ge_of_antitone h).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeOfAddOneLeSucc
section
theorem UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ :
    ∀ {a : WithBot ℕ∞} {k : ℕ},
    a + (1 : WithBot ℕ∞) ≤ (↑(k + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑k : WithBot ℕ∞) := by
  intro a k h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      rw [top_add, top_le_iff] at h1
      exact ENat.coe_ne_top _ h1
    | coe n =>
      have h1 : ((n : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      have h2 : n + 1 ≤ k + 1 := by exact_mod_cast h1
      have h3 : (n : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (Nat.le_of_succ_le_succ h2)
      exact WithBot.coe_le_coe.mpr h3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ListEig
section
theorem UpperTheory.Reformulated.B.Qk12.list_eig :
    ∀ {M ι : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] (L : ι → Module.End ℂ M) (c : ι → ℂ) (x : M) (l : List ι),
    (∀ i ∈ l, (L i : M → M) x = c i • x) → ((List.map L l).prod : M → M) x = (List.map c l).prod • x := by
  intro M ι _ _ L c x l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    have h1 : L a x = c a • x := h a List.mem_cons_self
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, h2,
      map_smul, h1, smul_smul, mul_comm]
end

