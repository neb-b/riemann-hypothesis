module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsPrimeDimOneAvoiding
section
namespace PositivityTheory.Xgn.PrimeOfDimensionOne

open IsLocalRing

theorem dim_eq_one (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    (f : B) (hf : f ≠ 0) (hm : f ∈ maximalIdeal B)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → f ∈ Q) : ringKrullDim B = 1 := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {f})
  have hcover : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ P ∈ (↑hfin.toFinset : Set (Ideal B)), (id P : Set B) := by
    intro g hg
    simp only [Set.mem_iUnion, Set.Finite.coe_toFinset, id, SetLike.mem_coe, exists_prop]
    have hne : Ideal.span {g} ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal g).1 hg)
    obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes hne
    have hQp := hQ.1.1
    have hgQ : g ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self g)
    by_cases hg0 : g = 0
    · obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes
        (Ideal.span_singleton_ne_top ((mem_maximalIdeal f).1 hm))
      exact ⟨P, hP, hg0 ▸ P.zero_mem⟩
    have hQ0 : Q ≠ ⊥ := fun hb => hg0 (by rw [hb] at hgQ; exact (Submodule.mem_bot B).1 hgQ)
    have hfQ : Ideal.span {f} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).2 (h Q hQp hQ0)
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hfQ
    have hPp := hP.1.1
    have hP0 : P ≠ ⊥ := fun hb => hf (by
      have := hP.1.2 (Ideal.mem_span_singleton_self f)
      rw [hb] at this
      exact (Submodule.mem_bot B).1 this)
    have hQ1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) Q hQ
    have hPeq : P = Q := by
      by_contra hne'
      have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPQ hne')
      have h1 : 1 ≤ P.height := Order.one_le_iff_ne_zero.2 (fun h0 => hP0 (Ideal.height_eq_zero_iff_eq_bot.1 h0))
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := (by gcongr : (1 : ℕ∞) + 1 ≤ P.height + 1).trans (hlt.trans hQ1)
      norm_num at h2
    exact ⟨P, hP, hPeq ▸ hgQ⟩
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun P hP _ _ =>
    ((Set.Finite.mem_toFinset hfin).1 hP).1.1)).1 hcover
  have hPmem := (Set.Finite.mem_toFinset hfin).1 hP
  have hPp := hPmem.1.1
  have hPm : P = maximalIdeal B := le_antisymm (le_maximalIdeal hPp.ne_top) hmP
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) P hPmem
  have hge : 1 ≤ (maximalIdeal B).height := Order.one_le_iff_ne_zero.2 (fun h0 =>
    hf ((Submodule.mem_bot B).1 (Ideal.height_eq_zero_iff_eq_bot.1 h0 ▸ hm)))
  rw [le_antisymm (hPm ▸ hle) hge]
  rfl

theorem of_mem (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ≠ 0) (hm : f ∈ maximalIdeal A) :
    ∃ P : Ideal A, P.IsPrime ∧ f ∉ P ∧ ringKrullDim (A ⧸ P) = 1 := by
  obtain ⟨P, ⟨hPp, hfP⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 inferInstance
    {P : Ideal A | P.IsPrime ∧ f ∉ P}
    ⟨⊥, Ideal.isPrime_bot, fun h => hf ((Submodule.mem_bot A).1 h)⟩
  refine ⟨P, hPp, hfP, ?_⟩
  have := hPp
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  refine dim_eq_one (A ⧸ P) (Ideal.Quotient.mk P f)
    (fun h0 => hfP (Ideal.Quotient.eq_zero_iff_mem.1 h0)) ?_ ?_
  · refine (mem_maximalIdeal _).2 fun hu => ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ P)ˣ).val
    have h1 : Ideal.Quotient.mk P (f * y - 1) = 0 := by
      rw [map_sub, map_mul, hy, map_one, sub_eq_zero]
      exact hu.mul_val_inv
    have h2 : f * y - 1 ∈ maximalIdeal A :=
      le_maximalIdeal hPp.ne_top (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have h3 : (1 : A) ∈ maximalIdeal A := by
      simpa using sub_mem ((maximalIdeal A).mul_mem_right y hm) h2
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · intro Q hQ hQ0
    by_contra hfQ
    refine hmax (Q.comap (Ideal.Quotient.mk P)) ⟨Ideal.comap_isPrime _ _, hfQ⟩
      (lt_of_le_of_ne (fun a ha => ?_) fun hPQ => hQ0 ?_)
    · show Ideal.Quotient.mk P a ∈ Q
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact Q.zero_mem
    · rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hPQ,
        Ideal.map_quotient_self]

end PositivityTheory.Xgn.PrimeOfDimensionOne

theorem PositivityTheory.Xgn.exists_prime_dim_one_avoiding : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (f : A), f ≠ 0 → ¬ IsField A → ∃ P : Ideal A, P.IsPrime ∧ f ∉ P ∧ ringKrullDim (A ⧸ P) = 1 := by
  intro A _ _ _ _ f hf hA
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    fun h => hA (IsLocalRing.isField_iff_maximalIdeal_eq.2 h)
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hP, hfgP, hdim⟩ := PositivityTheory.Xgn.PrimeOfDimensionOne.of_mem A (f * g) (mul_ne_zero hf hg0)
    ((IsLocalRing.maximalIdeal A).mul_mem_left f hg)
  exact ⟨P, hP, fun hfP => hfgP (P.mul_mem_right g hfP), hdim⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FreeModuleNakayamaDescent
section
open NumberField

namespace PositivityTheory.Xgn.FreeNakayamaDescent
open TensorProduct Module

theorem descent (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S]
    [Finite (MaximalSpectrum A)] [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (b : Basis (Fin r) S (S ⊗[A] M)) : Nonempty (Basis (Fin r) A M) := by
  haveI : Module.Free S (S ⊗[A] M) := Module.Free.of_basis b
  haveI : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M S
  have hrk : ∀ p : PrimeSpectrum A, rankAtStalk M p = r := by
    intro p
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := S) p
    haveI : Nontrivial S := q.nontrivial
    rw [← rankAtStalk_baseChange, rankAtStalk_eq_finrank_of_free]
    simp [finrank_eq_card_basis b]
  apply nonempty_basis_of_flat_of_finrank_eq A M r
  intro P
  haveI := P.2
  letI := Ideal.Quotient.field P.1
  have h := rankAtStalk_baseChange (R := A) (M := M) (S := A ⧸ P.1) ⟨⊥, Ideal.isPrime_bot⟩
  rw [hrk, rankAtStalk_eq_finrank_of_free] at h
  simpa using h

theorem basis_of_tower (k S T ι : Type) [Field k] [CommRing S] [Algebra k S] [AddCommGroup T]
    [Module k T] [Module S T] [IsScalarTower k S T] [Fintype ι] (c : Basis ι k S) (r : ℕ)
    (y : Fin r → T) (hli : LinearIndependent k (fun q : Fin r × ι => c q.2 • y q.1))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) = ⊤) :
    Nonempty (Basis (Fin r) S T) := by
  refine ⟨Basis.mk (v := y) ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg j
    have := hli (fun q => c.repr (g q.1) q.2) (by
      rw [Fintype.sum_prod_type, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_rhs => rw [← c.sum_repr (g j), Finset.sum_smul]
      simp only [smul_assoc])
    apply c.repr.injective
    ext i
    simpa using this (j, i)
  · intro t _
    have ht : t ∈ Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) := by
      rw [hsp]; trivial
    have hle : Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) ≤
        (Submodule.span S (Set.range y)).restrictScalars k := by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact Submodule.smul_mem (Submodule.span S (Set.range y)) (c q.2)
        (Submodule.subset_span (Set.mem_range_self q.1))
    exact hle ht

theorem abstract_descent (F k A S M N ι : Type) [Field F] [Field k] [CommRing A] [CommRing S]
    [Algebra F k] [Algebra F A] [Algebra F S] [Algebra k S] [Algebra A S]
    [IsScalarTower F k S] [IsScalarTower F A S] [Algebra.IsPushout F k A S]
    [Module.FaithfullyFlat A S]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M] [Module.Finite F M]
    [AddCommGroup N] [Module k N] [Fintype ι] (b : Basis ι F A)
    (e : k ⊗[F] M ≃ₗ[k] N) (act : ι → N →ₗ[k] N)
    (hact : ∀ i m, act i (e (1 ⊗ₜ m)) = e (1 ⊗ₜ (b i • m))) (r : ℕ) (x : Fin r → N)
    (hli : LinearIndependent k (fun q : Fin r × ι => act q.2 (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι => act q.2 (x q.1)) = ⊤) :
    ∃ x0 : Fin r → M, LinearIndependent F (fun q : Fin r × ι => b q.2 • x0 q.1) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => b q.2 • x0 q.1) = ⊤ := by
  haveI : Module.Finite F A := Module.Finite.of_basis b
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M
  have ibc : IsBaseChange k (IsScalarTower.toAlgHom F A S).toLinearMap := Algebra.IsPushout.out
  let c : Basis ι k S := ibc.basis b
  have hc : ∀ i, c i = algebraMap A S (b i) := fun i => ibc.basis_apply b i
  let g : S ⊗[A] M ≃ₗ[k] N := (Algebra.IsPushout.cancelBaseChange F k A S M).trans e
  have hg : ∀ i (n : N), g.symm (act i n) = c i • g.symm n := by
    intro i n
    obtain ⟨t, rfl⟩ := e.surjective n
    induction t with
    | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]
    | tmul s m =>
      have h1 : (s ⊗ₜ[F] m : k ⊗[F] M) = s • (1 ⊗ₜ[F] m) := by simp [smul_tmul']
      rw [h1, map_smul, map_smul, hact, map_smul, map_smul, smul_comm, hc]
      congr 1
      simp [g, smul_tmul', ← smul_tmul, Algebra.smul_def]
  obtain ⟨bS⟩ := basis_of_tower k S (S ⊗[A] M) ι c r (fun j => g.symm (x j))
    (by
      have := hli.map' g.symm.toLinearMap g.symm.ker
      have h2 : (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) =
          g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1)) := by
        funext q
        simp [hg]
      rw [h2]
      exact this)
    (by
      have : (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) =
          g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1)) := by
        funext q
        simp [hg]
      rw [this, Set.range_comp, ← Submodule.map_span, hsp, Submodule.map_top]
      exact g.symm.range)
  obtain ⟨bA⟩ := descent A S M r bS
  refine ⟨bA, ?_⟩
  have : (fun q : Fin r × ι => b q.2 • bA q.1) = b.smulTower' bA := by
    funext q
    exact (Basis.smulTower'_apply b bA q).symm
  rw [this]
  exact ⟨Basis.linearIndependent _, Basis.span_eq _⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem matrix_descent (F k A n ι : Type) [Field F] [Field k] [CommRing A]
    [Algebra F k] [Algebra F A] [Fintype n] [DecidableEq n] [Fintype ι] (b : Basis ι F A)
    (φ : A →ₐ[F] Matrix n n F) (r : ℕ) (x : Fin r → n → k)
    (hli : LinearIndependent k
      (fun q : Fin r × ι => ((φ (b q.2)).map (algebraMap F k)).mulVec (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι =>
      ((φ (b q.2)).map (algebraMap F k)).mulVec (x q.1)) = ⊤) :
    ∃ x0 : Fin r → n → F, LinearIndependent F (fun q : Fin r × ι => (φ (b q.2)).mulVec (x0 q.1)) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => (φ (b q.2)).mulVec (x0 q.1)) = ⊤ := by
  letI : Module A (n → F) := Module.compHom (n → F) φ.toRingHom
  have hs : ∀ (a : A) (m : n → F), a • m = (φ a).mulVec m := fun _ _ => rfl
  haveI : IsScalarTower F A (n → F) := ⟨fun c a m => by
    rw [hs, hs, map_smul, Matrix.smul_mulVec]⟩
  haveI : Algebra.IsPushout F k A (A ⊗[F] k) := Algebra.IsPushout.symm inferInstance
  exact abstract_descent F k A (A ⊗[F] k) (n → F) (n → k) ι b
    (TensorProduct.piScalarRight F k k n)
    (fun i => ((φ (b i)).map (algebraMap F k)).mulVecLin)
    (by
      intro i m
      funext a
      simp [hs, Matrix.mulVec, dotProduct, Algebra.smul_def]) r x hli hsp

theorem int_descent (F k O n ι : Type) [Field F] [Field k] [CommRing O]
    [Algebra F k] [Fintype n] [DecidableEq n] [Fintype ι] (β : Basis ι ℤ O)
    (ρ : O →+* Matrix n n F) (r : ℕ) (x : Fin r → n → k)
    (hli : LinearIndependent k
      (fun q : Fin r × ι => ((ρ (β q.2)).map (algebraMap F k)).mulVec (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι =>
      ((ρ (β q.2)).map (algebraMap F k)).mulVec (x q.1)) = ⊤) :
    ∃ x0 : Fin r → n → F, LinearIndependent F (fun q : Fin r × ι => (ρ (β q.2)).mulVec (x0 q.1)) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => (ρ (β q.2)).mulVec (x0 q.1)) = ⊤ := by
  let φ : F ⊗[ℤ] O →ₐ[F] Matrix n n F :=
    Algebra.TensorProduct.lift (Algebra.ofId F _) ρ.toIntAlgHom
      (fun c y => Algebra.commute_algebraMap_left c _)
  let b := Algebra.TensorProduct.basis F β
  have hb : ∀ i, φ (b i) = ρ (β i) := by
    intro i
    simp only [φ, b, Algebra.TensorProduct.basis_apply]
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, one_mul]
    rfl
  have := matrix_descent F k _ n _ b φ r x
    (by simpa only [hb] using hli) (by simpa only [hb] using hsp)
  simpa only [hb] using this

theorem lift_basis (R n κ : Type) [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n]
    [Fintype κ] (v : κ → n → R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun q => fun a => IsLocalRing.residue R (v q a)))
    (hsp : Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun q => fun a => IsLocalRing.residue R (v q a)) = ⊤) :
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  classical
  let b0 := Basis.mk hli hsp.ge
  let σ : n ≃ κ := (Pi.basisFun (IsLocalRing.ResidueField R) n).indexEquiv b0
  have h0 := ((Pi.basisFun (IsLocalRing.ResidueField R) n).reindex σ).is_basis_iff_det.1 ⟨hli, hsp⟩
  rw [((Pi.basisFun R n).reindex σ).is_basis_iff_det]
  rw [Basis.det_apply] at h0 ⊢
  rw [← isUnit_map_iff (IsLocalRing.residue R), RingHom.map_det]
  convert h0 using 2
  ext i j
  simp [Basis.toMatrix_apply]

end PositivityTheory.Xgn.FreeNakayamaDescent

theorem PositivityTheory.Xgn.free_module_nakayama_descent : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ := by
  intro E _ _ R k _ _ _ f _ n _ _ r ρ ⟨x, hli, hsp⟩
  letI : Algebra (IsLocalRing.ResidueField R) k := (IsLocalRing.ResidueField.lift f).toAlgebra
  let ρ0 : 𝓞 E →+* Matrix n n (IsLocalRing.ResidueField R) :=
    (IsLocalRing.residue R).mapMatrix.comp ρ
  have hb : ∀ a, ρ0 a = (ρ a).map (IsLocalRing.residue R) := fun _ => rfl
  have hb' : ∀ a, (ρ0 a).map (algebraMap (IsLocalRing.ResidueField R) k) = (ρ a).map f := by
    intro i
    rw [hb, Matrix.map_map]
    rfl
  obtain ⟨x0, h1, h2⟩ := PositivityTheory.Xgn.FreeNakayamaDescent.int_descent
    (IsLocalRing.ResidueField R) k _ n _ (RingOfIntegers.basis E) ρ0 r x
    (by simpa only [hb'] using hli) (by simpa only [hb'] using hsp)
  choose y hy using fun j a => IsLocalRing.residue_surjective (R := R) (x0 j a)
  refine ⟨y, ?_⟩
  have key : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => fun a =>
      IsLocalRing.residue R ((ρ (RingOfIntegers.basis E q.2)).mulVec (y q.1) a)) =
      fun q => (ρ0 (RingOfIntegers.basis E q.2)).mulVec (x0 q.1) := by
    funext q a
    rw [hb, RingHom.map_mulVec]
    congr 1
    funext a
    exact hy _ _
  apply PositivityTheory.Xgn.FreeNakayamaDescent.lift_basis
  · rw [key]; exact h1
  · rw [key]; exact h2
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.JordanBasisNilpotent
section
namespace PositivityTheory.Xgn.JordanBasis

theorem exists_span_sup_range {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (π : Module.End k W) (r : ℕ)
    (h : Module.finrank k (LinearMap.ker π) ≤ r) :
    ∃ x : Fin r → W, ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u := by
  classical
  have hd : Module.finrank k (W ⧸ LinearMap.range π) ≤ r := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range π)
    have h2 := LinearMap.finrank_range_add_finrank_ker π
    omega
  obtain ⟨g, hg⟩ : ∃ g : W ⧸ LinearMap.range π → W, ∀ q, (LinearMap.range π).mkQ (g q) = q :=
    ⟨_, Function.surjInv_eq (LinearMap.range π).mkQ_surjective⟩
  let b := Module.finBasis k (W ⧸ LinearMap.range π)
  let x : Fin r → W := fun i =>
    if h : (i : ℕ) < Module.finrank k (W ⧸ LinearMap.range π) then g (b ⟨i, h⟩) else 0
  have hspan : ∀ j, g (b j) ∈ Submodule.span k (Set.range x) := by
    intro j
    apply Submodule.subset_span
    refine ⟨⟨j, lt_of_lt_of_le j.2 hd⟩, ?_⟩
    simp [x, j.2]
  refine ⟨x, fun v => ?_⟩
  refine ⟨∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hspan j), ?_⟩
  have hq : (LinearMap.range π).mkQ
      (v - ∑ j, b.repr ((LinearMap.range π).mkQ v) j • g (b j)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [map_smul, hg]
    rw [b.sum_repr, sub_self]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hq
  exact ⟨u, by rw [hu]; abel⟩

theorem span_eq_top {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    (π : Module.End k W) (e r : ℕ) (hπ : π ^ e = 0) (x : Fin r → W)
    (hx : ∀ v : W, ∃ a ∈ Submodule.span k (Set.range x), ∃ u : W, v = a + π u) :
    Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) = ⊤ := by
  classical
  set S := Submodule.span k (Set.range fun q : Fin r × Fin e => (π ^ (q.2 : ℕ)) (x q.1)) with hS
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    rw [pow_zero] at hπ
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = 0 := by simpa using LinearMap.congr_fun hπ v
    rw [hv]
    exact S.zero_mem
  have hinv : ∀ s ∈ S, π s ∈ S := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => π s ∈ S) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      by_cases hj : (j : ℕ) + 1 < e
      · apply Submodule.subset_span
        refine ⟨(i, ⟨(j : ℕ) + 1, hj⟩), ?_⟩
        simp [pow_succ', Module.End.mul_apply]
      · have hje : (j : ℕ) + 1 = e := by omega
        have h0 : π ((π ^ (j : ℕ)) (x i)) = 0 := by
          have h1 : (π ^ ((j : ℕ) + 1)) (x i) = π ((π ^ (j : ℕ)) (x i)) := by
            rw [pow_succ', Module.End.mul_apply]
          rw [← h1, hje, hπ, LinearMap.zero_apply]
        show π ((π ^ (j : ℕ)) (x i)) ∈ S
        rw [h0]
        exact S.zero_mem
    · simp
    · intro a c _ _ ha hc
      rw [map_add (f := _)]
      exact S.add_mem ha hc
    · intro c a _ ha
      rw [map_smul]
      exact S.smul_mem c ha
  have hxS : ∀ a ∈ Submodule.span k (Set.range x), a ∈ S := by
    intro a ha
    refine Submodule.span_le.2 ?_ ha
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨(i, ⟨0, he⟩), by simp⟩
  have hpow : ∀ n : ℕ, ∀ s ∈ S, (π ^ n) s ∈ S := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      rw [pow_succ', Module.End.mul_apply]
      exact hinv _ (ih s hs)
  have key : ∀ n : ℕ, ∀ v : W, ∃ s ∈ S, ∃ u : W, v = s + (π ^ n) u := by
    intro n
    induction n with
    | zero => intro v; exact ⟨0, S.zero_mem, v, by simp⟩
    | succ n ih =>
      intro v
      obtain ⟨s, hs, u, rfl⟩ := ih v
      obtain ⟨a, ha, u', rfl⟩ := hx u
      refine ⟨s + (π ^ n) a, S.add_mem hs (hpow n a (hxS a ha)), u', ?_⟩
      rw [map_add (f := _), pow_succ, Module.End.mul_apply, add_assoc]
  refine Submodule.eq_top_iff'.2 fun v => ?_
  obtain ⟨s, hs, u, rfl⟩ := key e v
  rw [hπ, LinearMap.zero_apply, add_zero]
  exact hs

end PositivityTheory.Xgn.JordanBasis
end

