module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainTens
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.chain_tens :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [IsLocalRing O] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing B] [Algebra O B] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal (O' ⊗[O] B)) (E : Fin h → Ideal (O' ⊗[O] B)), (∀ i, (P i).IsPrime ∧ (P i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal (O' ⊗[O] B)) (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) → ∃ Q : Ideal (O' ⊗[O] B), Q.IsPrime ∧ Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = q ∧ Q ≤ P := by
  intro O O' B _ _ _ _ _ _ _ _ _ h p e hp he
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  let φ : B ⊗[O] O' ≃ₐ[B] O' ⊗[O] B := Algebra.TensorProduct.commRight O B O'
  haveI : Module.Finite B (O' ⊗[O] B) := Module.Finite.equiv φ.toLinearEquiv
  haveI : Module.Free B (O' ⊗[O] B) := Module.Free.of_equiv φ.toLinearEquiv
  haveI : Module.FaithfullyFlat O O' := inferInstance
  haveI : Module.FaithfullyFlat B (O' ⊗[O] B) :=
    Module.FaithfullyFlat.of_linearEquiv B (B ⊗[O] O') φ.symm.toLinearEquiv
  haveI : FaithfulSMul B (O' ⊗[O] B) := inferInstance
  exact UpperTheory.V.Pa.BC.chain_lift B (O' ⊗[O] B) h p e hp he
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsFiniteSpanningTaylorWilesTensor
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem tens_fin {Λ B S R M : Type} [CommRing Λ] [CommRing B] [CommRing S] [CommRing R] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Finite B S] [Module.Finite Λ M]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (θ : R →+* S)
    (hθ : ∀ a : Λ, ∃ t : R, θ t = algebraMap B S (lam a)) :
    ∃ s : Finset (S ⊗[B] M), ∀ z, ∃ c : S ⊗[B] M → R, z = ∑ g ∈ s, θ (c g) • g := by
  classical
  obtain ⟨a, ha⟩ := Module.Finite.fg_top (R := B) (M := S)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  let s : Finset (S ⊗[B] M) := Finset.image₂ (fun x y => x ⊗ₜ[B] y) a t
  refine ⟨s, ?_⟩
  have h1 : ∀ x ∈ a, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x hx y
    have hy : y ∈ Submodule.span Λ (t : Set M) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image₂_of_mem hx hy))
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h h' => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h h'
    | smul c y _ h =>
      obtain ⟨w, hw⟩ := hθ c
      rw [hl, TensorProduct.tmul_smul, ← algebraMap_smul S]
      exact Submodule.smul_mem _ (⟨algebraMap B S (lam c), w, hw⟩ : θ.range) h
  have h2 : ∀ x : S, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x
    have hx : x ∈ Submodule.span B (a : Set S) := ha ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => intro y; rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add x x' _ _ h h' => intro y; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ (h y) (h' y)
    | smul c x _ h => intro y; rw [TensorProduct.smul_tmul]; exact h _
  intro z
  have hz : z ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul x y => exact h2 x y
    | add z z' h h' => exact Submodule.add_mem _ h h'
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hz
  choose c hc using fun g => (f g).2
  refine ⟨c, ?_⟩
  rw [← hf]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hc]
  rfl

theorem UpperTheory.V.Pa.BC.exists_finite_spanning_taylorWiles_tensor :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (σ : Type) (D : ℕ) (b : TWBase u J σ D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (A : TWRing b h ut N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (m : TWMaps Nq ph ta A ex), ∃ s : Finset (SpAt u (fun j => h.p₀ (ph j)) ut ⊗[B] b.M), ∀ z, ∃ c : _ → A.R, z = ∑ g ∈ s, m.θ (c g) • g := by
  intro l _ L G0 n O _ _ _ r B _ _ _ u J σ D b G h q ut N A Nq ph ta ex m
  haveI : Module.Finite B (SpAt u (fun j => h.p₀ (ph j)) ut) := (UpperTheory.V.Pa.BC.sp_fin B q n _ _).1
  haveI := b.fin
  exact tens_fin (Λ := abelian₂ O σ D) (fun a => b.lam a) b.smul_lam m.θ.toRingHom fun a =>
    ⟨A.s (MvPowerSeries.C a), by
      have := m.theta_coefficientMap_eq (MvPowerSeries.C a)
      rw [MvPowerSeries.constantCoeff_C] at this
      exact this⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSField
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem span_map_mem {A B : Type} [Ring A] [Ring B] (F : A →+* B) (I : Set A) (x : A)
    (hx : x ∈ TwoSidedIdeal.span I) : F x ∈ TwoSidedIdeal.span (F '' I) := by
  have h : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap F (TwoSidedIdeal.span (F '' I)) := by
    rw [TwoSidedIdeal.span_le]
    intro a ha
    exact (TwoSidedIdeal.mem_comap F).2 (TwoSidedIdeal.subset_span ⟨a, ha, rfl⟩)
  exact (TwoSidedIdeal.mem_comap F).1 (h hx)

private theorem fin_quot {R κ G : Type} [CommRing R] [Field κ] [Group G] (I : Set (MonoidAlgebra R G))
    (ψ : R →+* κ)
    (hs : ∃ s : Finset G, ∀ y : MonoidAlgebra R G, ∃ c : G → R,
      y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span I) :
    Module.Finite κ (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G ψ '' I)).ringCon.Quotient := by
  classical
  obtain ⟨s, hs⟩ := hs
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G ψ '' I) with hJ
  let π : MonoidAlgebra κ G →ₗ[κ] J.ringCon.Quotient :=
    { toFun := J.ringCon.mk'
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a b => rfl }
  have hπ : Function.Surjective π := J.ringCon.mk'_surjective
  refine ⟨⟨s.image (fun g => π (MonoidAlgebra.single g 1)), ?_⟩⟩
  rw [eq_top_iff]
  intro z hz
  clear hz
  obtain ⟨y, rfl⟩ := hπ z
  have key : ∀ (g : G) (k : κ), π (MonoidAlgebra.single g k) = k • π (MonoidAlgebra.single g 1) := by
    intro g k
    rw [← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | single g k =>
    rw [key]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc⟩ := hs (MonoidAlgebra.single g 1)
    have h1 := span_map_mem (MonoidAlgebra.mapRingHom G ψ) I _ hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum] at h1
    simp only [MonoidAlgebra.mapRingHom_single, map_one] at h1
    have h2 : π (MonoidAlgebra.single g 1) = π (∑ g ∈ s, MonoidAlgebra.single g (ψ (c g))) := by
      show J.ringCon.mk' _ = J.ringCon.mk' _
      exact J.ringCon.eq.2 ((TwoSidedIdeal.rel_iff J _ _).2 h1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, ha, rfl⟩)

theorem UpperTheory.V.Pa.BC.nonSS_field :
    ∀ (R S S' G : Type) [CommRing R] [CommRing S] [CommRing S'] [Group G] (I : Set (MonoidAlgebra R G)) (φ : R →+* S) (φ' : R →+* S') (Q : Ideal S) (Q' : Ideal S'), Q'.IsPrime → Q'.comap φ' = Q.comap φ → (∃ s : Finset G, ∀ y : MonoidAlgebra R G, ∃ c : G → R, y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span I) → NonSS I φ Q → NonSS I φ' Q' := by
  intro R S S' G _ _ _ _ I φ φ' Q Q' hQ' hc hs hN
  obtain ⟨κ, _, f, hf, hns⟩ := hN
  let f' : S' →+* FractionRing (S' ⧸ Q') :=
    (algebraMap (S' ⧸ Q') (FractionRing (S' ⧸ Q'))).comp (Ideal.Quotient.mk Q')
  have hf' : RingHom.ker f' = Q' := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]
  have hk : RingHom.ker (f.comp φ) = RingHom.ker (f'.comp φ') := by
    rw [← RingHom.comap_ker, ← RingHom.comap_ker, hf, hf', hc]
  obtain ⟨K, _, j₁, j₂, hj⟩ := UpperTheory.V.Pa.BC.common_field R κ _ _ _ hk
  refine ⟨K, inferInstance, j₂.comp f', ?_, ?_⟩
  · rw [RingHom.ker_comp_of_injective _ j₂.injective, hf']
  · intro hss
    apply hns
    letI : Algebra κ K := j₁.toAlgebra
    haveI := fin_quot I (f.comp φ) hs
    obtain ⟨e⟩ := UpperTheory.V.Pa.BC.grp_quot_bc κ K G (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)
    have him : MonoidAlgebra.mapRingHom G (algebraMap κ K) '' (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)
        = MonoidAlgebra.mapRingHom G ((j₂.comp f').comp φ') '' I := by
      rw [RingHom.comp_assoc, ← hj, MonoidAlgebra.mapRingHom_comp j₁, RingHom.coe_comp, Set.image_comp]
      rfl
    rw [← him] at hss
    exact UpperTheory.V.Pa.BC.ss_descend κ K _ e.symm.isSemisimpleRing
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PtLift
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem root_const {O K : Type} [CommRing O] [Field K] [Algebra O K] (P : Polynomial O) (hm : P.Monic)
    (hs : (P.map (algebraMap O K)).Splits) (y : PowerSeries K)
    (hy : Polynomial.eval₂ (algebraMap O (PowerSeries K)) y P = 0) : ∃ c : K, y = PowerSeries.C c := by
  have h : algebraMap O (PowerSeries K) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
    RingHom.ext fun a => PowerSeries.algebraMap_apply
  rw [h, ← Polynomial.eval₂_map, hs.eq_prod_roots_of_monic (hm.map _), Polynomial.eval₂_multiset_prod,
    Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at hy
  obtain ⟨c, -, hc⟩ := hy
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hc
  exact ⟨c, sub_eq_zero.1 hc⟩

private theorem surj_of_card {O' K : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field K]
    [Finite K] (φ : O' →+* K) (hc : Nat.card (ResidueField O') = Nat.card K) : Function.Surjective φ := by
  have hne : RingHom.ker φ ≠ ⊥ := by
    intro h
    have hi : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h
    haveI : Finite O' := Finite.of_injective φ hi
    exact IsDiscreteValuationRing.not_isField O' (Finite.isField_of_domain O')
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : RingHom.ker φ = maximalIdeal O' :=
    IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
  let g : ResidueField O' →+* K := Ideal.Quotient.lift (maximalIdeal O') φ (fun a ha => by
    rw [← hmax] at ha; exact ha)
  have hg : Function.Bijective g := by
    haveI : Finite (ResidueField O') := Finite.of_injective g g.injective
    exact (Nat.bijective_iff_injective_and_card g).2 ⟨g.injective, hc⟩
  intro k
  obtain ⟨a, ha⟩ := hg.2 k
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨b, ha⟩

private theorem exists_pt {O O' B K : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing B] [Algebra O B]
    [Field K] [Algebra O K] (α : O') (P : Polynomial O) (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B))
    (hα : Algebra.adjoin O {α} = ⊤) (hm : P.Monic) (h0 : Polynomial.aeval α P = 0)
    (hs : (P.map (algebraMap O K)).Splits) (hQ : Q.IsPrime)
    (hc : Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f) :
    ∃ x : O' ⊗[O] B →+* PowerSeries K, (∀ b, x (1 ⊗ₜ b) = f b) ∧ RingHom.ker x = Q := by
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  have hB : ∀ b : B, algebraMap B (O' ⊗[O] B) b = 1 ⊗ₜ b := fun b => rfl
  have hcomp : (algebraMap B (O' ⊗[O] B)).comp (algebraMap O B) =
      (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B).comp (algebraMap O O') :=
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
  obtain ⟨x, hx1, hx2⟩ := UpperTheory.V.AlgebraTools.exists_lift_ker_eq B (O' ⊗[O] B) (PowerSeries K) f.toRingHom Unit
    (fun _ => α ⊗ₜ 1) (fun _ => P.map (algebraMap O B)) (by
      have hl : ∀ o : O', o ⊗ₜ[O] (1 : B) ∈ Algebra.adjoin B (Set.range fun _ : Unit => α ⊗ₜ[O] (1 : B)) := by
        intro o
        have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
        induction ho using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff.1 hy]
          exact Algebra.subset_adjoin ⟨(), rfl⟩
        | algebraMap r =>
          have := RingHom.congr_fun hcomp r
          change algebraMap B (O' ⊗[O] B) (algebraMap O B r) = algebraMap O O' r ⊗ₜ 1 at this
          rw [← this]
          exact Subalgebra.algebraMap_mem _ _
        | add y z _ _ hy hz => rw [TensorProduct.add_tmul]; exact add_mem hy hz
        | mul y z _ _ hy hz =>
          have := mul_mem hy hz
          rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
      rw [eq_top_iff]
      rintro s -
      induction s using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul o b =>
        have := mul_mem (hl o) (Subalgebra.algebraMap_mem _ b)
        rwa [hB, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      | add y z hy hz => exact add_mem hy hz)
    (fun _ => ⟨hm.map _, by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
      have := Polynomial.hom_eval₂ P (algebraMap O O')
        (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B) α
      rw [← Polynomial.aeval_def, h0, map_zero] at this
      exact this.symm, by
      have h : f.toRingHom.comp (algebraMap O B) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
        RingHom.ext fun a => (f.commutes a).trans PowerSeries.algebraMap_apply
      rw [Polynomial.map_map, h, ← Polynomial.map_map]
      exact hs.map _⟩) Q hQ hc
  exact ⟨x, fun b => RingHom.congr_fun hx1 b, hx2⟩

theorem UpperTheory.V.Pa.BC.pt_lift :
    ∀ (l : ℕ) [Fact l.Prime] (O O' : Type) [CommRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsCoef l O'] [Algebra O O'] (α : O') (P : Polynomial O) (B : Type) [CommRing B] [Algebra O B] (K : Type) [Field K] [Finite K] [Algebra O K] (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B)), Algebra.adjoin O {α} = ⊤ → P.Monic → Polynomial.aeval α P = 0 → (P.map (algebraMap O K)).Splits → Nat.card (ResidueField O') = Nat.card K → Q.IsPrime → Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f → ∃ (_ : Algebra O' K) (f' : Til O O' B →ₐ[O'] PowerSeries K), Function.Surjective (algebraMap O' K) ∧ (∀ b, f' (Til.ι O O' B b) = f b) ∧ f' (Til.s O O' B) = PowerSeries.X ∧ (RingHom.ker f').comap (Til.C O O' B) = Q := by
  intro l _ O O' _ _ _ _ _ _ α P B _ _ K _ _ _ f Q hα hm h0 hs hcard hQ hc
  obtain ⟨x, hx1, hx2⟩ := exists_pt α P f Q hα hm h0 hs hQ hc
  let y : O' →+* PowerSeries K := x.comp (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B)
  have hyO : y.comp (algebraMap O O') = algebraMap O (PowerSeries K) := by
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := O) (A := O') (B := B)) r
    change x ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap O O')) r) = _
    rw [this]
    exact (hx1 _).trans (f.commutes r)
  have hconst : ∀ o : O', ∃ c : K, y o = PowerSeries.C c := by
    intro o
    have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
    induction ho using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff.1 hz]
      refine root_const P hm hs _ ?_
      rw [← hyO, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, h0, map_zero]
    | algebraMap r => exact ⟨algebraMap O K r, (RingHom.congr_fun hyO r).trans PowerSeries.algebraMap_apply⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' + b', by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' * b', by rw [map_mul, map_mul, ha, hb]⟩
  let φ : O' →+* K := (PowerSeries.constantCoeff : PowerSeries K →+* K).comp y
  have hφ : ∀ o, y o = PowerSeries.C (φ o) := by
    intro o
    obtain ⟨c, hc⟩ := hconst o
    change _ = PowerSeries.C (PowerSeries.constantCoeff (y o))
    rw [hc, PowerSeries.constantCoeff_C]
  obtain ⟨g, hg1, hg2⟩ := UpperTheory.V.Pa.BC.ps_ev (O' ⊗[O] B) K x
  letI : Algebra O' K := φ.toAlgebra
  let g' : Til O O' B →+* PowerSeries K := g
  have hg1' : ∀ a, g' (Til.C O O' B a) = x a := hg1
  refine ⟨this, { g' with commutes' := fun o => ?_ }, surj_of_card φ hcard, fun b => ?_, hg2, ?_⟩
  · have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
      PowerSeries.algebraMap_apply
    change g' (algebraMap O' (Til O O' B) o) = _
    rw [h, hg1', PowerSeries.algebraMap_apply]
    exact hφ o
  · exact (hg1' _).trans (hx1 b)
  · ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hx2, RingHom.mem_ker, ← hg1']
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfIso
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.mvps_congr (K A B σ : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (e : A ≃ₐ[K] B) :
    ∃ E : MvPowerSeries σ A ≃ₐ[K] MvPowerSeries σ B, ∀ a, E a = MvPowerSeries.map (e : A →+* B) a := by
  have h1 : ∀ φ : MvPowerSeries σ A,
      MvPowerSeries.map (e.symm : B →+* A) (MvPowerSeries.map (e : A →+* B) φ) = φ := by
    intro φ
    ext n
    simp
  have h2 : ∀ φ : MvPowerSeries σ B,
      MvPowerSeries.map (e : A →+* B) (MvPowerSeries.map (e.symm : B →+* A) φ) = φ := by
    intro φ
    ext n
    simp
  let f : MvPowerSeries σ A ≃+* MvPowerSeries σ B :=
    { toFun := MvPowerSeries.map (e : A →+* B)
      invFun := MvPowerSeries.map (e.symm : B →+* A)
      left_inv := h1
      right_inv := h2
      map_mul' := map_mul _
      map_add' := map_add _ }
  refine ⟨AlgEquiv.ofRingEquiv (f := f) ?_, fun a => ?_⟩
  · intro k
    simp [f, MvPowerSeries.algebraMap_apply]
  · rfl

theorem UpperTheory.V.Pa.BC.sinf_iso :
    ∀ (l : ℕ) (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D q n : ℕ) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n, SinfRel l τ τS := by
  intro l O O' _ _ _ _ _ D q n τ hτ
  obtain ⟨τ0, h0ι, -, -, h0c⟩ :=
    UpperTheory.V.Pa.BC.til_mvps O O' (abelian₂ O Empty D) (Fin q × Fin n)
  obtain ⟨E, hE⟩ :=
    UpperTheory.V.Pa.BC.mvps_congr O' (Til O O' (abelian₂ O Empty D)) (abelian₂ O' Unit D) (Fin q × Fin n) τ
  have key : ∀ x : MvPowerSeries (Fin q × Fin n) (abelian₂ O Empty D),
      (τ0.trans E) (Til.ι O O' _ x) = MvPowerSeries.map ((τ : _ →+* _).comp (Til.ι O O' _)) x := by
    intro x
    rw [AlgEquiv.trans_apply, h0ι, hE, ← RingHom.comp_apply, ← MvPowerSeries.map_comp]
  refine ⟨τ0.trans E, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p
    rw [key, MvPowerSeries.map_X]
  · intro a
    rw [key, MvPowerSeries.map_C, RingHom.comp_apply]
    simp [hτ]
  · intro c hc z
    rw [AlgEquiv.trans_apply, hE, MvPowerSeries.constantCoeff_map, h0c c hc z]
    rfl
  · intro a
    unfold delIdeal
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    congr 1
    funext p
    simp only [Function.comp_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, key, map_sub, map_pow, map_add, map_one, MvPowerSeries.map_X]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMod
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_mod :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (f : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] [Module S M] [Module.Finite S M], (∀ (a : S) (m : M), a • m = f a • m) → ∃ e : Til O O' S ⊗[S] M ≃+ Til O O' R ⊗[R] M, (∀ a m, e (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m) ∧ ∀ a z, e (a • z) = Til.map O' f a • e z := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ f M _ _ _ _ h
  letI : Module O M := Module.compHom M (algebraMap O R)
  haveI : IsScalarTower O R M := ⟨fun o r m => by
    show (o • r) • m = (algebraMap O R o) • (r • m)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower O S M := ⟨fun o s m => by
    show (o • s) • m = (algebraMap O R o) • (s • m)
    rw [h (o • s) m, h s m, Algebra.smul_def o s, map_mul, f.commutes, mul_smul]⟩
  have hfin : Module.Finite R M := by
    letI : Algebra S R := f.toRingHom.toAlgebra
    haveI : IsScalarTower S R M := ⟨fun s r m => by
      show (f s * r) • m = s • (r • m)
      rw [mul_smul, h]⟩
    exact Module.Finite.of_restrictScalars_finite S R M
  haveI := hfin
  obtain ⟨e1, he1⟩ := BC.til_ev O O' S M
  obtain ⟨e2, he2⟩ := BC.til_ev O O' R M
  have hact : ∀ (m : M) (x : O' ⊗[O] S), Til.act O' m (Algebra.TensorProduct.map (AlgHom.id O' O') f x) = Til.act O' m x := by
    intro m x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o s => simp [Til.act, h]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hcoeff : ∀ k a, Til.coeff O O' R k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' S k a) := by
    intro k a
    rfl
  have key : ∀ a m, e1 (a ⊗ₜ m) = e2 (Til.map O' f a ⊗ₜ m) := by
    intro a m
    funext k
    rw [he1, he2, hcoeff, hact]
  have hform : ∀ a m, (e1.trans e2.symm) (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m := by
    intro a m
    rw [AddEquiv.trans_apply, key, AddEquiv.symm_apply_apply]
  refine ⟨e1.trans e2.symm, hform, ?_⟩
  intro a z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rw [TensorProduct.smul_tmul', hform, hform, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilPrime
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_prime :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing B] [Algebra O B] [IsNoetherianRing B] (Q : Ideal (O' ⊗[O] B)), Q.IsPrime → (Q.map (Til.C O O' B)).IsPrime ∧ (Q.map (Til.C O O' B)).comap (Til.ι O O' B) = Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) := by
  intro O O' B _ _ _ _ _ _ _ Q hQ
  haveI hN : IsNoetherianRing (O' ⊗[O] B) := by
    letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite B (O' ⊗[O] B) :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight O B O').toLinearEquiv
    exact Algebra.FiniteType.isNoetherianRing B (O' ⊗[O] B)
  obtain ⟨-, -, h3, h4⟩ := UpperTheory.V.AlgebraTools.powerSeries_ker_map (O' ⊗[O] B) Q (IsNoetherian.noetherian Q)
  refine ⟨h3 hQ, ?_⟩
  have h5 : (Q.map (Til.C O O' B)).comap (Til.C O O' B) = Q := h4
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  conv_rhs => rw [← h5]
  exact Iff.rfl
end

