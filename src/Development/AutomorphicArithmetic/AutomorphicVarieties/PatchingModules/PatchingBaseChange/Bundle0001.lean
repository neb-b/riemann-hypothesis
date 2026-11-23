module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.LinearTopology

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainLift
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.chain_lift_down (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Flat B B'] (P : Ideal B') (q : Ideal B) (hP : P.IsPrime) (hq : q.IsPrime)
    (hle : q ≤ P.comap (algebraMap B B')) :
    ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  haveI : (P.comap (algebraMap B B')).IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver (P.comap (algebraMap B B')) := ⟨rfl⟩
  obtain ⟨Q, h1, h2, h3⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q)
    (q := P.comap (algebraMap B B')) P hle
  exact ⟨Q, h2, h3.over.symm, h1⟩

private theorem UpperTheory.V.Pa.BC.prime_chain_lift_extension (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Algebra.IsIntegral B B'] [Module.Flat B B'] (h : ℕ) :
    ∀ (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) →
      (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) →
      ∀ P0 : Ideal B', P0.IsPrime → P0.comap (algebraMap B B') = p 0 →
      ∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), P 0 = P0 ∧
        (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧
        ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧
          E i ≤ P i.succ := by
  induction h with
  | zero =>
    intro p e _ _ P0 hP0 hP0c
    refine ⟨fun _ => P0, Fin.elim0, rfl, ?_, fun i => i.elim0⟩
    intro i
    rw [Fin.fin_one_eq_zero i]
    exact ⟨hP0, hP0c⟩
  | succ h ih =>
    intro p e hp he P0 hP0 hP0c
    obtain ⟨he0, he0l, he0r⟩ := he 0
    obtain ⟨E0, hE0, hE0c, hE0le⟩ :=
      UpperTheory.V.Pa.BC.chain_lift_down B B' P0 (e 0) hP0 he0 (by rw [hP0c]; exact he0l)
    haveI := hp (Fin.succ 0)
    haveI := hE0
    obtain ⟨P1, hP1ge, hP1, hP1c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      (p (Fin.succ 0)) E0 (by
        change E0.comap (algebraMap B B') ≤ p (Fin.succ 0)
        rw [hE0c]
        exact he0r)
    obtain ⟨P', E', hP'0, hP', hE'⟩ := ih (fun i => p i.succ) (fun i => e i.succ)
      (fun i => hp i.succ)
      (fun i => by
        obtain ⟨a, b, c⟩ := he i.succ
        refine ⟨a, ?_, c⟩
        rw [← Fin.succ_castSucc] at b
        exact b)
      P1 hP1 hP1c
    refine ⟨(Fin.cons P0 P' : Fin (h + 1 + 1) → Ideal B'),
      (Fin.cons E0 E' : Fin (h + 1) → Ideal B'), Fin.cons_zero _ _, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact ⟨hP0, hP0c⟩
      | succ j => rw [Fin.cons_succ]; exact hP' j
    · intro i
      cases i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hP'0]
        exact ⟨hE0, hE0c, hE0le, hP1ge⟩
      | succ j =>
        rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hE' j

theorem UpperTheory.V.Pa.BC.chain_lift :
    ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [Algebra.IsIntegral B B'] [Module.Flat B B'] [FaithfulSMul B B'] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal B') (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (algebraMap B B') → ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  intro B B' _ _ _ _ _ _ h p e hp he
  refine ⟨?_, fun P q hP hq hle => UpperTheory.V.Pa.BC.chain_lift_down B B' P q hP hq hle⟩
  haveI := hp 0
  obtain ⟨P0, _, hP0, hP0c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B') (p 0) ⊥ (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [(FaithfulSMul.algebraMap_injective B B') (hx.trans (map_zero _).symm)]
    exact Ideal.zero_mem _)
  obtain ⟨P, E, _, hPc, hE⟩ := UpperTheory.V.Pa.BC.prime_chain_lift_extension B B' h p e hp he P0 hP0 hP0c
  exact ⟨P, E, hPc, hE⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.CommonField
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.common_field :
    ∀ (B κ₁ κ₂ : Type) [CommRing B] [Field κ₁] [Field κ₂] (f₁ : B →+* κ₁) (f₂ : B →+* κ₂), RingHom.ker f₁ = RingHom.ker f₂ → ∃ (κ : Type) (_ : Field κ) (j₁ : κ₁ →+* κ) (j₂ : κ₂ →+* κ), j₁.comp f₁ = j₂.comp f₂ :=
  _root_.UpperTheory.Reformulated.B.Qe15.common_field
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.DiscStMap
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem tr_map {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : GDet n R G)
    (f : R →+* R') (x : G) :
    (D.map f).tr (MonoidAlgebra.single x 1) = f (D.tr (MonoidAlgebra.single x 1)) := by
  have h := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single x 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one] at h
  exact h

private theorem tr_comap {n : ℕ} {R G G' : Type} [CommRing R] [Group G] [Group G'] (D : GDet n R G)
    (p : G' →* G) (x : G') :
    (D.comap p).tr (MonoidAlgebra.single x 1) = D.tr (MonoidAlgebra.single (p x) 1) := by
  unfold GDet.tr GDet.lam GDet.comap GDet.chi
  simp only [MonoidAlgebra.mapRingHom_single, map_one, MonoidHom.coe_comp, Function.comp_apply]
  have hY : ((MonoidAlgebra.mapDomainRingHom (Polynomial R) p :
        MonoidAlgebra (Polynomial R) G' →+* MonoidAlgebra (Polynomial R) G) :
        MonoidAlgebra (Polynomial R) G' →* MonoidAlgebra (Polynomial R) G)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) =
      MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single (p x) 1 := by
    change (MonoidAlgebra.mapDomainRingHom (Polynomial R) p)
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.single x 1) = _
    rw [map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, map_one]
  exact congrArg (fun y => (-1) ^ 1 * ((D.D (Polynomial R)) y).coeff (n - 1)) hY

theorem UpperTheory.V.Pa.BC.discSt_map :
    ∀ (n : ℕ) (R R' G : Type) [CommRing R] [CommRing R'] [Group G] (D : GDet n R G), (∀ (g : R →+* R') (Q : Ideal R'), DiscSt (D.map g) Q ↔ DiscSt D (Q.comap g)) ∧ (∀ (G' : Type) [Group G'] (p : G' →* G), Function.Surjective p → ∀ Q : Ideal R, DiscSt (D.comap p) Q ↔ DiscSt D Q) ∧ ∀ Q Q' : Ideal R, Q ≤ Q' → DiscSt D Q' → DiscSt D Q := by
  intro n R R' G _ _ _ D
  refine ⟨fun g Q => ?_, fun G' _ p hp Q => ?_, fun Q Q' hQ hD => ?_⟩
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G,
        (Matrix.of fun i j => (D.map g).tr (MonoidAlgebra.single (a i * b j) 1)).det =
        g ((Matrix.of fun i j => D.tr (MonoidAlgebra.single (a i * b j) 1)).det) := by
      intro a b
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [RingHom.mapMatrix_apply, tr_map]
    simp only [key, Ideal.mem_comap]
  · unfold DiscSt
    have key : ∀ a b : Fin (n * n) → G',
        (Matrix.of fun i j => (D.comap p).tr (MonoidAlgebra.single (a i * b j) 1)) =
        Matrix.of fun i j => D.tr (MonoidAlgebra.single (p (a i) * p (b j)) 1) := by
      intro a b
      ext i j
      simp [tr_comap]
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨fun i => p (a i), fun j => p (b j), by simpa only [key] using h⟩
    · rintro ⟨a, b, h⟩
      refine ⟨fun i => Function.surjInv hp (a i), fun j => Function.surjInv hp (b j), ?_⟩
      simp only [key, Function.surjInv_eq hp]
      exact h
  · obtain ⟨a, b, h⟩ := hD
    exact ⟨a, b, fun hq => h (hQ hq)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsSemilinearEquivBaseChangeTensor
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor :
    ∀ (B P B' P₁ P' : Type) [CommRing B] [CommRing P] [CommRing B'] [CommRing P₁] [CommRing P'] [Algebra B P] [Algebra B B'] [Algebra P P₁] [Algebra B' P'] (τ : P₁ ≃+* P') (M M' : Type) [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B' M'] (_μ : B' ⊗[B] M ≃ₗ[B'] M'), (∀ b, τ (algebraMap P P₁ (algebraMap B P b)) = algebraMap B' P' (algebraMap B B' b)) → ∃ e : P₁ ⊗[P] (P ⊗[B] M) ≃+ P' ⊗[B'] M', ∀ z w, e (z • w) = τ z • e w := by
  intro B P B' P₁ P' _ _ _ _ _ _ _ _ _ τ M M' _ _ _ _ μ h
  letI : Algebra P₁ P' := τ.toRingHom.toAlgebra
  letI : Algebra P P' := (τ.toRingHom.comp (algebraMap P P₁)).toAlgebra
  letI : Algebra B P' := ((algebraMap B' P').comp (algebraMap B B')).toAlgebra
  haveI : IsScalarTower P P₁ P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B B' P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B P P' := IsScalarTower.of_algebraMap_eq (fun b => (h b).symm)
  let t : P₁ ≃ₗ[P₁] P' :=
    { τ.toAddEquiv with
      map_smul' := fun a b => by
        show τ (a * b) = τ a * τ b
        exact map_mul τ a b }
  let e1 : P₁ ⊗[P] (P ⊗[B] M) ≃ₗ[P₁] P' ⊗[P] (P ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.congr t (LinearEquiv.refl P _)
  let e2 : P' ⊗[P] (P ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B P P' P' M
  let e3 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B B' P' P' M
  let e4 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B'] M' :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P' P') μ
  let f := e2.trans (e3.symm.trans e4)
  refine ⟨e1.toAddEquiv.trans f.toAddEquiv, fun z w => ?_⟩
  show f (e1 (z • w)) = τ z • f (e1 w)
  rw [map_smul, ← map_smul f]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.GenBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.gen_bc :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (S : Set B) (S' : Set (Til O O' B)), IsLocalHom (Til.ι O O' B) → Til.s O O' B ∈ maximalIdeal (Til O O' B) → (∀ a ∈ S, Til.ι O O' B a ∈ S') → Til.s O O' B ∈ S' → GenBy O S → GenBy O' S' := by
  intro O O' _ _ _ _ _ _ _ B _ _ _ _ S S' hloc hs hS hsS hgen N
  let P : Til O O' B → Prop := fun x => ∃ a ∈ Algebra.adjoin O' S', x - a ∈ maximalIdeal (Til O O' B) ^ N
  have Pmem : ∀ x ∈ Algebra.adjoin O' S', P x := fun x hx => ⟨x, hx, by simp⟩
  have Padd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have : x + y - (a + b) = (x - a) + (y - b) := by ring
    rw [this]
    exact add_mem hx hy
  have Pmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    have : x * y - a * b = x * (y - b) + (x - a) * b := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hx)
  have hadj : ∀ a ∈ Algebra.adjoin O S, Til.ι O O' B a ∈ Algebra.adjoin O' S' := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hS x hx)
    | algebraMap r => rw [Til.ι_algebraMap]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hmap : Ideal.map (Til.ι O O' B) (maximalIdeal B ^ N) ≤ maximalIdeal (Til O O' B) ^ N := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (Til.ι O O' B) x hx
  have Pι : ∀ b, P (Til.ι O O' B b) := by
    intro b
    obtain ⟨a, ha, hb⟩ := hgen N b
    refine ⟨_, hadj a ha, ?_⟩
    rw [← map_sub]
    exact hmap (Ideal.mem_map_of_mem _ hb)
  have PC : ∀ t, P (Til.C O O' B t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add (f := _)]; exact Padd _ _ hx hy
    | tmul o b =>
      have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
        PowerSeries.algebraMap_apply
      have e : Til.C O O' B (o ⊗ₜ[O] b) = algebraMap O' (Til O O' B) o * Til.ι O O' B b := by
        rw [h]
        show _ = Til.C O O' B _ * Til.C O O' B ((1 : O') ⊗ₜ[O] b)
        rw [← map_mul]
        congr 1
        simp
      rw [e]
      exact Pmul _ _ (Pmem _ (Subalgebra.algebraMap_mem _ _)) (Pι b)
  have hsA : Til.s O O' B ∈ Algebra.adjoin O' S' := Algebra.subset_adjoin hsS
  have hdec : ∀ f : Til O O' B, ∃ (g : Til O O' B) (c : O' ⊗[O] B), f = Til.s O O' B * g + Til.C O O' B c :=
    fun f => ⟨_, _, PowerSeries.eq_X_mul_shift_add_const (R := O' ⊗[O] B) f⟩
  have key : ∀ (k : ℕ) (f : Til O O' B), ∃ g h, P g ∧ f = g + Til.s O O' B ^ k * h := by
    intro k f
    induction k with
    | zero => exact ⟨0, f, Pmem _ (zero_mem _), by simp⟩
    | succ k ih =>
      obtain ⟨g, h, hg, e⟩ := ih
      obtain ⟨h', c, e'⟩ := hdec h
      refine ⟨g + Til.s O O' B ^ k * Til.C O O' B c, h',
        Padd _ _ hg (Pmul _ _ (Pmem _ (pow_mem hsA k)) (PC c)), ?_⟩
      rw [e, e']
      ring
  intro f
  obtain ⟨g, h, hg, e⟩ := key N f
  rw [e]
  refine Padd _ _ hg ⟨0, zero_mem _, ?_⟩
  rw [sub_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs N)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.GrpQuotBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem span_le_ker {R S : Type} [Ring R] [Ring S] (f : R →+* S) (I : Set R) (h : ∀ x ∈ I, f x = 0) :
    (TwoSidedIdeal.span I).ringCon ≤ RingCon.ker f := by
  intro x y hxy
  rw [RingCon.ker_apply, ← sub_eq_zero, ← map_sub]
  rw [TwoSidedIdeal.rel_iff] at hxy
  have hle : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap f ⊥ := by
    rw [TwoSidedIdeal.span_le]
    intro z hz
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot]
    exact h z hz
  have h1 := hle hxy
  rwa [TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot] at h1

private theorem mk_eq_zero {R : Type} [Ring R] (I : Set R) {x : R} (hx : x ∈ I) :
    (TwoSidedIdeal.span I).ringCon.mk' x = 0 := by
  rw [← map_zero (TwoSidedIdeal.span I).ringCon.mk']
  exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (by simpa using TwoSidedIdeal.subset_span hx))

theorem UpperTheory.V.Pa.BC.grp_quot_bc :
    ∀ (κ κ' G : Type) [Field κ] [Field κ'] [Algebra κ κ'] [Group G] (I : Set (MonoidAlgebra κ G)), Nonempty (κ' ⊗[κ] (TwoSidedIdeal.span I).ringCon.Quotient ≃+* (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap κ κ') '' I)).ringCon.Quotient) := by
  intro κ κ' G _ _ _ _ I
  let φ : MonoidAlgebra κ G →+* MonoidAlgebra κ' G := MonoidAlgebra.mapRingHom G (algebraMap κ κ')
  let J := (TwoSidedIdeal.span I).ringCon
  let J' := (TwoSidedIdeal.span (φ '' I)).ringCon
  let T := κ' ⊗[κ] J.Quotient
  have hφ : ∀ x ∈ I, ((RingCon.mk' J').comp φ) x = 0 := fun x hx =>
    mk_eq_zero _ ⟨x, hx, rfl⟩
  let g0 : J.Quotient →+* J'.Quotient := RingCon.lift J ((RingCon.mk' J').comp φ) (span_le_ker _ _ hφ)
  have hg0 : ∀ x, g0 (RingCon.mk' J x) = RingCon.mk' J' (φ x) := fun x => RingCon.lift_mk' _ x
  let g : J.Quotient →ₐ[κ] J'.Quotient :=
    { g0 with
      commutes' := fun r => by
        change g0 (RingCon.mk' J (algebraMap κ _ r)) = RingCon.mk' J' (algebraMap κ _ r)
        rw [hg0]
        congr 1
        simp [φ, MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single] }
  let α : T →ₐ[κ'] J'.Quotient :=
    Algebra.TensorProduct.lift (Algebra.ofId κ' J'.Quotient) g (fun x y => Algebra.commutes _ _)
  let β : MonoidAlgebra κ' G →ₐ[κ'] T :=
    MonoidAlgebra.lift κ' T G
      { toFun := fun m => (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1)
        map_one' := by
          change (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single 1 1) = 1
          rw [← MonoidAlgebra.one_def, map_one]
          rfl
        map_mul' := fun a b => by
          change (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single (a * b) 1) =
            ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single a 1)) *
              ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single b 1))
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul,
            MonoidAlgebra.single_mul_single, mul_one] }
  have hβs : ∀ (m : G) (c : κ'), β (MonoidAlgebra.single m c) =
      c • ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1)) := by
    intro m c
    rw [MonoidAlgebra.lift_single]
    rfl
  have hβφ : ∀ x, β (φ x) = (1 : κ') ⊗ₜ RingCon.mk' J x := by
    intro x
    have key : (β : MonoidAlgebra κ' G →+* T).comp φ =
        ((Algebra.TensorProduct.includeRight : J.Quotient →ₐ[κ] T) : J.Quotient →+* T).comp (RingCon.mk' J) := by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        simp only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs]
        rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul,
          Algebra.TensorProduct.includeRight_apply]
        congr 1
        change r • ((MonoidAlgebra.single 1 1 : MonoidAlgebra κ G) : J.Quotient) =
          ((MonoidAlgebra.single 1 r : MonoidAlgebra κ G) : J.Quotient)
        rw [← RingCon.coe_smul, MonoidAlgebra.smul_single', mul_one]
      · intro m
        simp only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs, map_one, one_smul]
        rfl
    exact congrArg (fun h => h x) key
  have hβ0 : ∀ y ∈ φ '' I, (β : MonoidAlgebra κ' G →+* T) y = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [RingHom.coe_coe, hβφ, mk_eq_zero I hx, TensorProduct.tmul_zero]
  let β' : J'.Quotient →+* T := RingCon.lift J' (β : MonoidAlgebra κ' G →+* T) (span_le_ker _ _ hβ0)
  have hβ' : ∀ y, β' (RingCon.mk' J' y) = β y := fun y => RingCon.lift_mk' _ y
  let q' : MonoidAlgebra κ' G →ₐ[κ'] J'.Quotient :=
    { RingCon.mk' J' with commutes' := fun _ => rfl }
  have hα : ∀ (a : κ') (q : J.Quotient), α (a ⊗ₜ q) = algebraMap κ' J'.Quotient a * g0 q :=
    fun a q => Algebra.TensorProduct.lift_tmul _ _ _ a q
  have hαβ : ∀ z : J'.Quotient, α (β' z) = z := by
    intro z
    obtain ⟨y, rfl⟩ := RingCon.mk'_surjective J' z
    rw [hβ']
    have key : α.comp β = q' := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        rw [AlgHom.comp_apply, hβs, one_smul, hα, map_one, one_mul, hg0, MonoidAlgebra.mapRingHom_single, map_one]
        rfl
      · exact Subsingleton.elim _ _
    exact congrArg (fun h => h y) key
  have hβα : ∀ t : T, β' (α t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a q =>
      obtain ⟨x, rfl⟩ := RingCon.mk'_surjective J q
      rw [hα, map_mul, hg0]
      change β' (RingCon.mk' J' (algebraMap κ' _ a)) * β' (RingCon.mk' J' (φ x)) = _
      rw [hβ', hβ', AlgHom.commutes, hβφ, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  exact ⟨{ toFun := α, invFun := β', left_inv := hβα, right_inv := hαβ, map_mul' := map_mul α, map_add' := map_add α }⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSMono
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.nonSS_mono :
    ∀ (R R' S G G' : Type) [CommRing R] [CommRing R'] [CommRing S] [Group G] [Group G'] (p : G' →* G) (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R' G')) (φ : R →+* S) (φ' : R' →+* S) (Q : Ideal S), Function.Surjective p → (∀ z ∈ I', MonoidAlgebra.mapDomainRingHom S p (MonoidAlgebra.mapRingHom G' φ' z) ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I)) → NonSS I φ Q → NonSS I' φ' Q := by
  intro R R' S G G' _ _ _ _ _ p I I' φ φ' Q hp hI ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (f.comp φ) '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' (f.comp φ') '' I') with hJ'
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    J.ringCon.mk'.comp (MonoidAlgebra.mapDomainRingHom κ p)
  have hψs : Function.Surjective ψ := by
    have h1 : Function.Surjective (MonoidAlgebra.mapDomainRingHom κ p) := by
      intro x
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact ⟨0, map_zero _⟩
      | add a b ha hb =>
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        exact ⟨a' + b', map_add _ _ _⟩
      | single g c =>
        obtain ⟨g', rfl⟩ := hp g
        exact ⟨MonoidAlgebra.single g' c, by simp⟩
    exact (RingCon.mk'_surjective _).comp h1
  have hcomm : ∀ w : MonoidAlgebra S G',
      MonoidAlgebra.mapDomainRingHom κ p (MonoidAlgebra.mapRingHom G' f w) =
        MonoidAlgebra.mapRingHom G f (MonoidAlgebra.mapDomainRingHom S p w) := by
    intro w
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hcomp : ∀ (T H : Type) [CommRing T] [Group H] (θ : T →+* S) (z : MonoidAlgebra T H),
      MonoidAlgebra.mapRingHom H (f.comp θ) z =
        MonoidAlgebra.mapRingHom H f (MonoidAlgebra.mapRingHom H θ z) := by
    intro T H _ _ θ z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g c => simp
  have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I) ≤
      J.comap (MonoidAlgebra.mapRingHom G f) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, ← hcomp]
    exact TwoSidedIdeal.subset_span ⟨y, hy, rfl⟩
  have hle' : J' ≤ J.comap (MonoidAlgebra.mapDomainRingHom κ p) := by
    rw [hJ', TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hcomp, hcomm, ← TwoSidedIdeal.mem_comap]
    exact hle (hI z hz)
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    have h1 : a - b ∈ J' := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    have h2 := hle' h1
    rw [TwoSidedIdeal.mem_comap, map_sub] at h2
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h2)
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := hψs y
  exact ⟨(x : J'.ringCon.Quotient), rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PsEv
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

open scoped PowerSeries.WithPiTopology in
theorem UpperTheory.V.Pa.BC.ps_ev :
    ∀ (R K : Type) [CommRing R] [CommRing K] (x : R →+* PowerSeries K), ∃ f : PowerSeries R →+* PowerSeries K, (∀ a, f (PowerSeries.C a) = x a) ∧ f PowerSeries.X = PowerSeries.X := by
  intro R K _ _ x
  letI : UniformSpace R := ⊥
  letI : UniformSpace K := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  haveI : DiscreteUniformity K := ⟨rfl⟩
  refine ⟨PowerSeries.eval₂Hom (φ := x) (a := PowerSeries.X) continuous_of_discreteTopology
    PowerSeries.HasEval.X, ?_, ?_⟩
  · intro a
    rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]
end

