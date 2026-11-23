module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DualMFst
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_prod {A : Type} [CommRing A] {n : ℕ} (M : Fin n → Matrix (Fin n) (Fin n) A)
    (h1 : ∀ i a b, b < a → M i a b = 0) (h2 : ∀ i, M i i i = 0) : (List.ofFn M).prod = 0 := by
  have key : ∀ k, k ≤ n → ∀ a b : Fin n, b.val < k → ((List.ofFn M).take k).prod a b = 0 := by
    intro k
    induction k with
    | zero => intro _ a b hb; omega
    | succ k ih =>
      intro hk a b hb
      have hl : k < (List.ofFn M).length := by simp; omega
      rw [List.prod_take_succ _ _ hl, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c.val < k
      · rw [ih (by omega) a c hc, zero_mul]
      · have : (List.ofFn M)[k] c b = 0 := by
          rw [List.getElem_ofFn]
          by_cases hcb : b < c
          · exact h1 _ _ _ hcb
          · have hcb' : c.val ≤ b.val := not_lt.mp hcb
            have e1 : c = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
            have e2 : b = ⟨k, by omega⟩ := Fin.ext (by simp; omega)
            rw [e1, e2]
            exact h2 _
        rw [this, mul_zero]
  ext a b
  have := key n le_rfl a b b.2
  rwa [List.take_of_length_le (by simp)] at this

private theorem kEl_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) (i : Fin n) :
    (kEl u α i).map f = kEl (u.map f) (fun j => f (α j)) i := by
  unfold kEl
  generalize Finset.univ.erase i = t
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, map_mul, map_mul, Matrix.map_mul, ih]
    congr 1
    ext a b
    simp [Matrix.algebraMap_matrix_apply, apply_ite f]

private theorem kS_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) :
    (kS u α).map f = kS (u.map f) (fun j => f (α j)) := by
  ext a b
  simp only [kS, Matrix.map_apply, Matrix.of_apply, ← kEl_map]

private theorem kT_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) :
    (kT u α).map f = kT (u.map f) (fun j => f (α j)) := by
  ext a b
  simp only [kT, Matrix.map_apply, Matrix.of_apply, ← kEl_map]

private theorem fst_mul' {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) (DualNumber X)) :
    (A * B).map TrivSqZeroExt.fst = A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.fst := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem snd_mul' {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) (DualNumber X)) :
    (A * B).map TrivSqZeroExt.snd =
      A.map TrivSqZeroExt.snd * B.map TrivSqZeroExt.fst + A.map TrivSqZeroExt.fst * B.map TrivSqZeroExt.snd := by
  ext a b
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, ← Finset.sum_add_distrib, add_comm, mul_comm]

private theorem dualM_fst {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) X) :
    (dualM A B).map TrivSqZeroExt.fst = A := by
  ext a b
  simp [dualM]

private theorem dualM_snd {X : Type} [CommRing X] {n : ℕ} (A B : Matrix (Fin n) (Fin n) X) :
    (dualM A B).map TrivSqZeroExt.snd = B := by
  ext a b
  simp [dualM]

theorem UpperTheory.V.Th.Coc.flag :
    ∀ {O H : Type} [CommRing O] [IsDomain O] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) O) (ψ : Fin n → H → O) (s : H), (∀ g a b, b < a → r g a b = 0) → (∀ g i, r g i i = ψ i g) → (Function.Injective fun i => ψ i s) → ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (D : H → Matrix (Fin n) (Fin n) X) (a : Fin n → H → X), (∀ g : Fin n → H, (List.ofFn fun i => dualM (bar X (r (g i))) (D (g i)) - (TrivSqZeroExt.inl (algebraMap O X (ψ i (g i))) + TrivSqZeroExt.inr (a i (g i)) : DualNumber X) • (1 : Matrix (Fin n) (Fin n) (DualNumber X))).prod = 0) → ∃ Y : Matrix (Fin n) (Fin n) X, ∀ g, (∀ i j, j < i → (c₁ • D g - (bar X (r g) * Y - Y * bar X (r g))) i j = 0) ∧ ∀ i, (c₁ • D g - (bar X (r g) * Y - Y * bar X (r g))) i i = c₁ • a i g := by
  intro O H _ _ n r ψ s htri hdiag hinj
  have hrel : ∀ g : Fin n → H,
      (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) O)).prod = 0 := by
    intro g
    apply tri_prod
    · intro i a b hab
      simp [htri _ a b hab, Matrix.one_apply_ne hab.ne']
    · intro i
      simp [hdiag]
  obtain ⟨hoff, -⟩ := flagA r ψ s hrel
  obtain ⟨hB1, hB2⟩ := flagB (r s) (fun i => ψ i s) (htri s) (hdiag s)
  set S := kS (r s) (fun i => ψ i s) with hS
  set T := kT (r s) (fun i => ψ i s) with hT
  set Δ : Fin n → O := fun i => ∏ j ∈ Finset.univ.erase i, (ψ i s - ψ j s) with hΔ
  have hΔ0 : ∀ i, Δ i ≠ 0 := by
    intro i
    refine Finset.prod_ne_zero_iff.mpr fun j hj h => ?_
    exact (Finset.ne_of_mem_erase hj) (hinj (sub_eq_zero.mp h)).symm
  have hST : ∀ i, (S * T) i i = Δ i * Δ i := by
    intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hB2 i).1, (hB2 i).2]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [(hB1 i b h).1, zero_mul]
      · rw [(hB1 b i h).2, mul_zero]
    · simp
  obtain ⟨c₁, hc₁, hC⟩ := flagC S T Δ hΔ0 hB1 hB2 hoff
  refine ⟨c₁, hc₁, fun X _ _ D a hD => ?_⟩
  obtain ⟨h1, h2⟩ := flagA (fun g => dualM (bar X (r g)) (D g))
    (fun i g => (TrivSqZeroExt.inl (algebraMap O X (ψ i g)) + TrivSqZeroExt.inr (a i g) : DualNumber X)) s hD
  have eS := kS_map (TrivSqZeroExt.fstHom X X X).toRingHom (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X))
  have eT := kT_map (TrivSqZeroExt.fstHom X X X).toRingHom (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X))
  set S' := kS (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X)) with hS'
  set T' := kT (dualM (bar X (r s)) (D s))
    (fun i => (TrivSqZeroExt.inl (algebraMap O X (ψ i s)) + TrivSqZeroExt.inr (a i s) : DualNumber X)) with hT'
  have hf : ⇑(TrivSqZeroExt.fstHom X X X).toRingHom = TrivSqZeroExt.fst := rfl
  have fS : S'.map TrivSqZeroExt.fst = bar X S := by
    rw [hf] at eS
    rw [eS, dualM_fst, hS, bar, bar, kS_map]
    simp
  have fT : T'.map TrivSqZeroExt.fst = bar X T := by
    rw [hf] at eT
    rw [eT, dualM_fst, hT, bar, bar, kT_map]
    simp
  have e1 : (S' * T').map TrivSqZeroExt.snd =
      S'.map TrivSqZeroExt.snd * bar X T + bar X S * T'.map TrivSqZeroExt.snd := by
    rw [snd_mul', fS, fT]
  have e2 : ∀ g, (S' * dualM (bar X (r g)) (D g) * T').map TrivSqZeroExt.snd =
      S'.map TrivSqZeroExt.snd * bar X (r g) * bar X T + bar X S * D g * bar X T +
        bar X S * bar X (r g) * T'.map TrivSqZeroExt.snd := by
    intro g
    rw [snd_mul', snd_mul', fst_mul', fS, fT, dualM_fst, dualM_snd, add_mul]
  have e3 : ∀ i, ((S' * T') i i).fst = algebraMap O X (Δ i * Δ i) := by
    intro i
    have : (S' * T').map TrivSqZeroExt.fst = bar X (S * T) := by
      rw [fst_mul', fS, fT, bar, bar, bar, Matrix.map_mul]
    have h := congrFun (congrFun this i) i
    rw [← hST]
    exact h
  obtain ⟨Y, hY⟩ := hC X (S'.map TrivSqZeroExt.snd) (T'.map TrivSqZeroExt.snd) (by
    intro a b hab
    rw [← e1, Matrix.map_apply, h1 a b hab, TrivSqZeroExt.snd_zero])
  refine ⟨Y, fun g => hY (r g) (D g) (fun i => a i g) (htri g) ?_ ?_⟩
  · intro i j hij
    rw [← e2, Matrix.map_apply, (h2 g).1 i j hij, TrivSqZeroExt.snd_zero]
  · intro i
    rw [← e2, ← e1, Matrix.map_apply, Matrix.map_apply, (h2 g).2 i, TrivSqZeroExt.snd_mul, e3, hdiag]
    generalize ((S' * T') i i).snd = z
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Imports
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.kill :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [IsDomain O] {G : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → (∀ y, (repR x ρ y).trace = x (τ y)) → IsLift x δ (repR x ρ) τ c d → ∀ y, (∀ g, τ ((MonoidAlgebra.single g 1) * y) = 0) → repR x ρ y = 0 ∧ c₀ • d y = 0 := by
  intro O R X _ _ _ _ _ n _ G _ x δ ρ τ c c₀ d hc₀ hspan htr hd y hy
  obtain ⟨k1, k2⟩ := kill0 ρ c₀ hc₀ hspan
  have hs : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have h1 : repR x ρ y = 0 := by
    apply k1
    intro g
    rw [← hs, ← map_mul, htr, hy, map_zero]
  refine ⟨h1, k2 X (d y) ?_⟩
  intro g
  have e := hd.mul (MonoidAlgebra.single g 1) y
  rw [h1, hs] at e
  have hb0 : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
    ext i j
    simp [bar]
  rw [hb0, Matrix.mul_zero, zero_add] at e
  rw [← e, hd.tr, hy, map_zero, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftSurj
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lift_surj {B E E' P : Type} [CommRing B] [Ring E] [Ring E'] [Ring P] [Algebra B E] [Algebra B E']
    [Algebra B P] (q : E →ₐ[B] E') (hq : Function.Surjective q) (ρ : E →ₐ[B] P) (h : ∀ x, q x = 0 → ρ x = 0) :
    ∃ π : E' →ₐ[B] P, ∀ x, π (q x) = ρ x := by
  have key : ∀ x y, q x = q y → ρ x = ρ y := fun x y hxy =>
    sub_eq_zero.1 (by rw [← map_sub]; exact h _ (by rw [map_sub, hxy, sub_self]))
  choose s hs using hq
  have hq' : ∀ x, ρ (s (q x)) = ρ x := fun x => key _ _ (hs _)
  refine ⟨⟨⟨⟨⟨fun y => ρ (s y), ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, fun r => ?_⟩, hq'⟩
  · rw [← map_one q, hq', map_one]
  · change ρ (s (a * b)) = ρ (s a) * ρ (s b)
    rw [← map_mul]
    exact key _ _ (by rw [map_mul, hs, hs, hs])
  · change ρ (s 0) = 0
    rw [← map_zero q, hq', map_zero]
  · change ρ (s (a + b)) = ρ (s a) + ρ (s b)
    rw [← map_add (f := _)]
    exact key _ _ (by rw [map_add (f := _), hs, hs, hs])
  · change ρ (s (algebraMap B E' r)) = _
    rw [← q.commutes, hq', ρ.commutes]

theorem UpperTheory.V.Th.Coc.gma :
    ∀ {n : ℕ} {O R G : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Group G] (D : GDet n R G) (χ : Fin n → G →* (ResidueField O)ˣ), 1 ≤ n → Function.Injective χ → D.map (res O R : R →+* ResidueField O) = GDet.ofRep (diagRep χ) → ∃ (E : Type) (_ : Ring E) (_ : Algebra R E) (π : MonoidAlgebra R G →ₐ[R] E) (τ : E →ₗ[R] R) (e : Fin n → E), Function.Surjective π ∧ (∀ y, τ (π y) = D.tr y) ∧ IsTrGMA τ e := by
  intro n O R G _ _ _ _ _ _ D χ hn hχ hred
  obtain ⟨E, _, _, q, DE, hsurj, hDE, hCH, -⟩ := chQuot D.toDet
  obtain ⟨π0, hs0, -, -, hchi0⟩ := CA.f_chars χ hχ
  letI : Algebra R (ResidueField O) := (res O R : R →+* ResidueField O).toAlgebra
  have hal : algebraMap R (ResidueField O) = (res O R : R →+* ResidueField O) := rfl
  let ρ : MonoidAlgebra R G →ₐ[R] (Fin n → ResidueField O) :=
    (π0.restrictScalars R).comp (MonoidAlgebra.mapAlgHom G (Algebra.ofId R (ResidueField O)))
  have hρ : ∀ x, ρ x = π0 (MonoidAlgebra.mapRingHom G (res O R : R →+* ResidueField O) x) := fun x => rfl
  have hchi : ∀ x, (DE.chi (q x)).map (res O R : R →+* ResidueField O) = ∏ i, (Polynomial.X - Polynomial.C (ρ x i)) := fun x => by
    rw [← (CA.d_pull DE q).1, hDE, (CA.d_toDet D x).1, ← ((CA.d_gmap D).2.2.1 (res O R : R →+* ResidueField O) x).1, hred, hρ]
    exact hchi0 _
  have hker : ∀ x, q x = 0 → ρ x = 0 := fun x hx => by
    have h1 := hchi x
    rw [hx, ← map_zero q, hchi 0, map_zero] at h1
    funext i
    have h2 := congrArg (Polynomial.eval (ρ x i)) h1
    rw [Polynomial.eval_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero (f := fun j => Polynomial.eval (ρ x i) (Polynomial.X - Polynomial.C (ρ x j)))
      (Finset.mem_univ i) (by simp)] at h2
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2
    simpa using hj
  obtain ⟨π, hπ⟩ := lift_surj q hsurj ρ hker
  have hmap : ∀ y : MonoidAlgebra (ResidueField O) G, ∃ x, MonoidAlgebra.mapRingHom G (res O R : R →+* ResidueField O) x = y := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | single g r =>
      obtain ⟨c, rfl⟩ := residue_surjective r
      exact ⟨MonoidAlgebra.single g (algebraMap O R c), (MonoidAlgebra.mapRingHom_single _ _ _).trans
        (congrArg _ ((res O R).commutes c))⟩
  have hπs : Function.Surjective π := fun v => by
    obtain ⟨y, rfl⟩ := hs0 v
    obtain ⟨x, rfl⟩ := hmap y
    exact ⟨q x, by rw [hπ, hρ]⟩
  have hchiE : ∀ x, (DE.chi x).map (algebraMap R (ResidueField O)) = ∏ i, (Polynomial.X - Polynomial.C (π x i)) := fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hπ, hal, hchi]
  haveI : IsLocalHom (algebraMap R (ResidueField O)) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero ((res_eq_zero_iff O R a).2 hn)⟩
  obtain ⟨-, e, he, -⟩ := CA.f_gma DE π hCH hπs hchiE
  obtain ⟨h1, h2, -⟩ := CA.d_tr DE
  obtain ⟨t, ht⟩ := h1 hn
  have hc := fun i => CA.d_corner DE (e i) he.ch (he.idem.idem i) (he.rank i) hn
  refine ⟨E, _, _, q, t, e, hsurj, fun y => ?_, fun a b => ?_, he.idem, fun i a => ?_, fun i => ?_⟩
  · rw [ht, ← (CA.d_toDet D y).2.2.1, ← hDE]
    unfold Det.tr Det.lam
    rw [(CA.d_pull DE q).1]
  · rw [ht, ht]
    exact h2 1 a b
  · rw [ht]
    exact (hc i).1 a
  · rw [ht]
    exact (hc i).2.1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Polar
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (t : MonoidAlgebra R F.G₀ →ₗ[R] R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X), ((P : Matrix (Fin n) (Fin n) O)ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) O)ᵀ = -P) → F.IsForm O n ρ P → (∀ g, t (F.star O R n (MonoidAlgebra.single g 1)) = t (MonoidAlgebra.single g 1)) → IsLift x δ (repR x (mat ρ)) t c d → ∃ d' : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x (mat ρ)) t (2 * c) d' ∧ ∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d' (F.star O R n a) = (d' a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P t c d hP hF ht hd
  obtain ⟨hsm, hsa, hsr, hss, -, hsρ⟩ := starFacts F (O := O) (R := R) (n := n)
  have hρs := hsρ x ρ P hF
  obtain ⟨ε, hεε, hPt⟩ : ∃ ε : O, ε * ε = 1 ∧
      (P : Matrix (Fin n) (Fin n) O)ᵀ = ε • (P : Matrix (Fin n) (Fin n) O) := by
    rcases hP with h | h
    · exact ⟨1, one_mul 1, by rw [h, one_smul]⟩
    · exact ⟨-1, by ring, by rw [h, neg_one_smul]⟩
  have hmap : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B :=
    fun A B => Matrix.map_mul
  set Pb := bar X (P : Matrix (Fin n) (Fin n) O) with hPb
  set Q := bar X ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) with hQ
  set e : X := algebraMap O X ε with he
  have hQP : Q * Pb = 1 := by
    rw [hQ, hPb, ← hmap, Units.inv_mul]
    simp [bar]
  have hPQ : Pb * Q = 1 := by
    rw [hQ, hPb, ← hmap, Units.mul_inv]
    simp [bar]
  have hQP' : ∀ M, Q * (Pb * M) = M := fun M => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPQ' : ∀ M, Pb * (Q * M) = M := fun M => by rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hee : e * e = 1 := by rw [he, ← map_mul, hεε, map_one]
  have hPbt : Pbᵀ = e • Pb := by
    ext i j
    have h := congrFun (congrFun hPt i) j
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp [hPb, bar, Matrix.transpose_apply, h, map_mul, he]
  have hQt : Qᵀ = e • Q := by
    have h0 : e • (Pb * Qᵀ) = 1 := by
      rw [← Matrix.smul_mul, ← hPbt, ← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h1 : Pb * Qᵀ = e • 1 := by
      calc Pb * Qᵀ = (e * e) • (Pb * Qᵀ) := by rw [hee, one_smul]
        _ = e • 1 := by rw [mul_smul, h0]
    calc Qᵀ = Q * (Pb * Qᵀ) := by rw [hQP']
      _ = e • Q := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
  have hρ : ∀ a, bar X (repR x (mat ρ) (F.star O R n a)) =
      Q * (bar X (repR x (mat ρ) a))ᵀ * Pb := by
    intro a
    rw [hρs, hmap, hmap]
    rfl
  have hρT : ∀ a, (bar X (repR x (mat ρ) (F.star O R n a)))ᵀ =
      Pb * bar X (repR x (mat ρ) a) * Q := by
    intro a
    rw [hρ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hPbt, hQt]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc]
  let eD : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X :=
    AddMonoidHom.mk' (fun a => Q * (d (F.star O R n a))ᵀ * Pb) (by
      intro a b
      simp only [hsa, map_add (f := _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul])
  have heD : ∀ a, eD a = Q * (d (F.star O R n a))ᵀ * Pb := fun a => rfl
  have h0 : F.star O R n 0 = 0 := by simpa using hsr 0 0
  have htS : ∀ a, t (F.star O R n a) = t a := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [h0]
    | add a b ha hb => rw [hsa, map_add (f := _), map_add (f := _), ha, hb]
    | single g r =>
      have hs : (MonoidAlgebra.single g r : MonoidAlgebra R F.G₀) = r • MonoidAlgebra.single g 1 := by
        rw [MonoidAlgebra.smul_single', mul_one]
      rw [hs, hsr, map_smul, map_smul, ht]
  refine ⟨d + eD, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b
    simp only [AddMonoidHom.add_apply, heD, hd.mul, hsm, Matrix.transpose_add, Matrix.transpose_mul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hQP', hQP, Matrix.mul_one]
    abel
  · intro r a
    simp only [AddMonoidHom.add_apply, heD, hd.smul, hsr, Matrix.transpose_add, Matrix.transpose_smul,
      hρT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hQP',
      hQP, Matrix.mul_one, smul_add, two_mul, add_smul]
    abel
  · intro a
    rw [AddMonoidHom.add_apply, Matrix.trace_add, hd.tr, heD, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hPQ, Matrix.one_mul, Matrix.trace_transpose, hd.tr, htS, two_mul, add_smul]
  · intro a
    simp only [AddMonoidHom.add_apply, heD, hss, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPbt, hQt, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc, hPQ', hPQ, hQP, hQP', Matrix.mul_one]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.ZOf
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.zOf :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} [Algebra ℤ_[l] O] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O) (τ : MonoidAlgebra R F.G₀ → R) (c : O) (d : MonoidAlgebra R F.G₀ →+ Matrix (Fin n) (Fin n) X) (z : F.G₀ → Matrix (Fin n) (Fin n) X), IsDer x δ → F.IsForm O n ρ P → IsLift x δ (repR x (mat ρ)) τ c d → (∀ a, bar X (P : Matrix (Fin n) (Fin n) O) * d (F.star O R n a) = (d a)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) → (∀ g, z g = d (MonoidAlgebra.single g 1) * bar X (mat ρ g⁻¹)) → d 1 = 0 ∧ (∀ g g', z (g * g') = z g + bar X (mat ρ g) * z g' * bar X (mat ρ g⁻¹)) ∧ (∀ g, bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g) = -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O))) ∧ ∀ g, (z g * bar X (mat ρ g)).trace = c • δ (τ (MonoidAlgebra.single g 1)) := by
  intro l _ F O R X _ _ _ _ _ n _ x δ ρ P τ c d z hδ hF hL hst hz
  have bmul : ∀ A B : Matrix (Fin n) (Fin n) O, bar X (A * B) = bar X A * bar X B := fun A B => Matrix.map_mul
  have bone : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have bsm : ∀ (e : O) (A : Matrix (Fin n) (Fin n) O), bar X (e • A) = e • bar X A := by
    intro e A
    ext i j
    show algebraMap O X (e * A i j) = e • algebraMap O X (A i j)
    rw [map_mul, Algebra.smul_def]
  have rmul : ∀ g g', bar X (mat ρ (g * g')) = bar X (mat ρ g) * bar X (mat ρ g') := by
    intro g g'
    rw [map_mul, bmul]
  have rinv : ∀ g, bar X (mat ρ g⁻¹) * bar X (mat ρ g) = 1 := by
    intro g
    rw [← rmul, inv_mul_cancel, map_one, bone]
  have rinv' : ∀ g, bar X (mat ρ g) * bar X (mat ρ g⁻¹) = 1 := by
    intro g
    rw [← rmul, mul_inv_cancel, map_one, bone]
  have d1 : d 1 = 0 := by
    have h := hL.mul 1 1
    rw [mul_one, map_one (repR x (mat ρ)), bone, mul_one, one_mul] at h
    exact left_eq_add.mp h
  have δ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, map_one x, one_smul] at h
    exact left_eq_add.mp h
  have δa : ∀ e : O, δ (algebraMap O R e) = 0 := by
    intro e
    rw [Algebra.algebraMap_eq_smul_one, map_smul, δ1, smul_zero]
  have dmul : ∀ g g', d (MonoidAlgebra.single (g * g') 1) =
      d (MonoidAlgebra.single g 1) * bar X (mat ρ g') + bar X (mat ρ g) * d (MonoidAlgebra.single g' 1) := by
    intro g g'
    have h := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single g' 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, repR_single, repR_single, map_one, one_smul, one_smul] at h
    exact h
  have hd : ∀ g, d (MonoidAlgebra.single g 1) = z g * bar X (mat ρ g) := by
    intro g
    rw [hz, mul_assoc, rinv, mul_one]
  have dinv : ∀ g, d (MonoidAlgebra.single g⁻¹ 1) = -(bar X (mat ρ g⁻¹) * z g) := by
    intro g
    have h := dmul g⁻¹ g
    rw [inv_mul_cancel, ← MonoidAlgebra.one_def, d1] at h
    have h2 := congrArg (· * bar X (mat ρ g⁻¹)) h
    simp only [zero_mul, add_mul, mul_assoc, rinv', mul_one] at h2
    rw [hz]
    exact eq_neg_of_add_eq_zero_left h2.symm
  refine ⟨d1, ?_, ?_, ?_⟩
  · intro g g'
    rw [hz (g * g'), dmul, _root_.mul_inv_rev, rmul, hz g, hz g', add_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (bar X (mat ρ g')), rinv', one_mul]
  · intro g
    have h := hst (MonoidAlgebra.single g 1)
    rw [(starFacts F (O := O) (R := R) (n := n)).2.2.2.2.1 g] at h
    have hf := congrArg (bar X) (hF g)
    generalize ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) = e at h hf
    have hs : (MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R e) : MonoidAlgebra R F.G₀) =
        algebraMap O R e • MonoidAlgebra.single (F.conj g)⁻¹ 1 := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hs, hL.smul, δa, smul_zero, zero_smul, add_zero, AlgHom.commutes, dinv, hd, transpose_mul] at h
    rw [bmul, bmul, bsm] at hf
    have ht : bar X (mat ρ g)ᵀ = (bar X (mat ρ g))ᵀ := rfl
    rw [ht] at hf
    have hf2 : (bar X (mat ρ g))ᵀ * bar X (P : Matrix (Fin n) (Fin n) O) =
        e • (bar X (P : Matrix (Fin n) (Fin n) O) * bar X (mat ρ (F.conj g)⁻¹)) := by
      rw [← smul_mul_assoc, ← hf, mul_assoc, rinv', mul_one]
    have h3 : (bar X (mat ρ g))ᵀ * (bar X (P : Matrix (Fin n) (Fin n) O) * z (F.conj g)) =
        (bar X (mat ρ g))ᵀ * -((z g)ᵀ * bar X (P : Matrix (Fin n) (Fin n) O)) := by
      rw [mul_neg, ← mul_assoc, ← mul_assoc, ← h, hf2]
      simp [mul_assoc]
    have h4 : (bar X (mat ρ g⁻¹))ᵀ * (bar X (mat ρ g))ᵀ = 1 := by
      rw [← transpose_mul, rinv', transpose_one]
    have h5 := congrArg ((bar X (mat ρ g⁻¹))ᵀ * ·) h3
    simp only [← mul_assoc _ (bar X (mat ρ g))ᵀ, h4, one_mul] at h5
    exact h5
  · intro g
    rw [← hd, hL.tr]
end

