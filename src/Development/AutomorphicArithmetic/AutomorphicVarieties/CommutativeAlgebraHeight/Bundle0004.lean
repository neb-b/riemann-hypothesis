module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E']
  (f : E →ₐ[A] E')

private theorem map_eq_lTensor (S : Type) [CommRing S] [Algebra A S] (z : S ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id S S) f z = f.toLinearMap.lTensor S z := by
  induction z with
  | tmul s x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective S (g := f.toLinearMap) hf y
  exact ⟨x, (map_eq_lTensor f S x).trans hx⟩

private theorem eq_of_map_eq (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → x ∈ D.ker)
    (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E)
    (h : Algebra.TensorProduct.map (AlgHom.id S S) f x = Algebra.TensorProduct.map (AlgHom.id S S) f y) :
    D.D S x = D.D S y := by
  have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  have h0 : f.toLinearMap.lTensor S (x - y) = 0 := by
    rw [← map_eq_lTensor, map_sub, h, sub_self]
  obtain ⟨w, hw⟩ := (hex _).1 h0
  have key : ∀ (w : S ⊗[A] (LinearMap.ker f.toLinearMap)) (y : S ⊗[A] E),
      D.D S (y + (LinearMap.ker f.toLinearMap).subtype.lTensor S w) = D.D S y := by
    intro w
    induction w with
    | tmul s k =>
      intro y
      have := (D.mem_ker.1 (hk k.1 k.2)) S y (s ⊗ₜ 1) 1
      simpa using this
    | add a b ha hb => intro y; rw [LinearMap.map_add (f := _), ← add_assoc, hb, ha]
  rw [← key w y, hw, add_sub_cancel]

private theorem map_map_swap (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (g : B →ₐ[A] B')
    (x : B ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id B' B') f (Algebra.TensorProduct.map g (AlgHom.id A E) x) =
      Algebra.TensorProduct.map g (AlgHom.id A E') (Algebra.TensorProduct.map (AlgHom.id B B) f x) := by
  induction x with
  | tmul s x => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end

theorem UpperTheory.V.CA.d_factor :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E →ₐ[A] E'), Function.Surjective f → (∀ x, f x = 0 → x ∈ D.ker) → ∃! D' : Det n A E', D'.pull f = D := by
  intro n A E _ _ _ D E' _ _ f hf hk
  have hs := map_surj f hf
  have he := eq_of_map_eq D f hf hk
  have hσ : ∀ (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] E),
      D.D S (Function.surjInv (hs S) (Algebra.TensorProduct.map (AlgHom.id S S) f x)) = D.D S x :=
    fun S _ _ x => he S _ _ (Function.surjInv_eq _ _)
  let D' : Det n A E' :=
    { D := fun S _ _ =>
        { toFun := fun y => D.D S (Function.surjInv (hs S) y)
          map_one' := by
            rw [← map_one (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, map_one]
          map_mul' := fun x y => by
            obtain ⟨x, rfl⟩ := hs S x
            obtain ⟨y, rfl⟩ := hs S y
            rw [← map_mul (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, hσ, hσ, map_mul] }
      nat := fun B B' _ _ _ _ g x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B' (Function.surjInv (hs B') _) = g (D.D B (Function.surjInv (hs B) _))
        rw [← map_map_swap, hσ, hσ, D.nat]
      homog := fun B _ _ b x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B (Function.surjInv (hs B) _) = b ^ n * D.D B (Function.surjInv (hs B) _)
        rw [← map_smul, hσ, hσ, D.homog] }
  refine ⟨D', Det.ext' fun S _ _ x => hσ S x, fun D'' h => Det.ext' fun S _ _ y => ?_⟩
  obtain ⟨x, rfl⟩ := hs S y
  refine Eq.trans ?_ (hσ S x).symm
  rw [← h]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem determinant_evaluation_aeval {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (B : Type) [CommRing B] [Algebra A B] (b : B) :
    D.D B (1 + (b - 1) ⊗ₜ e) = aeval b (D.D A[X] (1 + (X - 1) ⊗ₜ e)) := by
  rw [← D.nat]
  congr 1
  simp

private theorem coeff_aeval_C_mul_X' {A : Type} [CommRing A] (P : A[X]) (a : A[X]) (j : ℕ) :
    (aeval (Polynomial.C a * Polynomial.X : A[X][X]) P).coeff j = Polynomial.C (P.coeff j) * a ^ j := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, map_add (f := _), add_mul]
  | monomial i c =>
    have e1 : aeval (Polynomial.C a * Polynomial.X : A[X][X]) (monomial i c) =
        Polynomial.C (Polynomial.C c * a ^ i) * Polynomial.X ^ i := by
      rw [aeval_monomial, mul_pow, ← Polynomial.C_pow, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]
      simp [mul_assoc]
    rw [e1, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]

private theorem aeval_C_X_eq_C {A : Type} [CommRing A] (P : A[X]) :
    aeval (Polynomial.C (X : A[X]) : A[X][X]) P = Polynomial.C P := by
  have := Polynomial.aeval_algHom_apply (Polynomial.CAlgHom (R := A) (A := A[X])) (X : A[X]) P
  simpa [Polynomial.aeval_X_left_apply] using this

private theorem pow_aux {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E]
    (D : Det n A E) (e : E) (he : IsIdempotentElem e) :
    ∃ r, D.D A[X] (1 + (X - 1) ⊗ₜ e) = X ^ r := by
  set P := D.D A[X] (1 + (X - 1) ⊗ₜ e) with hP
  have ev : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B), aeval b P = D.D B (1 + (b - 1) ⊗ₜ e) :=
    fun B _ _ b => (determinant_evaluation_aeval D e B b).symm
  have mul : ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B), aeval (s * t) P = aeval s P * aeval t P := by
    intro B _ _ s t
    rw [ev, ev, ev, ← map_mul]
    congr 1
    have key : ∀ u v : B, (1 + u ⊗ₜ[A] e : B ⊗[A] E) * (1 + v ⊗ₜ[A] e) = 1 + (u + v + u * v) ⊗ₜ[A] e := by
      intro u v
      simp only [mul_add, add_mul, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, he.eq, add_tmul]
      abel
    rw [key]
    congr 2
    ring
  have hcoef : ∀ j, Polynomial.C (P.coeff j) * X ^ j = P * Polynomial.C (P.coeff j) := by
    intro j
    have hm := mul A[X][X] (Polynomial.C X) Polynomial.X
    have h1 : (Polynomial.X : A[X][X]) = Polynomial.C 1 * Polynomial.X := by simp
    have cj := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q j) hm
    rw [coeff_aeval_C_mul_X', aeval_C_X_eq_C, Polynomial.coeff_C_mul, h1, coeff_aeval_C_mul_X', one_pow, mul_one] at cj
    exact cj
  have h1 : P.eval 1 = 1 := by
    have := ev A 1
    rw [sub_self, zero_tmul, add_zero, map_one] at this
    rw [← Polynomial.coe_aeval_eq_eval]
    exact this
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (P.coeff j) := by
    by_contra hcon
    push_neg at hcon
    have hmem : P.eval 1 ∈ maximalIdeal A := by
      rw [Polynomial.eval_eq_sum_range]
      refine Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_right _ _ ?_)
      exact (mem_maximalIdeal _).2 (hcon i)
    rw [h1] at hmem
    exact (mem_maximalIdeal _).1 hmem isUnit_one
  refine ⟨j, ?_⟩
  have hu : IsUnit (Polynomial.C (P.coeff j)) := hj.map Polynomial.C
  apply hu.mul_left_cancel
  rw [hcoef j, mul_comm]

theorem UpperTheory.V.CA.d_idem_rank :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E), IsIdempotentElem e → ∃ r ≤ n, D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r := by
  intro n A E _ _ _ _ D e he
  obtain ⟨r, hr⟩ := pow_aux D e he
  obtain ⟨r', hr'⟩ := pow_aux D (1 - e) he.one_sub
  refine ⟨r, ?_, ?_⟩
  · have hz : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
    have step : ∀ a : A[X], (1 + a ⊗ₜ[A] (1 - e) : A[X] ⊗[A] E) * (1 + a ⊗ₜ[A] e) = 1 + a ⊗ₜ[A] (1 : E) := by
      intro a
      rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, hz,
        tmul_zero, add_zero, add_assoc, ← tmul_add, sub_add_cancel]
    have key : (1 + (X - 1) ⊗ₜ[A] (1 - e) : A[X] ⊗[A] E) * (1 + (X - 1) ⊗ₜ[A] e) =
        (X : A[X]) • (1 : A[X] ⊗[A] E) := by
      rw [step, Algebra.TensorProduct.one_def, ← add_tmul, add_sub_cancel, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    have h2 := congrArg (D.D A[X]) key
    rw [map_mul, hr, hr', D.homog, map_one, mul_one, ← pow_add] at h2
    have h3 := congrArg Polynomial.natDegree h2
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h3
    omega
  · have h4 := determinant_evaluation_aeval D e A[X] (1 + X)
    have h5 : (1 + X : A[X]) - 1 = X := by ring
    rw [h5, hr, map_pow, aeval_X] at h4
    exact h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DKerSs
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_ker_ss :
    ∀ {n : ℕ} {k E ι : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[k] Matrix ι ι k), IsSemisimpleRing r.range → ∀ x, x ∈ (Det.ofRep h r).ker ↔ r x = 0 := by
  intro n k E ι _ _ _ _ _ _ h r hss x
  rw [Det.mem_ker]
  constructor
  · intro hx
    obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
      (Ideal.span {(⟨r x, x, rfl⟩ : r.range)})
    have h1 : e ∈ Ideal.span {(⟨r x, x, rfl⟩ : r.range)} := hI ▸ Ideal.subset_span rfl
    have h2 : (⟨r x, x, rfl⟩ : r.range) ∈ Ideal.span {e} := hI ▸ Ideal.subset_span rfl
    obtain ⟨⟨a, u, rfl⟩, ha⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h2
    have ha' : r u * r x = (e : Matrix ι ι k) := congrArg Subtype.val ha
    have hb' : (b : Matrix ι ι k) * (e : Matrix ι ι k) = r x := congrArg Subtype.val hb
    have he' : (e : Matrix ι ι k) * e = e := congrArg Subtype.val he
    have h3 : (Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1)).det = (Det.repS r k 1).det :=
      hx k 1 (1 ⊗ₜ (-u)) 1
    have h4 : Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1) = 1 - (e : Matrix ι ι k) := by
      rw [map_add (f := _), map_mul, map_mul, map_one, Det.repS_tmul, Det.repS_tmul, ← ha']
      simp [sub_eq_add_neg]
    rw [h4, map_one, Matrix.det_one] at h3
    have h5 : IsUnit (1 - (e : Matrix ι ι k)) := by
      rw [Matrix.isUnit_iff_isUnit_det, h3]; exact isUnit_one
    have h6 : (e : Matrix ι ι k) = 0 := by
      apply h5.mul_left_cancel
      rw [sub_mul, one_mul, he', sub_self, mul_zero]
    rw [← hb', h6, mul_zero]
  · intro hx S _ _ y u v
    show (Det.repS r S (y + u * (1 ⊗ₜ x) * v)).det = (Det.repS r S y).det
    rw [map_add (f := _), map_mul, map_mul, Det.repS_tmul, hx]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DKillsPoly
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_kills_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (h : Fin k → E), (∀ a, h a ∈ M) → D.D (MvPolynomial (Fin k) A) (1 + Det.gen h * (1 ⊗ₜ x)) = 1) → D.Kills x := by
  intro n A E _ _ _ D x M hM H B _ _ h
  have key : ∀ e : E, ((1 : B) ⊗ₜ[A] e) ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    intro e
    have he : e ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a y _ hy =>
      rw [tmul_smul, ← algebraMap_smul B]
      exact Submodule.smul_mem _ _ hy
  have hh : h ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    induction h with
    | add a b ha hb => exact add_mem ha hb
    | tmul b e =>
      have : b ⊗ₜ[A] e = b • ((1 : B) ⊗ₜ[A] e) := by simp [smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key e)
  obtain ⟨k, f, g, rfl⟩ := Submodule.mem_span_set'.1 hh
  choose m hm hmg using fun i => (g i).2
  have h1 := D.nat _ B (MvPolynomial.aeval f) (1 + Det.gen m * (1 ⊗ₜ x))
  rw [H k m hm, map_one] at h1
  refine Eq.trans (congrArg _ ?_) h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Det.gen, map_add (f := _), map_mul, map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X,
    AlgHom.id_apply, ← hmg, smul_tmul', smul_eq_mul, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DLiftIdem
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem dli_left_inv {E : Type} [Ring E] {j : E} (hj : j ∈ Ring.jacobson E) :
    ∃ z : E, z * (1 - j) = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hj
  obtain ⟨z, hz⟩ := hj (-1)
  rw [Ideal.mem_bot] at hz
  refine ⟨z, ?_⟩
  rw [← sub_eq_zero, ← hz]
  noncomm_ring

private theorem dli_idem_zero {E : Type} [Ring E] {u : E} (hu : IsIdempotentElem u)
    (hj : u ∈ Ring.jacobson E) : u = 0 := by
  obtain ⟨z, hz⟩ := dli_left_inv hj
  calc u = z * (1 - u) * u := by rw [hz, one_mul]
    _ = 0 := by rw [mul_assoc, sub_mul, one_mul, hu.eq, sub_self, mul_zero]

private theorem dli_mem_max {A B E : Type} [CommRing A] [CommRing B] [Ring E] [Algebra A B] [Algebra A E]
    [Algebra.IsIntegral A E] (ι : B →ₐ[A] E) (hι : Function.Injective ι) {y : B}
    (hy : ι y ∈ Ring.jacobson E) (M : Ideal B) (hM : M.IsMaximal) : y ∈ M := by
  by_contra hyM
  obtain ⟨b, m, hm, hbm⟩ := hM.exists_inv hyM
  have h1 : ι (b * y) ∈ Ring.jacobson E := by
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hy
  obtain ⟨z, hz⟩ := dli_left_inv h1
  have hm' : 1 - ι (b * y) = ι m := by
    rw [← map_one ι, ← map_sub, ← hbm]; simp
  rw [hm'] at hz
  obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := A) z
  have hpow : ∀ i : ℕ, z ^ i * ι m ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ z, pow_succ' (ι m), mul_assoc, ← mul_assoc z, hz, one_mul, ih]
  rw [← aeval_def, aeval_eq_sum_range] at hp0
  have h2 : ι (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • m ^ (p.natDegree - i)) = ι 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, ← zero_mul (ι m ^ p.natDegree), ← hp0, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [map_smul, map_pow, smul_mul_assoc]
    congr 1
    conv_rhs => rw [← Nat.add_sub_cancel' hi', pow_add, ← mul_assoc, hpow, one_mul]
  have h3 := hι h2
  rw [Finset.sum_range_succ, hp.coeff_natDegree, Nat.sub_self, pow_zero, one_smul] at h3
  apply hM.ne_top
  rw [Ideal.eq_top_iff_one, eq_neg_of_add_eq_zero_right h3]
  refine M.neg_mem (M.sum_mem fun i hi => ?_)
  rw [Algebra.smul_def]
  exact M.mul_mem_left _ (M.pow_mem_of_mem hm _ (Nat.sub_pos_of_lt (Finset.mem_range.1 hi)))

private theorem dli_comm {A B F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Ring F] (φ : B →+* F) (x : B)
    (hx : IsIdempotentElem (φ x)) (hy : ∀ M : Ideal B, M.IsMaximal → x - x ^ 2 ∈ M) :
    ∃ e : B, IsIdempotentElem e ∧ φ e = φ x := by
  set K : Ideal B := (maximalIdeal A).map (algebraMap A B) with hK
  haveI : IsAdicComplete K B := GlobalTheory.isAdicComplete_map_of_finite _ B
  have hrad : x - x ^ 2 ∈ K.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hKP, hP⟩
    refine hy P (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) P ?_)
    have : maximalIdeal A = P.under A :=
      (maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.1 hKP)
    rw [← this]; exact maximalIdeal.isMaximal A
  obtain ⟨n, hn⟩ := hrad
  have hn' : (x - x ^ 2) ^ (n + 1) ∈ K := by rw [pow_succ]; exact K.mul_mem_right _ hn
  set a : B := 1 - (1 - x ^ (n + 1)) ^ (n + 1) with ha
  have hφa : φ a = φ x := by
    simp only [ha, map_sub, map_one, map_pow, hx.pow_succ_eq, hx.one_sub.pow_succ_eq, sub_sub_cancel]
  have h0 : a ^ 2 - a ∈ K := by
    have := isIdempotentElem_one_sub_one_sub_pow_pow (Ideal.Quotient.mk K x) (n + 1) (by
      rw [← map_pow, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn')
    rw [← Ideal.Quotient.eq, sq, map_mul]
    simpa [ha] using this.eq
  obtain ⟨e, he, he'⟩ := HenselianRing.is_henselian (I := K) (Polynomial.X ^ 2 - Polynomial.X : B[X])
    (by nontriviality B; monicity!) a (by simpa using h0) (by
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk K (2 * a - 1)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq]
      convert K.mul_mem_left 4 h0 using 1
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one]
      push_cast
      ring)
  have he2 : e * e - e = 0 := by simpa [sq] using he
  refine ⟨e, sub_eq_zero.1 he2, ?_⟩
  have hu : IsUnit ((e - a) * (-(e - a)) + 1) := Ring.mem_jacobson_iff.1 (HenselianRing.jac he') _
  have hk : a ^ 2 - a ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, map_pow, hφa, sq, hx.eq, sub_self]
  have hd : (e - a) * ((e - a) * (-(e - a)) + 1) ∈ RingHom.ker φ := by
    have : (e - a) * ((e - a) * (-(e - a)) + 1) = -(3 * e - a - 1) * (a ^ 2 - a) := by
      linear_combination (-(e + 1 - 3 * a)) * he2
    rw [this]; exact Ideal.mul_mem_left _ _ hk
  rw [Ideal.mul_unit_mem_iff_mem _ hu, RingHom.mem_ker, map_sub, sub_eq_zero] at hd
  rw [hd, hφa]

section

variable {A E F : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A]
  [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] (π : E →ₐ[A] F)

private theorem dli_one (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E) (x : E) (hx : IsIdempotentElem (π x)) :
    ∃ e ∈ Algebra.adjoin A {x}, IsIdempotentElem e ∧ π e = π x := by
  haveI : Module.Finite A (Algebra.adjoin A {x}) :=
    Module.Finite.iff_fg.2 (Algebra.IsIntegral.isIntegral (R := A) x).fg_adjoin_singleton
  obtain ⟨e, he, he'⟩ := dli_comm (A := A) (B := Algebra.adjoin A {x})
    (π.comp (Algebra.adjoin A {x}).val).toRingHom ⟨x, Algebra.self_mem_adjoin_singleton A x⟩ hx
    (dli_mem_max (Algebra.adjoin A {x}).val Subtype.val_injective (hk _ (by
      simp [sq, hx.eq])))
  exact ⟨e, e.2, congrArg Subtype.val he.eq, he'⟩

private theorem dli_orth (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    (e₁ : F) (he₁ : IsIdempotentElem e₁) (e₂ : E) (he₂ : IsIdempotentElem e₂)
    (h₁ : e₁ * π e₂ = 0) (h₂ : π e₂ * e₁ = 0) :
    ∃ e' : E, IsIdempotentElem e' ∧ π e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  obtain ⟨y, rfl⟩ := hs e₁
  have hx : π ((1 - e₂) * y * (1 - e₂)) = π y := by
    simp only [map_mul, map_sub, map_one, sub_mul, mul_sub, one_mul, mul_one, h₁, h₂, zero_mul, sub_zero]
  obtain ⟨e, hm, he, he'⟩ := dli_one π hk ((1 - e₂) * y * (1 - e₂)) (hx ▸ he₁)
  rw [hx] at he'
  have hc0 : Commute e₂ ((1 - e₂) * y * (1 - e₂)) := by
    rw [Commute, SemiconjBy, ← mul_assoc, ← mul_assoc, he₂.mul_one_sub_self, mul_assoc _ (1 - e₂),
      he₂.one_sub_mul_self]
    simp
  have hc : Commute e₂ e := Algebra.commute_of_mem_adjoin_singleton_of_commute hm hc0
  have h0 : e₂ * e = 0 := dli_idem_zero (he₂.mul_of_commute hc he) (hk _ (by rw [map_mul, he', h₂]))
  exact ⟨e, he, he', by rw [← hc.eq, h0], h0⟩

private theorem dli_fin (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E)
    {n : ℕ} {e : Fin n → F} (he : OrthogonalIdempotents e) :
    ∃ e' : Fin n → E, OrthogonalIdempotents e' ∧ π ∘ e' = e := by
  induction n with
  | zero => exact ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n))
    have h₂' (i) : π (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ := dli_orth π hs hk _ (he.idem 0) _ h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

end

theorem UpperTheory.V.CA.d_lift_idem :
    ∀ {A E F ι : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing A] [Ring E] [Algebra A E] [Algebra.IsIntegral A E] [Ring F] [Algebra A F] [Fintype ι] [DecidableEq ι] (π : E →ₐ[A] F), Function.Surjective π → (∀ x, π x = 0 → x ∈ Ring.jacobson E) → ∀ f : ι → F, CompleteOrthogonalIdempotents f → ∃ e : ι → E, CompleteOrthogonalIdempotents e ∧ ∀ i, π (e i) = f i := by
  intro A E F ι _ _ _ _ _ _ _ _ _ _ _ π hs hk f hf
  obtain ⟨e', h₁, h₂⟩ := dli_fin π hs hk
    (hf.toOrthogonalIdempotents.embedding (Fintype.equivFin ι).symm.toEmbedding)
  have ho := h₁.embedding (Fintype.equivFin ι).toEmbedding
  have hv : ∀ i, π ((e' ∘ (Fintype.equivFin ι).toEmbedding) i) = f i := fun i => by
    simpa using congr_fun h₂ (Fintype.equivFin ι i)
  refine ⟨_, ⟨ho, ?_⟩, hv⟩
  have := dli_idem_zero ho.isIdempotentElem_sum.one_sub (hk _ (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, map_sum, Finset.sum_congr rfl fun i _ => hv i, hf.complete, sub_self]))
  exact (sub_eq_zero.1 this).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPoly
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_X_mul_C_X_monomial {A ι : Type} [CommRing A] (d : ι →₀ ℕ) (c : A) :
    MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) (MvPolynomial.monomial d c) =
      X ^ (Finsupp.degree d) * C (MvPolynomial.monomial d c) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod,
    map_pow, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl]
  ring

private theorem scale_coeff {A ι : Type} [CommRing A] (P : MvPolynomial ι A) (k : ℕ) :
    (MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) P).coeff k =
      MvPolynomial.homogeneousComponent k P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [aeval_X_mul_C_X_monomial, Polynomial.coeff_X_pow_mul',
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl), Polynomial.coeff_C]
    split_ifs <;> first | rfl | omega
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq, map_add (f := _)]

theorem UpperTheory.V.CA.d_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {ι : Type} [Fintype ι] (x : ι → E), (D.poly x).IsHomogeneous n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (s : ι → S), D.D S (∑ a, s a ⊗ₜ x a) = MvPolynomial.aeval s (D.poly x) := by
  intro n A E _ _ _ D ι _ x
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S),
      D.D S (∑ a, f (MvPolynomial.X a) ⊗ₜ x a) = f (D.poly x) := by
    intro S _ _ f
    rw [Det.poly, ← D.nat]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum]
  refine ⟨?_, fun S _ _ s => by simpa using key S (MvPolynomial.aeval s)⟩
  let g : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := MvPolynomial.aeval fun a => X * C (MvPolynomial.X a)
  let t : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := IsScalarTower.toAlgHom A (MvPolynomial ι A) (MvPolynomial ι A)[X]
  have h1 := key _ g
  have h3 := key _ t
  have h2 : (∑ a, g (MvPolynomial.X a) ⊗ₜ[A] x a) = (X : (MvPolynomial ι A)[X]) • ∑ a, t (MvPolynomial.X a) ⊗ₜ[A] x a := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [g, t]
  rw [h2, D.homog, h3] at h1
  have hc := congrArg (fun p : (MvPolynomial ι A)[X] => p.coeff n) h1
  simp only [g, t, scale_coeff, IsScalarTower.coe_toAlgHom', Polynomial.coeff_X_pow_mul', le_refl, if_true,
    Nat.sub_self] at hc
  have hP : MvPolynomial.homogeneousComponent n (D.poly x) = D.poly x := by
    rw [← hc]
    simp
  exact hP ▸ MvPolynomial.homogeneousComponent_isHomogeneous n _
end

