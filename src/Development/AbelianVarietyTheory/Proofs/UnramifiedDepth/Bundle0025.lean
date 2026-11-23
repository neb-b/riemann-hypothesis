module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0029
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NsmulFAddSqZeroEq
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma fgInv_span_le_nil {S ι : Type} [CommRing S] (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    Ideal.span (Set.range a) ≤ nilradical S := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_nilradical.2 (ha i)

private lemma fgInv_elim_nil {S ι κ : Type} [CommRing S] (a : ι → S) (b : κ → S)
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i, IsNilpotent (Sum.elim a b i) := by
  rintro (i | i)
  · exact ha i
  · exact hb i

private lemma fgInv_det_unit {S : Type} [CommRing S] {g : ℕ} (M : Matrix (Fin g) (Fin g) S)
    (hM : ∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ nilradical S) : IsUnit M.det := by
  have h1 : (Ideal.Quotient.mk (nilradical S)).mapMatrix M =
      (Ideal.Quotient.mk (nilradical S)).mapMatrix 1 := by
    ext k j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (hM k j)
  have h2 : Ideal.Quotient.mk (nilradical S) M.det = Ideal.Quotient.mk (nilradical S) 1 := by
    rw [RingHom.map_det, h1, map_one, Matrix.det_one, map_one]
  have h3 : IsNilpotent (M.det - 1) := mem_nilradical.1 (Ideal.Quotient.eq.1 h2)
  have h4 := h3.isUnit_add_one
  simpa using h4

private lemma fgInv_mulVec_sq {S : Type} [CommRing S] {g : ℕ} (N : Matrix (Fin g) (Fin g) S)
    (e : Fin g → S) (he : ∀ i j, e i * e j = 0) : ∀ i j, (N *ᵥ e) i * (N *ᵥ e) j = 0 := by
  intro i j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  rw [mul_mul_mul_comm, he, mul_zero]

private lemma fgInv_mulVec_eq {S : Type} [CommRing S] {g : ℕ} (M : Matrix (Fin g) (Fin g) S)
    (v u : Fin g → S) (hvu : ∀ i j, v i * u j = 0)
    (hM : ∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range v)) :
    M *ᵥ u = u := by
  have h : (M - 1) *ᵥ u = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have key : ∀ x ∈ Ideal.span (Set.range v), x * u j = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun l _ => by rw [mul_assoc, hvu, mul_zero]
    exact key _ (hM k j)
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h

theorem nsmulF_add_sqZero_eq :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) := by
  intro H1 H2 R₀ _ g B K ch n S _ _ hn a e ha he
  have h0 : ∀ i : Fin g, IsNilpotent ((0 : Fin g → S) i) := fun _ => IsNilpotent.zero
  have hnil : ∀ x y : Fin g → S, (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) →
      ∀ i, IsNilpotent (fAdd ch.F x y i) := by
    intro x y hx hy k
    have hxy := fgInv_elim_nil x y hx hy
    have h00 := fgInv_elim_nil (0 : Fin g → S) (0 : Fin g → S) h0 h0
    have e1 := fgInv_span_le_nil _ hxy (((H1 (ch.F k) S (Sum.elim x y)).2 hxy).2)
    have e2 := fgInv_span_le_nil _ h00 (((H1 (ch.F k) S (Sum.elim 0 0)).2 h00).2)
    have e3 : nEval (ch.F k) (Sum.elim (0 : Fin g → S) (0 : Fin g → S)) = 0 :=
      congrFun (ch.F_unit S 0 h0) k
    rw [e3] at e2
    have e4 := (nilradical S).sub_mem e1 e2
    rw [sub_sub_sub_cancel_right, sub_zero] at e4
    exact mem_nilradical.1 e4
  have hns : ∀ x : Fin g → S, (∀ i, IsNilpotent (x i)) → ∀ m,
      ∀ i, IsNilpotent (nsmulF ch.F x m i) := by
    intro x hx m
    induction m with
    | zero => exact h0
    | succ m ih => exact hnil _ _ ih hx
  have hdist : ∀ x y : Fin g → S, (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) → ∀ m,
      nsmulF ch.F (fAdd ch.F x y) m = fAdd ch.F (nsmulF ch.F x m) (nsmulF ch.F y m) := by
    intro x y hx hy m
    induction m with
    | zero => exact (ch.F_unit S 0 h0).symm
    | succ m ih =>
      have hX := hns x hx m
      have hY := hns y hy m
      show fAdd ch.F (nsmulF ch.F (fAdd ch.F x y) m) (fAdd ch.F x y) =
        fAdd ch.F (fAdd ch.F (nsmulF ch.F x m) x) (fAdd ch.F (nsmulF ch.F y m) y)
      rw [ih, ch.F_assoc S _ _ _ hX hY (hnil _ _ hx hy),
        ch.F_assoc S _ _ _ hX hx (hnil _ _ hY hy),
        ← ch.F_assoc S _ _ _ hY hx hy, ← ch.F_assoc S _ _ _ hx hY hy, ch.F_comm S _ _ hY hx]
  obtain ⟨M, hM, hMe⟩ := H2 ch S a ha
  have hdet : IsUnit M.det :=
    fgInv_det_unit M fun k j => fgInv_span_le_nil a ha (hM k j)
  set u : Fin g → S := M⁻¹ *ᵥ e with hu
  have huu : ∀ i j, u i * u j = 0 := fgInv_mulVec_sq _ e he
  have hun : ∀ i, IsNilpotent (u i) := fun i => ⟨2, by rw [pow_two, huu]⟩
  have hau : fAdd ch.F a u = a + e := by
    rw [hMe u huu, hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hmu : ∀ m : ℕ, nsmulF ch.F u m = (m : S) • u := by
    intro m
    induction m with
    | zero => simp [nsmulF]
    | succ m ih =>
      show fAdd ch.F (nsmulF ch.F u m) u = _
      obtain ⟨N, hN, hNe⟩ := H2 ch S (nsmulF ch.F u m) (hns u hun m)
      rw [hNe u huu, fgInv_mulVec_eq N _ u _ hN, ih, Nat.cast_succ, add_smul, one_smul]
      intro i j
      rw [ih, Pi.smul_apply, smul_eq_mul, mul_assoc, huu, mul_zero]
  rw [← hau, hdist a u ha hun, hmu, hn, zero_smul, ch.F_unit S _ (hns a ha n)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PSerFrobOfInvariance
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma pSerOf_trunc {R₀ : Type} [CommRing R₀] {g : ℕ} (N : ℕ) (G₁ : MvPolynomial (Fin g) R₀) :
    ∃ G : MvPolynomial (Fin g) R₀,
      (∀ m, AddMonoidAlgebra.coeff G m = if ∀ i, m i < N then AddMonoidAlgebra.coeff G₁ m else 0) ∧
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
        MvPolynomial.aeval a G = MvPolynomial.aeval a G₁ := by
  classical
  refine ⟨∑ m ∈ G₁.support.filter (fun m => ∀ i, m i < N),
    MvPolynomial.monomial m (AddMonoidAlgebra.coeff G₁ m), ?_, ?_⟩
  · intro m
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases h : ∀ i, m i < N
    · by_cases h0 : AddMonoidAlgebra.coeff G₁ m = 0
      · simp [h0]
      · simp [h, h0]
    · rw [if_neg h, if_neg]
      intro hm
      exact h (Finset.mem_filter.1 hm).2
  · intro S _ _ a ha
    conv_rhs => rw [G₁.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hz : ∏ j, a j ^ m j = 0 :=
        Finset.prod_eq_zero (f := fun j => a j ^ m j) (Finset.mem_univ i)
          (pow_eq_zero_of_le hi (ha i))
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), hz, mul_zero]

theorem pSerFrob_of_invariance :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g N : ℕ) (G : MvPolynomial (Fin g) R₀),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S], (p : S) = 0 → ∀ a e : Fin g → S, (∀ i, a i ^ N = 0) → (∀ i j, e i * e j = 0) →
      MvPolynomial.aeval (a + e) G = MvPolynomial.aeval a G) →
    ∀ m : Fin g →₀ ℕ, (∀ i, m i < N) → (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff G m = p * r) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) := by
  intro hev hinv hcoef R₀ _ p _ g B K ch N
  classical

  have hnil : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S),
      (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (fAdd ch.F a b k) := by
    intro S _ _ a b ha hb k
    have h0 : algebraMap R₀ S (MvPowerSeries.coeff 0 (ch.F k)) = 0 := by
      have h1 := ((hev (ch.F k) S (Sum.elim (0 : Fin g → S) (0 : Fin g → S))).2
        (by rintro (i | i) <;> simp)).2
      have h2 : nEval (ch.F k) (Sum.elim (0 : Fin g → S) (0 : Fin g → S)) = 0 :=
        congrFun (ch.F_unit S 0 (by simp)) k
      have h3 : Ideal.span (Set.range (Sum.elim (0 : Fin g → S) (0 : Fin g → S))) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro _ ⟨i | i, rfl⟩ <;> simp
      rw [h2, h3, Ideal.mem_bot, zero_sub, neg_eq_zero] at h1
      exact h1
    have h1 := ((hev (ch.F k) S (Sum.elim a b)).2 (by rintro (i | i); exacts [ha i, hb i])).2
    rw [h0, sub_zero] at h1
    have h2 : Ideal.span (Set.range (Sum.elim a b)) ≤ nilradical S := by
      rw [Ideal.span_le]
      rintro _ ⟨i | i, rfl⟩
      exacts [mem_nilradical.2 (ha i), mem_nilradical.2 (hb i)]
    exact mem_nilradical.1 (h2 h1)
  have hnil' : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      (∀ i, IsNilpotent (a i)) → ∀ n k, IsNilpotent (nsmulF ch.F a n k) := by
    intro S _ _ a ha n
    induction n with
    | zero => intro k; simp [nsmulF]
    | succ n ih => exact hnil S _ _ ih ha
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
      (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) → ∀ n k,
      φ (nsmulF ch.F a n k) = nsmulF ch.F (fun i => φ (a i)) n k := by
    intro S _ _ S' _ _ φ a ha n
    induction n with
    | zero => intro k; simp [nsmulF]
    | succ n ih =>
      intro k
      have h1 := ((hev (ch.F k) S (Sum.elim (nsmulF ch.F a n) a)).2
        (by rintro (i | i); exacts [hnil' S a ha n i, ha i])).1 S' φ
      change φ (nEval (ch.F k) (Sum.elim (nsmulF ch.F a n) a)) =
        nEval (ch.F k) (Sum.elim (nsmulF ch.F (fun i => φ (a i)) n) (fun i => φ (a i)))
      rw [h1]
      congr 1
      funext i
      rcases i with i | i
      · exact ih i
      · rfl

  let I : Ideal (MvPolynomial (Fin g) R₀) :=
    Ideal.span (Set.range fun j : Fin g => (MvPolynomial.X j : MvPolynomial (Fin g) R₀) ^ (N + 1))
  let x : Fin g → MvPolynomial (Fin g) R₀ ⧸ I := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have hx : ∀ j, IsNilpotent (x j) := fun j => ⟨N + 1, by
    change Ideal.Quotient.mk I (MvPolynomial.X j) ^ (N + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩⟩
  choose G₁ hG₁ using fun k => Ideal.Quotient.mk_surjective (nsmulF ch.F x p k)
  have huniv : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      (∀ i, a i ^ (N + 1) = 0) → ∀ k, nsmulF ch.F a p k = MvPolynomial.aeval a (G₁ k) := by
    intro S _ _ a ha k
    let φ : (MvPolynomial (Fin g) R₀ ⧸ I) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval a) (by
        intro f hf
        have : I ≤ RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin g) R₀ →ₐ[R₀] S) := by
          rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hf)
    have hφ : ∀ f, φ (Ideal.Quotient.mk I f) = MvPolynomial.aeval a f := fun f => rfl
    have h1 := hnat _ S φ x hx p k
    have h2 : (fun i => φ (x i)) = a := by
      funext i
      change φ (Ideal.Quotient.mk I _) = _
      rw [hφ, MvPolynomial.aeval_X]
    rw [h2, ← hG₁ k, hφ] at h1
    exact h1.symm
  choose G hG hGe using fun k => pSerOf_trunc N (G₁ k)
  refine ⟨G, ?_, ?_⟩
  · intro k m hm
    rw [hG]
    split_ifs with h
    · refine hcoef p g N (G₁ k) ?_ m h hm
      intro S _ _ hp a e ha he
      have h1 : ∀ i, (a + e) i ^ (N + 1) = 0 := fun i =>
        (Commute.all (a i) (e i)).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (ha i)
          (show e i ^ 2 = 0 by rw [sq, he]) (by omega)
      have h2 : ∀ i, a i ^ (N + 1) = 0 := fun i => by rw [pow_succ, ha i, zero_mul]
      rw [← huniv S _ h1, ← huniv S _ h2, hinv ch p S hp a e (fun i => ⟨N, ha i⟩) he]
    · exact ⟨0, by simp⟩
  · intro S _ _ a ha
    funext k
    rw [hGe k S a ha]
    exact huniv S a (fun i => by rw [pow_succ, ha i, zero_mul]) k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicEndApply
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PadicOrderAction

def padicEnd (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0) :
    ℤ_[p] →+* AddMonoid.End M where
  toFun c := nsmulAddMonoidHom (PadicInt.toZMod c).val
  map_one' := by
    ext x
    change (PadicInt.toZMod (1 : ℤ_[p])).val • x = x
    rw [map_one, ZMod.val_one, one_nsmul]
  map_mul' a b := by
    ext x
    change (PadicInt.toZMod (a * b)).val • x = (PadicInt.toZMod a).val • (PadicInt.toZMod b).val • x
    rw [map_mul, ZMod.val_mul, ← nsmul_eq_mod_nsmul _ (hM x), mul_nsmul']
  map_zero' := by
    ext x
    change (PadicInt.toZMod (0 : ℤ_[p])).val • x = 0
    rw [map_zero, ZMod.val_zero, zero_nsmul]
  map_add' a b := by
    ext x
    change (PadicInt.toZMod (a + b)).val • x = (PadicInt.toZMod a).val • x + (PadicInt.toZMod b).val • x
    rw [map_add (f := _), ZMod.val_add, ← nsmul_eq_mod_nsmul _ (hM x), add_nsmul]

def liftInt {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) : A ⊗[ℤ] B →+* C :=
  (Algebra.TensorProduct.lift φ.toIntAlgHom ψ.toIntAlgHom h).toRingHom

lemma liftInt_tmul {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) (a : A) (b : B) : liftInt φ ψ h (a ⊗ₜ[ℤ] b) = φ a * ψ b :=
  Algebra.TensorProduct.lift_tmul φ.toIntAlgHom ψ.toIntAlgHom h a b

variable {R₀ : Type} [CommRing R₀]

lemma pTorsion_nsmul_eq_zero (B : BX R₀) (p : ℕ) (S : LAlg R₀) (x : torP B p S) : p • x = 0 :=
  Subtype.ext ((mem_torP B p _).1 x.2)

def resEnd {B : BX R₀} {O : LAlg R₀} (e : OEnd B O) (p : ℕ) {S : LAlg R₀} (s : LHom O S) :
    AddMonoid.End (torP B p S) :=
  ((e.f s).comp (torP B p S).subtype).codRestrict (torP B p S) fun x => by
    rw [mem_torP, ← map_nsmul, pTorsion_nsmul_eq_zero, map_zero]

def ordEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) : O₀ →+* AddMonoid.End (torP B p S) :=
  RingHom.mk' (α := O₀) (β := AddMonoid.End (torP B p S))
    { toFun := fun a => resEnd (f a) p s
      map_one' := AddMonoidHom.ext fun x => Subtype.ext (h x).1
      map_mul' := fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).2 }
    fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).1

def complEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) :
    ℤ_[p] ⊗[ℤ] O₀ →+* AddMonoid.End (torP B p S) :=
  liftInt (padicEnd p _ (pTorsion_nsmul_eq_zero B p S)) (ordEnd f p s h) fun c a =>
    AddMonoidHom.ext fun x => (map_nsmul (ordEnd f p s h a) (PadicInt.toZMod c).val x).symm

lemma complEnd_tmul {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) (c : ℤ_[p]) (a : O₀) (x : torP B p S) :
    (complEnd f p s h (c ⊗ₜ[ℤ] a) x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x := by
  have e : complEnd f p s h (c ⊗ₜ[ℤ] a) =
      padicEnd p _ (pTorsion_nsmul_eq_zero B p S) c * ordEnd f p s h a := liftInt_tmul _ _ _ c a
  rw [e]
  rfl

def complMat {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ) [Fact p.Prime]
    [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) :
    ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) O :=
  liftInt (algebraMap ℤ_[p] (Matrix (Fin g) (Fin g) O)) dL fun c a => Algebra.commutes c (dL a)

lemma complMat_tmul {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ)
    [Fact p.Prime] [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) (c : ℤ_[p]) (a : O₀) :
    complMat p dL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c • dL a := by
  rw [complMat, liftInt_tmul, algebraMap_smul]
  exact (Algebra.smul_def c (dL a)).symm

def kerMul {R S : LAlg R₀} (π : LHom R S) (r : (R : Type)) (i : π.ker) : π.ker :=
  ⟨r * i, Ideal.mul_mem_left (RingHom.ker π.1) r i.2⟩

lemma padic_mul_eq {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (t : ℤ_[p] →+* R) (c : ℤ_[p])
    (i : R) (hi : p • i = 0) : t c * i = (PadicInt.toZMod c).val • i := by
  have h : c - ((PadicInt.toZMod c).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨d, hd⟩ := h
  have hc : c = d * p + ((PadicInt.toZMod c).val : ℤ_[p]) := by rw [hd]; ring
  rw [nsmul_eq_mul] at hi ⊢
  conv_lhs => rw [hc]
  rw [map_add (f := _), map_mul, map_natCast, map_natCast, add_mul, _root_.mul_assoc, hi, mul_zero, zero_add]

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (O : Type)] (dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
    Function.Surjective (algebraMap R₀ (O : Type)) → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) →
    ∃ (A : OAct B O p (ℤ_[p] ⊗[ℤ] O₀)) (ρL : ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
      (∀ c a, ρL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] (O : Type) c • dL a) ∧
      (∀ a k l, ρL a k l = algebraMap R₀ (O : Type) (gb.repr (A.actL a (gb l)) k)) ∧
      ∀ c a (S : LAlg R₀) (s : LHom O S) (x : torP B p S), (A.act (c ⊗ₜ[ℤ] a) S s x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x) := by
  intro R₀ _ g B O gb O₀ _ f p _ _ dL hs hf htg
  choose pre hpre using hs
  let L : ℤ_[p] ⊗[ℤ] O₀ → B.gg →ₗ[R₀] B.gg := fun a =>
    gb.constr R₀ fun l => ∑ k, pre (complMat p dL a k l) • gb k
  have hL : ∀ a l, L a (gb l) = ∑ k, pre (complMat p dL a k l) • gb k := fun a l =>
    gb.constr_basis R₀ _ l
  have key : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] kerMul π (s.1 (complMat p dL a k l)) i) := by
    intro a R S s π hπ l i hi
    induction a using TensorProduct.induction_on with
    | zero =>
      have : ∀ k, kerMul π (s.1 (complMat p dL 0 k l)) i = 0 := fun k =>
        Subtype.ext (by simp [kerMul])
      simp only [this]
      simp only [TensorProduct.tmul_zero, Finset.sum_const_zero, map_zero]
      rfl
    | tmul c a =>
      rw [complEnd_tmul]
      change _ • (f a).f s (B.tg π hπ (gb l ⊗ₜ i)) = _
      rw [htg a s π hπ l i (fun k => kerMul π (s.1 (dL a k l)) i) (fun k => rfl), ← map_nsmul,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      refine (map_nsmul (TensorProduct.mk R₀ B.gg π.ker (gb k)) _ _).symm.trans ?_
      change gb k ⊗ₜ[R₀] _ = _
      congr 1
      apply Subtype.ext
      have hi' : p • (i : (R : Type)) = 0 := congrArg Subtype.val hi
      have h2 := padic_mul_eq (s.1.toRingHom.comp (algebraMap ℤ_[p] (O : Type))) c
        (s.1 (dL a k l) * i) (by rw [← mul_smul_comm, hi', mul_zero])
      change (PadicInt.toZMod c).val • (s.1 (dL a k l) * i) = s.1 (complMat p dL (c ⊗ₜ a) k l) * i
      rw [← h2, complMat_tmul, Matrix.smul_apply, smul_eq_mul, map_mul, _root_.mul_assoc]
      rfl
    | add a b ha hb =>
      have : ∀ k, kerMul π (s.1 (complMat p dL (a + b) k l)) i =
          kerMul π (s.1 (complMat p dL a k l)) i + kerMul π (s.1 (complMat p dL b k l)) i :=
        fun k => Subtype.ext (by simp [kerMul, add_mul])
      simp only [this, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [map_add (B.tg π hπ), ← ha, ← hb, map_add (f := _)]
      rfl
  have key2 : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (L a (gb l) ⊗ₜ[R₀] i) := by
    intro a R S s π hπ l i hi
    rw [key a s π hπ l i hi, hL, TensorProduct.sum_tmul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    change s.1 (complMat p dL a k l) * i = pre (complMat p dL a k l) • (i : (R : Type))
    rw [Algebra.smul_def, ← s.1.commutes, hpre]
  refine ⟨{ act := fun a S s => complEnd f p s (hf s) a
            act_one := fun S s x => by rw [map_one]; rfl
            act_mul := fun a b S s x => by rw [map_mul]; rfl
            act_add := fun a b S s x => by rw [map_add (f := _)]; rfl
            act_nat := ?_
            actL := L
            act_tg := ?_ }, complMat p dL, complMat_tmul p dL, ?_,
            fun c a S s x => complEnd_tmul f p s (hf s) c a x⟩
  · intro a S S' s s' φ hφ x
    subst hφ
    change B.map φ (complEnd f p s (hf s) a x : B.G S) =
      (complEnd f p (φ.comp s) (hf _) a ⟨B.map φ x, map_torP B p φ x⟩ : B.G S')
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [complEnd_tmul, complEnd_tmul, map_nsmul, (f a).nat]
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      change B.map φ ((complEnd f p s (hf s) a x : B.G S) + (complEnd f p s (hf s) b x : B.G S)) = _
      rw [map_add (f := _), ha, hb]
      rfl
  · intro a R S s π hπ w i hi
    have hr : ∀ l, p • (gb.repr w l • i) = 0 := fun l => by rw [smul_comm, hi, smul_zero]
    have h1 : (⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : torP B p R) =
        ∑ l, ⟨B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i)), tg_torP B p π hπ _ _ (hr l)⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      change B.tg π hπ (w ⊗ₜ i) = ∑ l, B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      congr 1
      conv_lhs => rw [← gb.sum_repr w, TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun l _ => TensorProduct.smul_tmul _ _ _
    change (complEnd f p s (hf s) a ⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : B.G R) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_congr rfl fun l _ => key2 a s π hπ l _ (hr l), ← map_sum]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← gb.sum_repr w, map_sum, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, TensorProduct.smul_tmul]
  · intro a k l
    change complMat p dL a k l = algebraMap R₀ (O : Type) (gb.repr (L a (gb l)) k)
    rw [hL, gb.repr_sum_self, hpre]

end GlobalTheory.PadicOrderAction
end
end

