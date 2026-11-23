module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparating
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_det_ne_zero_of_rows_separating :
    ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K),
      (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) →
      ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  intro K _ σ h M hM
  have hsp : Submodule.span K (Set.range M) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have ha : (fun j => f (fun k => if j = k then 1 else 0)) = 0 := by
      apply hM
      intro s
      have h1 : f (M s) = 0 := hf (Submodule.subset_span ⟨s, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
      rw [smul_eq_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [Pi.zero_apply] at this
    rw [this, smul_zero]
  obtain ⟨b, hbS, hbsp, hli⟩ := exists_linearIndependent K (Set.range M)
  have hsp' : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin h → K)) := by
    rw [Subtype.range_coe, hbsp, hsp]
  let B := Module.Basis.mk hli hsp'
  let e : Fin h ≃ b := (Pi.basisFun K (Fin h)).indexEquiv B
  have hmem : ∀ i, ∃ s, M s = (e i : Fin h → K) := fun i => hbS (e i).2
  choose s hs using hmem
  refine ⟨s, ?_⟩
  have hrows : LinearIndependent K (Matrix.of fun i j => M (s i) j).row := by
    have : (Matrix.of fun i j => M (s i) j).row = (fun x : b => (x : Fin h → K)) ∘ e := by
      funext i j
      simp [Matrix.row, hs]
    rw [this]
    exact hli.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulStdBlock
section
namespace GlobalTheory

open Matrix

theorem exists_det_one_mul_stdBlock {K : Type} [Field K] {n r : ℕ} (hrn : r < n)
    (y : Matrix (Fin n) (Fin r) K) (hy : y.rank = r) :
    ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧
      g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  classical
  have hli : LinearIndependent K y.col := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_cols] at hy
    exact hy.symm
  let b := Module.Basis.sumExtend hli
  have hfin : Finite (Fin r ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis b
  have : Finite (Module.Basis.sumExtendIndex hli) := Finite.of_injective (Sum.inr : _ → Fin r ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin r ⊕ Module.Basis.sumExtendIndex hli) = n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  have hb : ∀ i, b (Sum.inl i) = y.col i := by
    intro i
    simp only [b, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  have hS : Fintype.card (Module.Basis.sumExtendIndex hli) = n - r := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard; omega
  let e : Fin (n - r) ≃ Module.Basis.sumExtendIndex hli := (Fintype.equivFinOfCardEq hS).symm
  let τ : Fin n → Fin r ⊕ Module.Basis.sumExtendIndex hli := fun c =>
    if h : (c : ℕ) < r then Sum.inl ⟨c, h⟩ else Sum.inr (e ⟨c - r, by omega⟩)
  have hτ : Function.Injective τ := by
    intro c c' h
    simp only [τ] at h
    split_ifs at h
    all_goals first
      | (simp only [Sum.inl.injEq, Fin.mk.injEq] at h; ext; omega)
      | (simp only [Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at h; ext; omega)
      | exact absurd h Sum.inl_ne_inr
      | exact absurd h.symm Sum.inl_ne_inr
  let s : Fin n → Fin n → K := b ∘ τ
  have hs : LinearIndependent K s := b.linearIndependent.comp τ hτ
  let g₀ : Matrix (Fin n) (Fin n) K := Matrix.of fun i a => s a i
  have hg₀col : g₀.col = s := by ext a i; rfl
  have hu : IsUnit g₀ := Matrix.linearIndependent_cols_iff_isUnit.mp (hg₀col ▸ hs)
  have hdet : g₀.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  let last : Fin n := ⟨n - 1, by omega⟩
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun a => if a = last then g₀.det⁻¹ else 1
  let g := g₀ * D
  have hgdet : g.det = 1 := by
    simp only [g, D, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ hdet
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (by rw [hgdet]; exact isUnit_one)
  refine ⟨hU.unit, ?_, ?_⟩
  · ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hgdet]
  · have hE : ∀ (a : Fin n) (c : Fin r), ((a : ℕ) = (c : ℕ)) ↔ a = Fin.castLE hrn.le c := by
      intro a c; rw [Fin.ext_iff, Fin.coe_castLE]
    have hτc : ∀ c : Fin r, τ (Fin.castLE hrn.le c) = Sum.inl c := by
      intro c
      simp only [τ, Fin.coe_castLE, dif_pos c.isLt]
    rw [IsUnit.unit_spec]
    ext i c
    simp only [g, D, Matrix.mul_assoc, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, hE]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hne : Fin.castLE hrn.le c ≠ last := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.coe_castLE, last] at h2
      omega
    simp only [if_neg hne, mul_one]
    show b (τ (Fin.castLE hrn.le c)) i = y i c
    rw [hτc, hb]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowerEvalTwoVarsRingHom
section
open MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DPEval2

def bv (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • (X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

def ex (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2

theorem ex_injective : Function.Injective ex := by
  intro p q h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) h
  simp [ex] at h0 h1
  exact Prod.ext h0 h1

theorem bv_eq (p : ℕ × ℕ) :
    bv p = ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • monomial (ex p) (1 : ℚ) := by
  rw [bv, ex, X_pow_eq_monomial, X_pow_eq_monomial, smul_monomial, smul_monomial,
    monomial_mul_monomial, smul_monomial]
  simp

theorem bv_li : LinearIndependent ℚ bv := by
  have h := ((basisMonomials (Fin 2) ℚ).linearIndependent.comp ex ex_injective).units_smul
    (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity))
  have e : bv = (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity)) •
      (⇑(basisMonomials (Fin 2) ℚ) ∘ ex) := by
    funext p
    simp [bv_eq, Units.smul_def, coe_basisMonomials]
  rw [e]; exact h

theorem ex_add (p q : ℕ × ℕ) : ex (p + q) = ex p + ex q := by
  simp only [ex, Prod.fst_add, Prod.snd_add, Finsupp.single_add]; abel

theorem bv_mul (p q : ℕ × ℕ) :
    bv p * bv q = ((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) • bv (p + q) := by
  rw [bv_eq, bv_eq, bv_eq, smul_mul_smul, monomial_mul_monomial, ← ex_add,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_one]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul, Nat.cast_add_choose]
  field_simp

def D : Submodule ℤ (MvPolynomial (Fin 2) ℚ) := Submodule.span ℤ (Set.range bv)

theorem bv_mem (p : ℕ × ℕ) : bv p ∈ D := Submodule.subset_span ⟨p, rfl⟩

def β : Module.Basis (ℕ × ℕ) ℤ D := Module.Basis.span (bv_li.restrict_scalars' ℤ)

theorem β_eq (p : ℕ × ℕ) : β p = ⟨bv p, bv_mem p⟩ :=
  Module.Basis.span_apply _ p

theorem mul_mem {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) : x * y ∈ D := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [bv_mul]
    exact Submodule.smul_of_tower_mem _ _ (bv_mem _)
  · intro y _; simp
  · intro y _; simp
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

variable {B : Type} [CommRing B] (u v : ℕ → B)

def ψ : D →ₗ[ℤ] B := β.constr ℤ fun p ↦ u p.1 * v p.2


open Classical in
def φ (q : MvPolynomial (Fin 2) ℚ) : B := by
  classical
  exact if h : q ∈ D then ψ u v ⟨q, h⟩ else 0

theorem φ_of_mem {q : MvPolynomial (Fin 2) ℚ} (h : q ∈ D) :
    φ u v q = ψ u v ⟨q, h⟩ := dite_eq_left h

theorem φ_bv (p : ℕ × ℕ) : φ u v (bv p) = u p.1 * v p.2 := by
  rw [φ_of_mem u v (bv_mem p), ← β_eq, ψ, Module.Basis.constr_basis]

theorem φ_add {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x + y) = φ u v x + φ u v y := by
  rw [φ_of_mem u v hx, φ_of_mem u v hy, φ_of_mem u v (add_mem hx hy), ← map_add (f := _)]; rfl

theorem φ_zsmul (z : ℤ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (z • x) = z • φ u v x := by
  rw [φ_of_mem u v hx, φ_of_mem u v (Submodule.smul_mem _ z hx), ← map_zsmul]; rfl

theorem φ_nsmul (n : ℕ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (n • x) = n • φ u v x := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n x, φ_zsmul u v _ hx, Nat.cast_smul_eq_nsmul]

theorem φ_zero : φ u v 0 = 0 := by
  rw [φ_of_mem u v (zero_mem _)]; exact map_zero (ψ u v)

theorem φ_mul (hu : ∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n))
    (hv : ∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n))
    {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x * y) = φ u v x * φ u v y := by
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦ φ u v (x * y) = φ u v x * φ u v y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [bv_mul, φ_nsmul u v _ (bv_mem _), φ_bv, φ_bv, φ_bv, nsmul_eq_mul]
    calc ((((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ)) : B) * (u (p + q).1 * v (p + q).2)
        = (((p.1 + q.1).choose p.1 : B) * u (p.1 + q.1)) * (((p.2 + q.2).choose p.2 : B) * v (p.2 + q.2)) := by
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul]; ring
      _ = u p.1 * v p.2 * (u q.1 * v q.2) := by rw [← hu, ← hv]; ring
  · intro y _; simp [φ_zero]
  · intro y _; simp [φ_zero]
  · intro x y z hx hy hz h1 h2
    rw [add_mul, φ_add u v (mul_mem hx hz) (mul_mem hy hz), φ_add u v hx hy, h1, h2, add_mul]
  · intro x y z hx hy hz h1 h2
    rw [mul_add, φ_add u v (mul_mem hx hy) (mul_mem hx hz), φ_add u v hy hz, h1, h2, mul_add]
  · intro r x y hx hy h
    rw [smul_mul_assoc, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hx, h, smul_mul_assoc]
  · intro r x y hx hy h
    rw [mul_smul_comm, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hy, h, mul_smul_comm]

end GlobalTheory.DPEval2

namespace GlobalTheory


open DPEval2 in
theorem dpEval_two :
    ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  intro B _ u v _ _ hu hv
  refine ⟨DPEval2.φ u v, fun a c ↦ DPEval2.φ_bv u v (a, c), fun d hd e he ↦ ?_,
    fun z d hd ↦ DPEval2.φ_zsmul u v z hd⟩
  exact ⟨DPEval2.φ_add u v hd he, DPEval2.mul_mem hd he, DPEval2.φ_mul u v hu hv hd he⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingDvrContainingFinset
section
open IsLocalRing

namespace GlobalTheory.DomDVR


set_option maxHeartbeats 1000000 in
theorem exists_dominating_dvr : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  intro F _ _ T' hT s h1 hmul
  classical
  haveI := hT
  set A := Submodule.span T' (s : Set F) with hA
  have hAmul : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A := by
    intro x y hx hy
    have : A * A ≤ A := by
      rw [hA, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
    exact this (Submodule.mul_mem_mul hx hy)
  have hsm : ∀ d ∈ T', ∀ a ∈ A, d * a ∈ A := fun d hd a ha => A.smul_mem ⟨d, hd⟩ ha
  let Asub : Subalgebra T' F := A.toSubalgebra h1 hAmul
  have hint : ∀ x ∈ s, IsIntegral T' x := fun x hx =>
    IsIntegral.of_mem_of_fg Asub (Submodule.fg_span s.finite_toSet) x (Submodule.subset_span hx)
  let K := FractionRing T'
  have hι : Function.Injective (T'.subtype) := Subtype.val_injective
  letI : Algebra K F := (IsFractionRing.lift (K := K) hι).toAlgebra
  haveI : IsScalarTower T' K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap (K := K) hι x).symm)
  have hintK : ∀ x ∈ (s : Set F), IsIntegral K x := fun x hx => (hint x hx).tower_top
  let L := IntermediateField.adjoin K (s : Set F)
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin hintK
  haveI : CharZero K := (algebraMap K F).charZero
  haveI : Algebra.IsSeparable K L := inferInstance
  let C := integralClosure T' L
  haveI : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain T' K L C

  have hLF : ∀ a : T', ((algebraMap T' L a : L) : F) = a := by
    intro a
    rw [IsScalarTower.algebraMap_apply T' K L]
    show algebraMap K F (algebraMap T' K a) = a
    exact IsFractionRing.lift_algebraMap (K := K) hι a
  have hcoe : ∀ a : T', (((algebraMap T' C a : C) : L) : F) = a := by
    intro a
    rw [← hLF a, IsScalarTower.algebraMap_apply T' C L]
    rfl
  have hinjC : Function.Injective (algebraMap T' C) := fun a b h => Subtype.val_injective (by
    have := congrArg (fun c : C => ((c : L) : F)) h
    simpa only [hcoe] using this)
  obtain ⟨P, hPmax, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (maximalIdeal T')
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinjC]; exact bot_le)
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field T'
    rw [← hPm, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinjC)]
  let Loc := Localization.AtPrime P
  haveI : IsDiscreteValuationRing Loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot Loc
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap C L y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (by
      rw [show (y : C) = 0 from Subtype.ext (by simpa using h)]; exact P.zero_mem)
  let ψ : Loc →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hψ : Function.Injective ψ := (IsLocalization.lift_injective_iff hunit).2 fun x y =>
    ⟨fun h => by rw [IsLocalization.injective Loc P.primeCompl_le_nonZeroDivisors h], fun h => by rw [Subtype.val_injective h]⟩
  let φ : Loc →+* F := (algebraMap L F).comp ψ
  have hφ : Function.Injective φ := fun a b h => hψ ((algebraMap L F).injective h)
  have hφc : ∀ c : C, φ (algebraMap C Loc c) = ((c : L) : F) := by
    intro c
    show ((ψ (algebraMap C Loc c) : L) : F) = _
    rw [IsLocalization.lift_eq]
    rfl
  let T'' := φ.range
  let e : Loc ≃+* T'' := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => hφ (by simpa only [RingHom.coe_rangeRestrict] using congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  refine ⟨T'', IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact RingHom.mem_range.2 ⟨algebraMap C Loc (algebraMap T' C ⟨x, hx⟩), by rw [hφc, hcoe]⟩
  · intro x hx
    have hxL : x ∈ L := IntermediateField.subset_adjoin K _ hx
    have hxC : (⟨x, hxL⟩ : L) ∈ C := by
      rw [mem_integralClosure_iff]
      let f : L →ₐ[T'] F := { toRingHom := algebraMap L F, commutes' := fun a => hLF a }
      exact (isIntegral_algHom_iff f (algebraMap L F).injective).1 (hint x hx)
    exact RingHom.mem_range.2 ⟨algebraMap C Loc ⟨⟨x, hxL⟩, hxC⟩, by rw [hφc]⟩
  · rintro x hx ⟨y, hy, hxy⟩
    by_contra hne
    have hnu : (⟨x, hx⟩ : T') ∈ maximalIdeal T' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      exact hne ⟨b, b.2, congrArg Subtype.val hb⟩
    have hP : algebraMap T' C ⟨x, hx⟩ ∈ P := by
      rw [← hPm] at hnu; exact hnu
    have hmax : algebraMap C Loc (algebraMap T' C ⟨x, hx⟩) ∈ maximalIdeal Loc :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff Loc P _).2 hP
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    apply (IsLocalRing.mem_maximalIdeal _).1 hmax
    refine isUnit_iff_exists_inv.2 ⟨z, hφ ?_⟩
    rw [map_mul, map_one, hφc, hcoe]; exact hxy
  · let M : Subalgebra K F :=
      { carrier := {y | ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ A}
        mul_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a * b) = (d1 * a) * (d2 * b) by ring]; exact hAmul _ _ ha hb⟩
        add_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a + b) = d2 * (d1 * a) + d1 * (d2 * b) by ring]
            exact A.add_mem (hsm _ hd2 _ ha) (hsm _ hd1 _ hb)⟩
        algebraMap_mem' := by
          intro k
          obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T') k
          have hb : ((b : T') : F) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
          refine ⟨(b : T'), (b : T').2, hb, ?_⟩
          have e1 : algebraMap K F (IsLocalization.mk' K a b) = (a : F) / ((b : T') : F) :=
            IsFractionRing.lift_mk' hι a b
          have e2 : ((b : T') : F) * ((a : F) / ((b : T') : F)) = a := by field_simp
          rw [e1, e2]
          simpa using hsm _ a.2 _ h1 }
    have hLM : ∀ y ∈ L, y ∈ M := by
      intro y hy
      have e := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := K) (S := (s : Set F))
        (fun x hx => (hintK x hx).isAlgebraic)
      have hy' : y ∈ Algebra.adjoin K (s : Set F) := by rw [← e]; exact hy
      refine (Algebra.adjoin_le ?_ : Algebra.adjoin K (s : Set F) ≤ M) hy'
      intro x hx
      exact ⟨1, T'.one_mem, one_ne_zero, by rw [one_mul]; exact Submodule.subset_span hx⟩
    intro y hy
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    exact hLM _ (ψ z).2
end GlobalTheory.DomDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqRe
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_equiv_euclidean_pi_mul_norm_sq_eq_re (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) :
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  classical
  let B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ (fun x y => (Q x y).re)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  let q : QuadraticForm ℝ V := B.toQuadraticMap
  have hq : ∀ x, q x = (Q x x).re := fun x => rfl
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares q
  have he : ∀ x, ∑ i, w i * (e x i * e x i) = (Q x x).re := by
    intro x
    have := e.map_app x
    rw [QuadraticMap.weightedSumSquares_apply] at this
    simpa [hq] using this
  have hw : ∀ i, 0 < w i := by
    intro i
    have h1 := he (e.symm (Pi.single i 1))
    have h2 : e (e.symm (Pi.single i 1)) = Pi.single i 1 := e.toLinearEquiv.apply_symm_apply _
    have hne : e.symm (Pi.single i 1) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      have := congrFun h2 i
      simp at this
    rw [h2, Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by simp)] at h1
    have h3 := hQ (e.symm (Pi.single i 1))
    have h4 : 0 < c * ‖e.symm (Pi.single i 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    simp at h1
    linarith
  have hs : ∀ i, Real.sqrt (w i / Real.pi) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (div_pos (hw i) Real.pi_pos)).ne'
  let D : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (w i / Real.pi)) (hs i)
  let A : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (e.toLinearEquiv.trans D).trans (WithLp.linearEquiv 2 ℝ _).symm
  have hA : ∀ x i, A x i = Real.sqrt (w i / Real.pi) * e x i := fun x i => rfl
  refine ⟨A.toContinuousLinearEquiv, fun x => ?_⟩
  rw [← he, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (A.toContinuousLinearEquiv x) i = Real.sqrt (w i / Real.pi) * e x i := hA x i
  rw [this, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (div_pos (hw i) Real.pi_pos).le]
  have := Real.pi_pos.ne'
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
section
namespace GlobalTheory.EtC

def IsExcisionNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  Algebra.Etale A A' ∧ (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
    ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}

theorem isExcisionNbhd_self (A : Type) [CommRing A] (f : A) : IsExcisionNbhd A A f :=
  ⟨inferInstance, fun a' => ⟨a', by simp⟩, fun a h => by simpa using h⟩

end GlobalTheory.EtC
end

