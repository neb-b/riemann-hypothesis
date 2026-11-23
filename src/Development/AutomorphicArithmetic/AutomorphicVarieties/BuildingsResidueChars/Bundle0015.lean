module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrderLevelInjectiveOfSmulEq
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem ord_mem {y z : Etau K τ} :
    z ∈ PK.Ord (O := O) y ↔ ∃ a b : O, a • (1 : Etau K τ) + b • y = z :=
  Submodule.mem_span_pair

private theorem ord_one (y : Etau K τ) : (1 : Etau K τ) ∈ PK.Ord (O := O) y :=
  ord_mem.2 ⟨1, 0, by simp⟩

private theorem ord_mul {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {z z' : Etau K τ} (hz : z ∈ PK.Ord (O := O) y) (hz' : z' ∈ PK.Ord (O := O) y) : z * z' ∈ PK.Ord (O := O) y := by
  obtain ⟨a, b, rfl⟩ := ord_mem.1 hz
  obtain ⟨p, q, rfl⟩ := ord_mem.1 hz'
  refine ord_mem.2 ⟨a * p + b * q * c, a * q + b * p, ?_⟩
  simp only [Algebra.smul_def, map_add (f := _), map_mul]
  linear_combination (-(algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) q)) * hy

private theorem ord_sub {y y' : Etau K τ} {c c' : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hy' : y' * y' = algebraMap O (Etau K τ) c') {w : (Etau K τ)ˣ}
    (hw : PS.ml w (PK.Ord (O := O) y) = PK.Ord (O := O) y') {z : Etau K τ} (hz : z ∈ PK.Ord (O := O) y) : z ∈ PK.Ord (O := O) y' := by
  have hw1 : ((w⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ PK.Ord (O := O) y := by
    have := ord_one (O := O) y'
    rw [← hw, PS.mem_ml, mul_one] at this
    exact this
  rw [← hw, PS.mem_ml]
  exact ord_mul hy hw1 hz
end

private theorem lvl_le {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {τ : K} {π : O} (hπ : Irreducible π) {x : Etau K τ}
    (hx : x.im ≠ 0) {m m' : ℕ} (h : yy π m x ∈ PK.Ord (O := O) (yy π m' x)) : m' ≤ m := by
  obtain ⟨a, b, hab⟩ := ord_mem.1 h
  have him := congrArg QuadraticAlgebra.im hab
  simp only [yy, ← algebraMap_smul K a, ← algebraMap_smul K b, im_add, im_smul, im_one, mul_zero, zero_add,
    smul_eq_mul] at him
  have hk : algebraMap O K (b * π ^ m') = algebraMap O K (π ^ m) := by
    rw [map_mul]
    exact mul_right_cancel₀ hx (by rw [← him]; ring)
  have hd : π ^ m' ∣ π ^ m := ⟨b, by rw [IsFractionRing.injective O K hk.symm, mul_comm]⟩
  exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 hd

theorem UpperTheory.order_level_injective_of_smul_eq :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (w : (Etau K τ)ˣ) (m m' : ℕ), PS.ml w (PK.Ord (O := O) (yy π m x)) = PK.Ord (O := O) (yy π m' x) → m = m' := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc w m m' hw
  haveI := L.frac
  have hx : x.im ≠ 0 := hc.gen.im_ne
  have hsq : ∀ j : ℕ, yy π j x * yy π j x = algebraMap O (Etau K τ) (π ^ j * π ^ j * e) := by
    intro j
    simp only [yy, smul_mul_smul_comm, hc.sq]
    rw [IsScalarTower.algebraMap_apply O K (Etau K τ), IsScalarTower.algebraMap_apply O K (Etau K τ),
      Algebra.smul_def, ← map_mul, map_mul (algebraMap O K) (π ^ j * π ^ j), map_mul (algebraMap O K) (π ^ j)]
  have self_mem : ∀ j : ℕ, yy π j x ∈ PK.Ord (O := O) (yy π j x) := fun j => ord_mem.2 ⟨0, 1, by simp⟩
  have hw' : PS.ml w⁻¹ (PK.Ord (O := O) (yy π m' x)) = PK.Ord (O := O) (yy π m x) := by
    rw [← hw, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]
  have h1 : m' ≤ m := lvl_le hc.irr hx (ord_sub (hsq m) (hsq m') hw (self_mem m))
  have h2 : m ≤ m' := lvl_le hc.irr hx (ord_sub (hsq m') (hsq m) hw' (self_mem m'))
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricSubalgebraLeAdjoinRangeProdCAddXComplex
section
open MvPolynomial in
theorem UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex :
    ∀ n : ℕ, MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) := by
  intro n
  set S := Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) with hS
  have hv : ∀ u : ℂ, ∏ k : Fin n, (C u + X k : MvPolynomial (Fin n) ℂ)
      = ∑ j ∈ Finset.range (n + 1), u ^ (n - j) • esymm (Fin n) ℂ j := by
    intro u
    have h := congrArg (Polynomial.eval (C u : MvPolynomial (Fin n) ℂ))
      (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
    simp only [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, map_pow, mul_comm]
  have he : ∀ j, j < n + 1 → esymm (Fin n) ℂ j ∈ S := by
    intro j hj
    by_contra hc
    obtain ⟨φ, hφ, h0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule S) hc inferInstance
    have h1 : ∀ x ∈ S, φ x = 0 := fun x hx => (Submodule.eq_bot_iff _).1 h0 _ ⟨x, hx, rfl⟩
    have hp : (∑ i ∈ Finset.range (n + 1), Polynomial.monomial (n - i) (φ (esymm (Fin n) ℂ i))) = 0 := by
      apply Polynomial.funext
      intro u
      have h2 := h1 _ (Algebra.subset_adjoin ⟨u, rfl⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hv, map_sum, map_smul, smul_eq_mul] at h2
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h3 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (n - j)) hp
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h3
    rw [Finset.sum_eq_single j] at h3
    · exact hφ (by simpa using h3)
    · intro b hb hbj
      rw [Finset.mem_range] at hb
      exact Finsupp.single_eq_of_ne (by omega)
    · intro h
      exact absurd (Finset.mem_range.2 hj) h
  intro p hp
  obtain ⟨q, hq⟩ := (esymmAlgHom_fin_bijective ℂ n).2 ⟨p, hp⟩
  have hq' : p = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) q := by
    rw [← esymmAlgHom_apply, hq]
  rw [hq']
  have : Algebra.adjoin ℂ (Set.range fun i : Fin n => esymm (Fin n) ℂ (i + 1)) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact he _ (by have := i.2; omega))
  apply this
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨q, rfl⟩
end

