module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraTraceMapOfCokernelKilledByScalar
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem algebraTrace_map_of_cokernel_killed (S A B : Type) [CommRing S] [IsDomain S] [CommRing A]
    [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B]
    [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ)
    (s : S) (hs : s ≠ 0) (hr : ∀ b : B, s • b ∈ φ.range) (x : A) :
    Algebra.trace S B (φ x) = Algebra.trace S A x := by
  classical
  choose g hg using fun b => (AlgHom.mem_range φ).1 (hr b)
  let gl : B →ₗ[S] A :=
    { toFun := g
      map_add' := by
        intro b c
        apply hφ
        rw [map_add (f := _), hg, hg, hg, smul_add]
      map_smul' := by
        intro r b
        apply hφ
        rw [hg, RingHom.id_apply, map_smul, hg, smul_comm] }
  have h1 : φ.toLinearMap ∘ₗ gl = s • LinearMap.id := by
    ext b
    simp [gl, hg]
  have h2 : gl ∘ₗ φ.toLinearMap = s • LinearMap.id := by
    ext a
    apply hφ
    simp [gl, hg]
  have h3 : Algebra.lmul S B (φ x) ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ Algebra.lmul S A x := by
    ext a
    simp
  have key : s * Algebra.trace S B (φ x) = s * Algebra.trace S A x := by
    rw [Algebra.trace_apply, Algebra.trace_apply]
    calc s * LinearMap.trace S B (Algebra.lmul S B (φ x))
        = LinearMap.trace S B (Algebra.lmul S B (φ x) ∘ₗ (φ.toLinearMap ∘ₗ gl)) := by
          rw [h1, LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]
      _ = LinearMap.trace S B (φ.toLinearMap ∘ₗ (Algebra.lmul S A x ∘ₗ gl)) := by
          rw [← LinearMap.comp_assoc, h3, LinearMap.comp_assoc]
      _ = LinearMap.trace S A ((Algebra.lmul S A x ∘ₗ gl) ∘ₗ φ.toLinearMap) := by
          rw [LinearMap.trace_comp_comm']
      _ = s * LinearMap.trace S A (Algebra.lmul S A x) := by
          rw [LinearMap.comp_assoc, h2, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
            smul_eq_mul]
  exact mul_left_cancel₀ hs key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingMapLinearCombination
section
namespace GlobalTheory.AlternatingLinearCombination

theorem alternating_map_linear_combination {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    (f fun i => ∑ l : Fin n, a i l • g l) = Matrix.det (Matrix.of a) • f g := by
  classical
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff L]
  intro φ
  let ψ : (Fin n → L) →ₗ[L] M := Fintype.linearCombination L g
  let F : (Fin n → L) [⋀^Fin n]→ₗ[L] L := (φ.compAlternatingMap f).compLinearMap ψ
  have h := F.eq_smul_basis_det (Pi.basisFun L (Fin n))
  have h1 : F a = φ (f fun i => ∑ l : Fin n, a i l • g l) := by
    simp [F, ψ, Fintype.linearCombination_apply]
  have h2 : F (Pi.basisFun L (Fin n)) = φ (f g) := by
    have : (fun i => ψ (Pi.basisFun L (Fin n) i)) = g := by
      funext i
      simp [ψ]
    change φ (f fun i => ψ (Pi.basisFun L (Fin n) i)) = _
    rw [this]
  have h3 : F a = φ (f g) * Matrix.det (Matrix.of a) := by
    rw [h, AlternatingMap.smul_apply, h2, Pi.basisFun_det_apply, smul_eq_mul]
  rw [map_sub, map_smul, ← h1, h3, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.AlternatingLinearCombination
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorAvoidsFibreMinimalPrimes
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem annihilator_avoids_fibre_minimalPrimes
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B)
    (hd : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q}))
    (u : PrimeSpectrum B) : ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  classical
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) u
  let I₀ : Ideal B := p.asIdeal.map (algebraMap A B)
  let T : Set (Ideal B) := {Q | Q ∈ I₀.minimalPrimes ∧ Q.comap (algebraMap A B) = p.asIdeal}
  have hTfin : T.Finite := by
    let e := PrimeSpectrum.preimageOrderIsoFiber A B p
    haveI : IsNoetherianRing (p.asIdeal.Fiber B) :=
      Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
    have hM : {j : PrimeSpectrum (p.asIdeal.Fiber B) | j.asIdeal ∈ minimalPrimes (p.asIdeal.Fiber B)}.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing _).preimage (fun x _ y _ h => PrimeSpectrum.ext h)
    refine (hM.image fun j => (e.symm j).1.asIdeal).subset ?_
    rintro Q ⟨hQmin, hQp⟩
    have hQprime : Q.IsPrime := hQmin.1.1
    let Q' : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hQ'mem : Q' ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} := by
      show PrimeSpectrum.comap (algebraMap A B) Q' = p
      ext1; exact hQp
    obtain ⟨J, hJmin, hJle⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ (e ⟨Q', hQ'mem⟩).asIdeal)
    have hJprime : J.IsPrime := hJmin.1.1
    let j : PrimeSpectrum (p.asIdeal.Fiber B) := ⟨J, hJprime⟩
    refine ⟨j, hJmin, ?_⟩
    have hle : e.symm j ≤ ⟨Q', hQ'mem⟩ := by
      rw [← e.le_iff_le, e.apply_symm_apply]; exact hJle
    have hle' : (e.symm j).1.asIdeal ≤ Q := hle
    have hover : (e.symm j).1.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (e.symm j).2
    have hge : I₀ ≤ (e.symm j).1.asIdeal := by
      rw [Ideal.map_le_iff_le_comap, hover]
    exact le_antisymm hle' (hQmin.2 ⟨(e.symm j).1.isPrime, hge⟩ hle')
  obtain ⟨s, hs⟩ := hTfin.exists_finset_coe
  have hsT : ∀ i, i ∈ s ↔ i ∈ T := fun i => by rw [← hs]; rfl
  let K : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hK : ∀ x, x ∈ K ↔ x * b = 0 := fun x => by
    simp [K, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ Q ∈ T, ¬ K ≤ Q := by
    intro Q hQ hKQ
    have hQprime : Q.IsPrime := hQ.1.1.1
    have hnot : ¬ (∏ Q'' ∈ s.erase Q, Q'') ≤ Q := by
      rw [hQprime.prod_le]
      rintro ⟨i, hi, hiQ⟩
      have hiT : i ∈ T := (hsT i).1 (Finset.mem_of_mem_erase hi)
      exact Finset.ne_of_mem_erase hi (le_antisymm hiQ (hQ.1.2 hiT.1.1 hiQ))
    obtain ⟨f, hfprod, hfQ⟩ := SetLike.not_le_iff_exists.1 hnot
    have hfo : ∀ Q'' ∈ T, Q'' ≠ Q → f ∈ Q'' := fun Q'' hQ'' hne =>
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_erase.2 ⟨hne, (hsT Q'').2 hQ''⟩))) hfprod
    let Qp : PrimeSpectrum B := ⟨Q, hQprime⟩
    have hcl := hd Qp
    rw [mem_closure_iff] at hcl
    obtain ⟨P, hPf, ⟨t, htP, htb⟩, hPfib⟩ :=
      hcl (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B)) (PrimeSpectrum.basicOpen f).isOpen hfQ
    have hPf' : f ∉ P.asIdeal := hPf
    have hPover : P.asIdeal.comap (algebraMap A B) = p.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal hPfib).trans hQ.2
    have hI₀P : I₀ ≤ P.asIdeal := by rw [Ideal.map_le_iff_le_comap, hPover]
    obtain ⟨Q', hQ'min, hQ'P⟩ := Ideal.exists_minimalPrimes_le hI₀P
    have hQ'T : Q' ∈ T := ⟨hQ'min, le_antisymm ((Ideal.comap_mono hQ'P).trans hPover.le)
      (Ideal.map_le_iff_le_comap.1 hQ'min.1.2)⟩
    by_cases hQQ : Q' = Q
    · subst hQQ
      exact htP (hQ'P (hKQ ((hK t).2 htb)))
    · exact hPf' (hQ'P (hfo Q' hQ'T hQQ))
  have hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i : Ideal B).IsPrime := fun i hi _ _ =>
    ((hsT i).1 hi).1.1.1
  have hnot := mt (Ideal.subset_union_prime (f := id) (I := K) ⊥ ⊥ hprime).1 (by
    rintro ⟨i, hi, hKi⟩; exact key i ((hsT i).1 hi) hKi)
  rw [Set.not_subset] at hnot
  obtain ⟨g, hgK, hgU⟩ := hnot
  refine ⟨g, (hK g).1 hgK, fun Q hQ hQu hgQ => hgU ?_⟩
  have hQT : Q ∈ T := ⟨hQ, le_antisymm (Ideal.comap_mono hQu) (Ideal.map_le_iff_le_comap.1 hQ.1.2)⟩
  exact Set.mem_biUnion (show Q ∈ (↑s : Set (Ideal B)) from (hsT Q).2 hQT) hgQ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorLiftOfMulEqP
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem annihilator_lift_of_mul_eq_p : ∀ (p : ℕ) (O : Type) [CommRing O] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), (p : k) = 0 → (p : Λ) ^ 2 = 0 → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], (∀ m : M, (p : Λ) • m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M)) → ∀ ϖ z : O, ϖ * z - (p : O) ∈ Ideal.span {(p : O) ^ 2} → ∀ n : N, ((1 : k) ⊗ₜ[ℤ] ϖ) • n = 0 → n ∈ Ideal.span {a : k ⊗[ℤ] O | ((1 : k) ⊗ₜ[ℤ] ϖ) * a = 0} • (⊤ : Submodule (k ⊗[ℤ] O) N) := by
  intro p O _ Λ _ k _ π hpk hp2 M _ _ _ _ htor N _ _ f hf hker ϖ z hϖz n hn
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hϖz

  have hL : ∀ (c : Λ) (m : M), c • m = (c ⊗ₜ[ℤ] (1 : O)) • m := by
    intro c m
    rw [← smul_one_smul (Λ ⊗[ℤ] O) c m]
    congr 1
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

  have hp2M : ∀ m : M, ((p : Λ) ^ 2) • m = 0 := by intro m; rw [hp2, zero_smul]

  have hpz : ∀ m : M, (p : Λ) • m = ((1 : Λ) ⊗ₜ[ℤ] z) • ((1 : Λ) ⊗ₜ[ℤ] ϖ) • m := by
    intro m
    rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm z ϖ]
    have : ϖ * z = (p : O) + y * (p : O) ^ 2 := by linear_combination -hy
    rw [this, TensorProduct.tmul_add, add_smul]
    have h1 : ((1 : Λ) ⊗ₜ[ℤ] (p : O)) = ((p : Λ) ⊗ₜ[ℤ] (1 : O)) := by
      have e1 : (p : O) = p • (1 : O) := by simp
      have e2 : (p : Λ) = p • (1 : Λ) := by simp
      rw [e1, e2, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have h2 : ((1 : Λ) ⊗ₜ[ℤ] (y * (p : O) ^ 2)) = ((p : Λ) ^ 2) • ((1 : Λ) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [show (y * (p : O) ^ 2) = ((p ^ 2 : ℕ) : ℤ) • y by push_cast; simp [zsmul_eq_mul]; ring]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      push_cast; simp [zsmul_eq_mul]
    rw [h1, h2, ← hL, smul_assoc, hp2M, add_zero]

  have hσp : ∀ m : M, f ((p : Λ) • m) = 0 := by
    intro m
    rw [hL, f.map_smulₛₗ]
    have : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((p : Λ) ⊗ₜ[ℤ] (1 : O)) = 0 := by
      simp [Algebra.TensorProduct.map_tmul, hpk]
    rw [this, zero_smul]
  have hf0 : ∀ m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M), f m = 0 := by
    intro m hm
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hm
    obtain ⟨b, -, rfl⟩ := hm
    exact hσp b
  have hσϖ : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] ϖ) = (1 : k) ⊗ₜ[ℤ] ϖ := by
    simp [Algebra.TensorProduct.map_tmul]
  have hσz : (Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom ((1 : Λ) ⊗ₜ[ℤ] z) = (1 : k) ⊗ₜ[ℤ] z := by
    simp [Algebra.TensorProduct.map_tmul]
  obtain ⟨m, rfl⟩ := hf n
  have h1 : f (((1 : Λ) ⊗ₜ[ℤ] ϖ) • m) = 0 := by rw [f.map_smulₛₗ, hσϖ]; exact hn
  have h2 := hker _ h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨m', -, hm'⟩ := h2
  have h3 : ((1 : Λ) ⊗ₜ[ℤ] ϖ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [smul_sub, ← hm', smul_smul, mul_comm ((1 : Λ) ⊗ₜ[ℤ] ϖ), ← smul_smul, ← hpz, sub_self]
  have h4 : (p : Λ) • (m - ((1 : Λ) ⊗ₜ[ℤ] z) • m') = 0 := by
    rw [hpz, h3, smul_zero]
  have h5 := hf0 _ (htor _ h4)
  have hn' : f m = ((1 : k) ⊗ₜ[ℤ] z) • f m' := by
    rw [map_sub, f.map_smulₛₗ, hσz, sub_eq_zero] at h5; exact h5
  rw [hn']
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  apply Ideal.subset_span
  show ((1 : k) ⊗ₜ[ℤ] ϖ) * ((1 : k) ⊗ₜ[ℤ] z) = 0
  have hw : ϖ * z = ((p : ℤ) • (1 + (p : O) * y)) := by rw [zsmul_eq_mul]; push_cast; linear_combination -hy
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hw, ← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
  push_cast
  rw [hpk, TensorProduct.zero_tmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEInjectiveOfGenericPointMap
section
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory

theorem appLE_injective_of_genericPoint_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (π : Y ⟶ X) (hπ : π (genericPoint Y) = genericPoint X) {U : X.Opens} {V : Y.Opens}
    (hV : (V : Set Y).Nonempty) (h : V ≤ π ⁻¹ᵁ U) :
    Function.Injective (π.appLE U V h).hom := by
  have hy : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hxU : π (genericPoint Y) ∈ U := h hy
  have hF : IsField (X.presheaf.stalk (π (genericPoint Y))) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by rw [hπ]; simp [irreducibleComponents_eq_singleton])
  letI := hF.toField
  have key : ∀ s, (π.stalkMap (genericPoint Y)).hom (X.presheaf.germ U _ hxU s) =
      Y.presheaf.germ V (genericPoint Y) hy ((π.appLE U V h).hom s) := by
    intro s
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp [Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]
  intro s t hst
  apply germ_injective_of_isIntegral X _ hxU
  apply (π.stalkMap (genericPoint Y)).hom.injective
  rw [key, key, hst]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxStep
section
namespace GlobalTheory.FixedPointApproximation

noncomputable def approx {B : Type} [CommRing B] (q : B) (σ : B →+* B) (w : B) : ℕ → B
  | 0 => 0
  | n + 1 => -w + q * σ (approx q σ w n)

theorem approx_step {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B) (n : ℕ) :
    q ^ n ∣ approx q σ w (n + 1) - approx q σ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨σ t, ?_⟩
    have e : approx q σ w (n + 1 + 1) - approx q σ w (n + 1) =
        q * σ (approx q σ w (n + 1) - approx q σ w n) := by
      rw [map_sub]
      show -w + q * σ (approx q σ w (n + 1)) - (-w + q * σ (approx q σ w n)) = _
      ring
    rw [e, ht, map_mul, map_pow, hq]
    ring

theorem approx_dvd {B : Type} [CommRing B] (q : B) (σ : B →+* B) (hq : σ q = q) (w : B)
    (m n : ℕ) (h : m ≤ n) : q ^ m ∣ approx q σ w m - approx q σ w n := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h2 : q ^ m ∣ approx q σ w (n + 1) - approx q σ w n :=
      (pow_dvd_pow q hmn).trans (approx_step q σ hq w n)
    have e : approx q σ w m - approx q σ w (n + 1) =
        (approx q σ w m - approx q σ w n) - (approx q σ w (n + 1) - approx q σ w n) := by ring
    rw [e]
    exact dvd_sub ih h2

theorem smodEq_iff {B : Type} [CommRing B] (q : B) (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule B B)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem exists_fixed {B : Type} [inst : CommRing B] (q : B)
    [h : IsAdicComplete (Ideal.span {q}) B] (σ : B →+* B) (hq : σ q = q) (w : B) :
    ∃ c : B, c = -w + q * σ c := by
  obtain ⟨c, hc⟩ := h.toIsPrecomplete.prec (f := approx q σ w) fun {m n} hmn =>
    (smodEq_iff q m _ _).mpr (approx_dvd q σ hq w m n hmn)
  refine ⟨c, ?_⟩
  have hd : ∀ n, q ^ n ∣ c - (-w + q * σ c) := by
    intro n
    have h1 : q ^ n ∣ approx q σ w n - c := (smodEq_iff q n _ _).mp (hc n)
    have h2 : q ^ (n + 1) ∣ approx q σ w (n + 1) - c := (smodEq_iff q (n + 1) _ _).mp (hc (n + 1))
    obtain ⟨t, ht⟩ := h1
    have e : c - (-w + q * σ c) = -(approx q σ w (n + 1) - c) + q * σ (approx q σ w n - c) := by
      rw [map_sub]
      show _ = -((-w + q * σ (approx q σ w n)) - c) + q * (σ (approx q σ w n) - σ c)
      ring
    rw [e, ht, map_mul, map_pow, hq]
    exact dvd_add (dvd_neg.mpr ((pow_dvd_pow q (Nat.le_succ n)).trans h2)) ⟨q * σ t, by ring⟩
  have h0 := h.toIsHausdorff.haus (c - (-w + q * σ c)) fun n =>
    (smodEq_iff q n _ _).mpr (by simpa using hd n)
  exact sub_eq_zero.mp h0

end GlobalTheory.FixedPointApproximation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPrimeTensorIsDomainIsIntegrallyClosedFaithfulS
section
open IsLocalRing

namespace GlobalTheory

theorem atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul : ∀ (R A : Type) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [FaithfulSMul R A] (p : Ideal R) [p.IsPrime], IsDomain (TensorProduct R (Localization.AtPrime p) A) ∧ IsIntegrallyClosed (TensorProduct R (Localization.AtPrime p) A) ∧ FaithfulSMul (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) := by
  intro R A _ _ _ _ _ _ _ p _
  set Rp := Localization.AtPrime p
  set B := TensorProduct R Rp A
  letI : Algebra A B := Algebra.TensorProduct.rightAlgebra
  have hpush : Algebra.IsPushout R A Rp B := TensorProduct.isPushout'
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) B :=
    (Algebra.isLocalization_iff_isPushout p.primeCompl Rp).mpr hpush
  have hinj : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  have hle : Algebra.algebraMapSubmonoid A p.primeCompl ≤ nonZeroDivisors A := by
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by simpa using h0)
    rw [this]; exact p.zero_mem
  haveI hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hle
  refine ⟨hdom, isIntegrallyClosed_of_isLocalization B _ hle, ?_⟩
  have hAB : Function.Injective (algebraMap A B) := IsLocalization.injective B hle
  refine (faithfulSMul_iff_algebraMap_injective Rp B).mpr ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  have hcomp : ∀ r : R, algebraMap Rp B (algebraMap R Rp r) = algebraMap A B (algebraMap R A r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have h1 : algebraMap Rp B (algebraMap R Rp r) = 0 := by
    have := congrArg (algebraMap Rp B) (IsLocalization.mk'_spec Rp r s)
    rw [map_mul, hx, zero_mul] at this
    exact this.symm
  rw [hcomp] at h1
  have hr : r = 0 := hinj ((hAB (h1.trans (map_zero _).symm)).trans (map_zero _).symm)
  simp [hr]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayCongrModOfIsCoprime
section
theorem GlobalTheory.away_congr_of_isCoprime : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → (∀ c : C, ∃ a : A, c - algebraMap A C a ∈ Ideal.span {algebraMap A C g}) → ∀ c' : Localization.Away (algebraMap A C f), ∃ b : Localization.Away f, c' - Localization.awayMap (algebraMap A C) f b ∈ Ideal.span {Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) g)} := by
  intro A C _ _ _ f g hfg hC c'
  obtain ⟨u, v, huv⟩ := hfg
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C f)) c'
  obtain ⟨k, hk⟩ := s.2
  obtain ⟨a, ha⟩ := hC c
  refine ⟨algebraMap A (Localization.Away f) (a * u ^ k), ?_⟩
  have hmap : ∀ x : A, Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) x)
      = algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C x) :=
    fun x => IsLocalization.map_eq _ _
  rw [hmap, hmap]
  rw [Ideal.mem_span_singleton] at ha ⊢
  have hunit : IsUnit (algebraMap C (Localization.Away (algebraMap A C f)) (s : C)) :=
    IsLocalization.map_units _ s
  rw [← hunit.dvd_mul_right]
  have key : (IsLocalization.mk' (Localization.Away (algebraMap A C f)) c s
      - algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C (a * u ^ k)))
      * algebraMap C (Localization.Away (algebraMap A C f)) (s : C)
      = algebraMap C (Localization.Away (algebraMap A C f)) (c - algebraMap A C (a * (u * f) ^ k)) := by
    rw [sub_mul, IsLocalization.mk'_spec, ← hk]
    simp only [map_sub, map_mul, map_pow]
    ring
  rw [key]
  apply map_dvd
  have h1 : g ∣ a * (1 - (u * f) ^ k) := by
    have h2 : g ∣ 1 - u * f := ⟨v, by rw [← huv]; ring⟩
    have h3 : 1 - u * f ∣ 1 ^ k - (u * f) ^ k := sub_dvd_pow_sub_pow 1 (u * f) k
    rw [one_pow] at h3
    exact Dvd.dvd.mul_left (h2.trans h3) a
  have h4 := map_dvd (algebraMap A C) h1
  have : c - algebraMap A C (a * (u * f) ^ k) = (c - algebraMap A C a) + algebraMap A C (a * (1 - (u * f) ^ k)) := by
    simp only [map_sub, map_mul, map_pow, map_one]; ring
  rw [this]
  exact dvd_add ha h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
section
noncomputable section

namespace GlobalTheory.AffineCurveNbhd

def IsNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
  (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})

theorem awayHom_isUnit {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) :
    IsUnit (((algebraMap A'' (Localization.Away (algebraMap A A'' f))).comp φ.toRingHom) (algebraMap A A' f)) := by
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.Away.algebraMap_isUnit _

def awayHom {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A'' f) :=
  Localization.awayLift ((algebraMap A'' _).comp φ.toRingHom) _ (awayHom_isUnit φ f)

theorem awayHom_comp_algebraMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (algebraMap A' _) = (algebraMap A'' _).comp φ.toRingHom :=
  IsLocalization.Away.lift_comp _ (awayHom_isUnit φ f)

end GlobalTheory.AffineCurveNbhd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPowOfCommutatorEqSmul
section
namespace GlobalTheory.CommutatorPowerFormula

theorem commutator_pow_of_commutator_eq_smul {A : Type} [Ring A] [Algebra ℚ A] {H X : A} {s : ℚ}
    (h : H * X - X * H = s • X) (k : ℕ) :
    H * X ^ k - X ^ k * H = ((k : ℚ) * s) • X ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have e : H * X ^ (n + 1) - X ^ (n + 1) * H
        = (H * X ^ n - X ^ n * H) * X + X ^ n * (H * X - X * H) := by
      rw [pow_succ]
      noncomm_ring
    rw [e, ih, h, smul_mul_assoc, mul_smul_comm, ← pow_succ, ← add_smul]
    congr 1
    push_cast
    ring

end GlobalTheory.CommutatorPowerFormula
end

