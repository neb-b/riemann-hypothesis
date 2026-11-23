module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimAlg
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.CrisFrobeniusIterateEvalEtaleFamily
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem iter_gen {A R ι : Type*} (f : A → A) (φ : R → R) (E : (ι → R) → A)
    (h : ∀ c, f (E c) = E (fun k => φ (c k))) (N : ℕ) (c : ι → R) :
    f^[N] (E c) = E (fun k => φ^[N] (c k)) := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
    simp only [Function.iterate_succ_apply]
    rw [h, ih]

private theorem sl_sum {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A] (σ : R →+* R)
    (f : A →ₛₗ[σ] A) [Fintype ι] (c : ι → R) (x : ι → A) (hx : ∀ k, f (x k) = x k) :
    f (∑ k, c k • x k) = ∑ k, σ (c k) • x k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, hx]

theorem UpperTheory.crisFrobenius_iterate_evalEtaleFamily :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (e : E.EtFam l K), e.Phi → ∀ (M : Model l K) (j n N : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l),
        (phiH M.P n j)^[N] (evE e M j n v c) = evE e M j n v (fun k => (phiA l)^[N] (c k)) := by
  intro l _ K e he M j n N ι _ v c
  exact iter_gen (phiH M.P n j) (phiA l) (fun c => evE e M j n v c)
    (fun c => sl_sum (ACris.phi (K := ℂ_[l]) (p := l)) (M.phiMH n j) c (fun k => e M n j ((v k).lev n))
      (fun k => he M n j _)) N c
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.CrystallineExpansionRelationOfScaledEndomorphism
section
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

private theorem core {F R C : Type} {V : Type*} [Field F] [AddCommGroup V] [Module F V] [CommRing R] [CommRing C] [Algebra F C]
    (c : R →+* C) (φ : C →ₐ[F] C) (φR : R →+* R) (t : R) (ht : IsUnit (c t)) (hφ : ∀ a, φ (c a) = c (φR a))
    (L : ℕ) (hL : (L : F) ≠ 0) (hφt : φR t = (L : R) * t) (f n N r s κ : ℕ) (hκ : (κ : F) ≠ 0)
    {ι : Type} [Fintype ι] (A : Fin (n + 1) → (V →ₗ[F] V)) (v : ι → V) (d : ι → R)
    (w : Fin (n + 1) → ι → V) (σ : Fin (n + 1) → ℤ)
    (hw : ∀ i k, w i k = (L ^ s : ℕ) • A i (v k))
    (hvec : ∑ q : Fin (n + 1) × ι, w q.1 q.2 ⊗ₜ[F] (c ((κ : R) * (((σ q.1 : ℤ) : R) * (L : R) ^ (f * (q.1 : ℕ) * r) *
      φR^[f * (n - q.1 + N)] (d q.2))) * Ring.inverse (c t) ^ 0) = 0) :
    ∑ i : Fin (n + 1), σ i • TensorProduct.map (A i) (φ.toLinearMap ^ (f * (n - i + N)))
      (∑ k, v k ⊗ₜ[F] (c (d k) * Ring.inverse (c t) ^ r)) = 0 := by
  set τ := Ring.inverse (c t) with hτdef
  have hτ : τ * c t = 1 := Ring.inverse_mul_cancel _ ht
  have hpow : ∀ (m : ℕ) (x : C), (φ.toLinearMap ^ m) x = (⇑φ)^[m] x := by
    intro m x
    rw [Module.End.pow_apply]
    rfl
  have hic : ∀ (m : ℕ) (a : R), (⇑φ)^[m] (c a) = c (φR^[m] a) := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hφ, ih]
  have hit : ∀ m : ℕ, φR^[m] t = (L : R) ^ m * t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, hφt, pow_succ]
      ring
  have hτm : ∀ m : ℕ, (⇑φ)^[m] τ * ((L : C) ^ m * c t) = 1 := by
    intro m
    have h2 := congrArg (⇑φ)^[m] hτ
    rw [iterate_map_mul, iterate_map_one, hic, hit, map_mul, map_pow, map_natCast] at h2
    exact h2
  have nat_unit : ∀ a : ℕ, (a : F) ≠ 0 → IsUnit (a : C) := by
    intro a ha
    have := (IsUnit.mk0 _ ha).map (algebraMap F C)
    simpa using this
  set u : C := (κ : C) * (L : C) ^ (s + f * (n + N) * r) * c t ^ r with hu
  have huu : IsUnit u := ((nat_unit κ hκ).mul ((nat_unit L hL).pow _)).mul (ht.pow _)
  obtain ⟨u', hu'⟩ := huu.exists_left_inv
  have hinj : ∀ x : V ⊗[F] C, LinearMap.lTensor V (LinearMap.mulLeft F u) x = 0 → x = 0 := by
    intro x hx
    have hl : ∀ y : V ⊗[F] C, LinearMap.lTensor V (LinearMap.mulLeft F u') (LinearMap.lTensor V (LinearMap.mulLeft F u) y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [← mul_assoc, hu']
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [← hl x, hx, map_zero]
  have hsc : ∀ (i : Fin (n + 1)) (x : R),
      u * (⇑φ)^[f * (n - i + N)] (c x * τ ^ r) =
        (L ^ s : ℕ) • c ((κ : R) * ((L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] x)) := by
    intro i x
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
    have hexp : f * (n + N) * r = f * (n - i + N) * r + f * (i : ℕ) * r := by
      have h1 : n + N = (n - i + N) + i := by omega
      rw [h1]
      ring
    rw [iterate_map_mul, iterate_map_pow, hic, nsmul_eq_mul, Nat.cast_pow, map_mul, map_mul, map_natCast, map_pow,
      map_natCast]
    have h := hτm (f * (n - i + N))
    rw [hu, hexp]
    calc _ = (κ : C) * (L : C) ^ s * (L : C) ^ (f * (i : ℕ) * r) * c (φR^[f * (n - i + N)] x) *
          ((⇑φ)^[f * (n - i + N)] τ * ((L : C) ^ (f * (n - i + N)) * c t)) ^ r := by
          rw [mul_pow, mul_pow, pow_add, pow_add, pow_mul]
          ring
      _ = _ := by
          rw [h, one_pow]
          ring
  have hterm : ∀ (i : Fin (n + 1)) (k : ι),
      σ i • (A i (v k) ⊗ₜ[F] (u * (⇑φ)^[f * (n - i + N)] (c (d k) * τ ^ r))) =
        w i k ⊗ₜ[F] (c ((κ : R) * (((σ i : ℤ) : R) * (L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) * τ ^ 0) := by
    intro i k
    have hy : c ((κ : R) * (((σ i : ℤ) : R) * (L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) =
        σ i • c ((κ : R) * ((L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) := by
      rw [zsmul_eq_mul, ← map_intCast c, ← map_mul]
      congr 1
      ring
    rw [hsc, hw, pow_zero, mul_one, hy]
    generalize c ((κ : R) * ((L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) = y
    generalize A i (v k) = a
    have e1 : a ⊗ₜ[F] ((L ^ s : ℕ) • y) = (L ^ s : ℕ) • (a ⊗ₜ[F] y) := map_nsmul (TensorProduct.mk F V C a) _ y
    have e2 : ((L ^ s : ℕ) • a) ⊗ₜ[F] (σ i • y) = (L ^ s : ℕ) • (a ⊗ₜ[F] (σ i • y)) :=
      map_nsmul ((TensorProduct.mk F V C).flip (σ i • y)) _ a
    have e3 : a ⊗ₜ[F] (σ i • y) = σ i • (a ⊗ₜ[F] y) := map_zsmul (TensorProduct.mk F V C a) _ y
    rw [e1, e2, e3, smul_comm]
  apply hinj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hvec, Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zsmul, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, hpow, hterm i k]

section
variable {l : ℕ} [Fact l.Prime]
private theorem crisFrobenius_cyclotomicPeriod : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul (untilt_epsilon (p := l))
end

theorem UpperTheory.crystalline_expansion_relation_of_scaled_endomorphisms :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K) (j f n N r s κ : ℕ) (_ : κ ≠ 0)
        {ι : Type} [Fintype ι] (A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j)) (v : ι → M.T j) (c : ι → Acris l)
        (w : Fin (n + 1) → ι → M.T j) (σ : Fin (n + 1) → ℤ)
        (_ : ∀ i k, M.toV j (w i k) = (l ^ s : ℕ) • A i (M.toV j (v k)))
        (_ : vec B M j 0 (fun q : Fin (n + 1) × ι => w q.1 q.2)
          (fun q => (κ : Acris l) * (((σ q.1 : ℤ) : Acris l) * (l : Acris l) ^ (f * (q.1 : ℕ) * r) * (phiA l)^[f * (n - q.1 + N)] (c q.2))) = 0),
        ∑ i : Fin (n + 1), σ i • TensorProduct.map (A i) (B.φ.toLinearMap ^ (f * (n - i + N))) (vec B M j r v c) = 0 := by
  intro l _ K B M j f n N r s κ hκ ι _ A v c w σ hw hv
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hκ' : (κ : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hκ
  simp only [vec] at hv ⊢
  exact core (F := ℚ_[l]) (V := M.V j) B.c B.φ (phiA l) (tA l) B.t_unit B.φ_c l hl crisFrobenius_cyclotomicPeriod f n N r s κ hκ' A
    (fun k => M.toV j (v k)) c (fun i k => M.toV j (w i k)) σ hw hv
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.EvalEtaleFamilyMemLimitOfReduced
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

theorem UpperTheory.evalEtaleFamily_mem_limit_of_reduced :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (e : E.EtFam l K), e.Red → ∀ (M : Model l K) (j : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l),
        (fun n => evE e M j n v c) ∈ (M.MS j).lim := by
  intro l _ K e he M j ι _ v c n
  have h2 : ∀ k, GlobalTheory.EtC.red (l ^ (n + 1)) (l ^ n) M.spc (j : ℤ) 0 ((v k).lev (n + 1)) = (v k).lev n :=
    fun k => (show GlobalTheory.EtC.Hl l M.spc j 0 from v k).2 n
  have h3 : ∀ k, (M.MS j).r n (e M (n + 1) j ((v k).lev (n + 1))) = e M n j ((v k).lev n) :=
    fun k => (he M n j ((v k).lev (n + 1))).trans (congrArg (e M n j) (h2 k))
  have hk : ∀ k, (M.MS j).r n (c k • e M (n + 1) j ((v k).lev (n + 1))) = c k • e M n j ((v k).lev n) := by
    intro k
    exact (LinearMap.map_smul ((M.MS j).r n) (c k) _).trans (congrArg (fun y => c k • y) (h3 k))
  exact (map_sum ((M.MS j).r n) _ _).trans (Finset.sum_congr rfl fun k _ => hk k)
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCrystallineLatticeExpansion
section
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

private theorem inverse_pow_raise {A C : Type*} [CommRing A] [CommRing C] (φ : A →+* C) (t a : A) (ht : IsUnit (φ t)) (r s : ℕ) :
    φ a * Ring.inverse (φ t) ^ r = φ (t ^ s * a) * Ring.inverse (φ t) ^ (r + s) := by
  have hi : φ t * Ring.inverse (φ t) = 1 := Ring.mul_inverse_cancel _ ht
  rw [map_mul, map_pow, pow_add]
  calc φ a * Ring.inverse (φ t) ^ r
      = φ a * Ring.inverse (φ t) ^ r * (φ t * Ring.inverse (φ t)) ^ s := by
        rw [hi, one_pow, mul_one]
    _ = _ := by rw [mul_pow]; ring

private theorem eq_mul_inverse_pow {A C : Type*} [CommRing A] [CommRing C] (φ : A →+* C) (t a : A) (ht : IsUnit (φ t)) (r : ℕ) (y : C)
    (h : φ t ^ r * y = φ a) : y = φ a * Ring.inverse (φ t) ^ r := by
  have hi : φ t * Ring.inverse (φ t) = 1 := Ring.mul_inverse_cancel _ ht
  rw [← h]
  calc y = (φ t * Ring.inverse (φ t)) ^ r * y := by rw [hi, one_pow, one_mul]
    _ = _ := by rw [mul_pow]; ring

private theorem vec_raise {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j r s : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) :
    vec B M j r v c = vec B M j (r + s) v (fun k => tA l ^ s * c k) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrArg (fun z => M.toV j (v k) ⊗ₜ[ℚ_[l]] z) (inverse_pow_raise B.c (tA l) (c k) B.t_unit r s)

private theorem vec_sum {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j r : ℕ) {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (v₁ : ι₁ → M.T j) (v₂ : ι₂ → M.T j)
    (c₁ : ι₁ → Acris l) (c₂ : ι₂ → Acris l) :
    vec B M j r v₁ c₁ + vec B M j r v₂ c₂ = vec B M j r (Sum.elim v₁ v₂) (Sum.elim c₁ c₂) :=
  (Fintype.sum_sum_type (fun x => M.toV j (Sum.elim v₁ v₂ x) ⊗ₜ[ℚ_[l]]
    (B.c (Sum.elim c₁ c₂ x) * Ring.inverse (B.c (tA l)) ^ r))).symm

private theorem vec_add_sum_elim {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j r₁ r₂ : ℕ) {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (v₁ : ι₁ → M.T j) (v₂ : ι₂ → M.T j)
    (c₁ : ι₁ → Acris l) (c₂ : ι₂ → Acris l) :
    vec B M j r₁ v₁ c₁ + vec B M j r₂ v₂ c₂ = vec B M j (r₁ + r₂) (Sum.elim v₁ v₂)
      (Sum.elim (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k)) := by
  have e₁ : vec B M j r₁ v₁ c₁ = vec B M j (r₁ + r₂) v₁ (fun k => tA l ^ r₂ * c₁ k) :=
    vec_raise B M j r₁ r₂ v₁ c₁
  have e₂ : vec B M j r₂ v₂ c₂ = vec B M j (r₁ + r₂) v₂ (fun k => tA l ^ r₁ * c₂ k) :=
    (Nat.add_comm r₂ r₁) ▸ vec_raise B M j r₂ r₁ v₂ c₂
  exact (congrArg₂ HAdd.hAdd e₁ e₂).trans
    (vec_sum B M j (r₁ + r₂) v₁ v₂ (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k))

private theorem vec_add {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) (x y : M.V j ⊗[ℚ_[l]] B.C)
    (hx : ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), x = vec B M j r v c)
    (hy : ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), y = vec B M j r v c) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), x + y = vec B M j r v c := by
  obtain ⟨ι₁, i₁, v₁, c₁, r₁, h₁⟩ := hx
  obtain ⟨ι₂, i₂, v₂, c₂, r₂, h₂⟩ := hy
  exact ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim v₁ v₂,
    Sum.elim (fun k => tA l ^ r₂ * c₁ k) (fun k => tA l ^ r₁ * c₂ k), r₁ + r₂,
    (congrArg₂ HAdd.hAdd h₁ h₂).trans (vec_add_sum_elim B M j r₁ r₂ v₁ v₂ c₁ c₂)⟩

private theorem vec_pure {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) (h : M.T j) (y : B.C) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
      M.toV j h ⊗ₜ[ℚ_[l]] y = vec B M j r v c := by
  obtain ⟨r, a, ha⟩ := B.loc y
  refine ⟨Unit, inferInstance, fun _ => h, fun _ => a, r, ?_⟩
  have hy : y = B.c a * Ring.inverse (B.c (tA l)) ^ r := eq_mul_inverse_pow B.c (tA l) a B.t_unit r y ha
  have e : vec B M j r (fun _ : Unit => h) (fun _ => a) = M.toV j h ⊗ₜ[ℚ_[l]] (B.c a * Ring.inverse (B.c (tA l)) ^ r) :=
    Fintype.sum_unique _
  rw [e, ← hy]

private theorem vec_zero {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
      (0 : M.V j ⊗[ℚ_[l]] B.C) = vec B M j r v c :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, 0, (Fintype.sum_empty _).symm⟩

private theorem vec_tmul {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K)
    (j : ℕ) (a : M.V j) :
    ∀ y : B.C, ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
      a ⊗ₜ[ℚ_[l]] y = vec B M j r v c := by
  have key : ∀ a' : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0, ∀ y : B.C,
      ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ),
        (show M.V j from a') ⊗ₜ[ℚ_[l]] y = vec B M j r v c := by
    intro a'
    induction a' using TensorProduct.induction_on with
    | zero =>
      intro y
      have e : (show M.V j from (0 : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) ⊗ₜ[ℚ_[l]] y = 0 :=
        TensorProduct.zero_tmul _ _
      rw [e]
      exact vec_zero B M j
    | tmul q h =>
      intro y
      have e : (show M.V j from (q ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) =
          q • M.toV j (show M.T j from h) := by
        change (q ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0) =
          q • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, TensorProduct.smul_tmul]
      exact vec_pure B M j _ _
    | add a₁ a₂ h₁ h₂ =>
      intro y
      have e : (show M.V j from (a₁ + a₂ : ℚ_[l] ⊗[ℤ_[l]] GlobalTheory.EtC.Hl l M.spc j 0)) ⊗ₜ[ℚ_[l]] y =
          (show M.V j from a₁) ⊗ₜ[ℚ_[l]] y + (show M.V j from a₂) ⊗ₜ[ℚ_[l]] y :=
        TensorProduct.add_tmul _ _ _
      rw [e]
      exact vec_add B M j _ _ (h₁ y) (h₂ y)
  exact key a

theorem UpperTheory.exists_crystalline_lattice_expansion :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K) (j : ℕ) (x : M.V j ⊗[ℚ_[l]] B.C),
        ∃ (ι : Type) (_ : Fintype ι) (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), x = vec B M j r v c := by
  intro l _ K B M j x
  induction x using TensorProduct.induction_on with
  | zero => exact vec_zero B M j
  | tmul a y => exact vec_tmul B M j a y
  | add x y hx hy => exact vec_add B M j x y hx hy
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.HeckeCorrespondenceProduct
section
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

private theorem pow_mul_int (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    ∃ (s : ℕ) (c : ℤ_[l]), ((l ^ s : ℕ) : ℚ_[l]) * q = (c : ℚ_[l]) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt ‖q‖ hl
  have hpos : (0 : ℝ) < (l : ℝ) ^ s := by positivity
  refine ⟨s, ⟨((l ^ s : ℕ) : ℚ_[l]) * q, ?_⟩, rfl⟩
  rw [PadicInt.mem_subring_iff, norm_mul]
  push_cast
  rw [norm_pow, Padic.norm_p, inv_pow, inv_mul_le_one₀ hpos]
  exact hs.le

private theorem exists_int {l : ℕ} [Fact l.Prime] {H : Type*} [AddCommGroup H] [Module ℤ_[l] H]
    (a : ℚ_[l] ⊗[ℤ_[l]] H) : ∃ (s : ℕ) (h : H), (l ^ s : ℕ) • a = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul q x =>
    obtain ⟨s, c, hc⟩ := pow_mul_int l q
    refine ⟨s, c • x, ?_⟩
    have hq : ((l ^ s : ℕ) : ℚ_[l]) • q = c • (1 : ℚ_[l]) := by
      rw [smul_eq_mul, hc, Algebra.smul_def, mul_one]
      rfl
    rw [← Nat.cast_smul_eq_nsmul ℚ_[l], TensorProduct.smul_tmul', hq, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨s, h, e⟩ := ha
    obtain ⟨t, k, f⟩ := hb
    refine ⟨s + t, (l ^ t : ℕ) • h + (l ^ s : ℕ) • k, ?_⟩
    have e1 : (l ^ (s + t) : ℕ) • a = (l ^ t : ℕ) • (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h := by
      rw [← e, smul_smul, pow_add, mul_comm]
    have e2 : (l ^ (s + t) : ℕ) • b = (l ^ s : ℕ) • (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] k := by
      rw [← f, smul_smul, pow_add]
    have t1 : ∀ (c : ℕ) (x : H), c • (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (c • x) :=
      fun c x => (map_nsmul (TensorProduct.mk ℤ_[l] ℚ_[l] H 1) c x).symm
    rw [smul_add, e1, e2, TensorProduct.tmul_add, t1, t1]

private theorem exists_kill {l : ℕ} [Fact l.Prime] {H : Type*} [AddCommGroup H] [Module ℤ_[l] H]
    (h : H) (e : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] h = 0) : ∃ b : ℕ, (l ^ b : ℕ) • h = 0 :=
  _root_.UpperTheory.Reformulated.B.Qk55.exists_kill h e

private theorem exists_ub {α : Type*} [Fintype α] (f : α → ℕ) : ∃ s, ∀ a, f a ≤ s :=
  ⟨Finset.univ.sup f, fun a => Finset.le_sup (Finset.mem_univ a)⟩

private theorem pullV_toV {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M N : Model l K}
    (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (x : N.T n) :
    Model.pullV u hu n (N.toV n x) = M.toV n (Model.pullT u hu n x) := by
  simp only [Model.pullV, Model.toV, Model.pullT, GlobalTheory.EtC.pullHQ]
  exact LinearMap.baseChange_tmul _ _ _

private theorem toV_nsmul {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n c : ℕ)
    (x : M.T n) : M.toV n (c • x) = c • M.toV n x :=
  map_nsmul (TensorProduct.mk ℤ_[l] ℚ_[l] (GlobalTheory.EtC.Hl l M.spc n 0) 1) c x

private theorem toV_sub {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ)
    (x y : M.T n) : M.toV n (x - y) = M.toV n x - M.toV n y :=
  map_sub (TensorProduct.mk ℤ_[l] ℚ_[l] (GlobalTheory.EtC.Hl l M.spc n 0) 1) x y

private theorem toV_sum {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ)
    {α : Type*} (t : Finset α) (f : α → M.T n) : M.toV n (∑ a ∈ t, f a) = ∑ a ∈ t, M.toV n (f a) :=
  map_sum (TensorProduct.mk ℤ_[l] ℚ_[l] (GlobalTheory.EtC.Hl l M.spc n 0) 1) f t

theorem UpperTheory.hecke_correspondence_product :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M W : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p) (j n : ℕ)
        (T : Fin (n + 1) → Corr l M.X) (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p)
        (A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j)) (_ : ∀ i, IsHk M (T i) (hr i) j (A i))
        (z : ∀ i, Fin (T i).d → (W.X ⟶ (T i).Z)) (hz : ∀ i a, z i a ≫ (T i).p = π)
        (_ : ∀ i (X : Scheme.{0}) (y : X ⟶ W.X), IsUnit (l : Γ(X, ⊤)) → SplitOn (T i).p (y ≫ π) fun a => y ≫ z i a)
        {ι : Type} [Fintype ι] (v : ι → M.T j),
        ∃ (s b : ℕ) (w : Fin (n + 1) → ι → M.T j), (∀ i k, M.toV j (w i k) = (l ^ s : ℕ) • A i (M.toV j (v k))) ∧
          ∀ i k, (l ^ b : ℕ) • Model.pullT π hπ j (w i k) = (l ^ (s + b) : ℕ) •
            ∑ a, Model.pullT (z i a ≫ (T i).r) (by rw [Category.assoc, hr, ← Category.assoc, hz, hπ]) j (v k) := by
  intro l _ K M W π hπ j n T hr A hA z hz hsp ι _ v
  have h1 : ∀ (i : Fin (n + 1)) (k : ι), ∃ (s : ℕ) (h : M.T j), (l ^ s : ℕ) • A i (M.toV j (v k)) = M.toV j h :=
    fun i k => exists_int (H := GlobalTheory.EtC.Hl l M.spc j 0) (A i (M.toV j (v k)))
  choose s' h hs' using h1
  obtain ⟨s, hs⟩ := exists_ub (fun p : Fin (n + 1) × ι => s' p.1 p.2)
  have hle : ∀ i k, s' i k ≤ s := fun i k => hs (i, k)
  let w : Fin (n + 1) → ι → M.T j := fun i k => (l ^ (s - s' i k) : ℕ) • h i k
  have hw : ∀ i k, M.toV j (w i k) = (l ^ s : ℕ) • A i (M.toV j (v k)) := by
    intro i k
    have e : (l ^ s : ℕ) = l ^ (s - s' i k) * l ^ s' i k := by rw [← pow_add, Nat.sub_add_cancel (hle i k)]
    rw [e, mul_smul, hs', toV_nsmul]
  let d : ∀ i k, W.T j := fun i k => Model.pullT π hπ j (w i k) - (l ^ s : ℕ) •
    ∑ a, Model.pullT (z i a ≫ (T i).r) (by rw [Category.assoc, hr, ← Category.assoc, hz, hπ]) j (v k)
  have hd : ∀ i k, W.toV j (d i k) = 0 := by
    intro i k
    simp only [d]
    rw [toV_sub, toV_nsmul, toV_sum, ← pullV_toV, hw, map_nsmul, hA i W π hπ (z i) (hz i) (hsp i)]
    simp only [pullV_toV, sub_self]
  have h2 : ∀ i k, ∃ b : ℕ, (l ^ b : ℕ) • d i k = 0 := fun i k =>
    exists_kill (H := GlobalTheory.EtC.Hl l W.spc j 0) (d i k) (hd i k)
  choose b' hb' using h2
  obtain ⟨b, hb⟩ := exists_ub (fun p : Fin (n + 1) × ι => b' p.1 p.2)
  refine ⟨s, b, w, hw, fun i k => ?_⟩
  have e : (l ^ b : ℕ) = l ^ (b - b' i k) * l ^ b' i k := by rw [← pow_add, Nat.sub_add_cancel (hb (i, k))]
  have hz0 : (l ^ b : ℕ) • d i k = 0 := by rw [e, mul_smul, hb', smul_zero]
  simp only [d] at hz0
  rw [smul_sub, sub_eq_zero] at hz0
  rw [hz0, smul_smul, pow_add, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.LinearCombinationTransferOfProjectorRelations
section
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.linear_combination_transfer_of_projector_relations :
    ∀ {A : Type} [CommRing A] {H H' : Type 1} [AddCommGroup H] [Module A H] [AddCommGroup H'] [Module A H']
        {J ι : Type} [Fintype J] [Fintype ι] {I : J → Type} [∀ i, Fintype (I i)] (G : H →ₗ[A] H') (P : ∀ i, I i → (H →ₗ[A] H'))
        (Ev : ι → H) (Wc : J → ι → H) (β γ L R : A) (σ : J → ℤ) (ρ : J → A) (cc : J → ι → A) (Z : J → H)
        (_ : ∀ i k, β • G (Wc i k) = γ • ∑ a, P i a (Ev k))
        (_ : ∀ i, (L * ρ i) • ∑ k, cc i k • Ev k = R • Z i)
        (_ : ∑ x : Σ i, I i, σ x.1 • P x.1 x.2 (Z x.1) = 0),
        (L * β) • G (∑ q : J × ι, ((σ q.1 : A) * ρ q.1 * cc q.1 q.2) • Wc q.1 q.2) = 0 := by
  intro A _ H H' _ _ _ _ J ι _ _ I _ G P Ev Wc β γ L R σ ρ cc Z h1 h2 h3
  have hi : ∀ i, ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k)) = (γ * R) • ∑ a, P i a (Z i) := by
    intro i
    have e1 : ∀ a, ∑ k, (L * ρ i * cc i k) • P i a (Ev k) = R • P i a (Z i) := by
      intro a
      have := congrArg (P i a) (h2 i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_smul, map_sum, Finset.smul_sum, smul_smul] at this
      simpa only [mul_assoc] using this
    calc ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k))
        = ∑ k, (L * ρ i * cc i k) • (γ • ∑ a, P i a (Ev k)) := by simp only [h1]
      _ = γ • ∑ a, ∑ k, (L * ρ i * cc i k) • P i a (Ev k) := by
          rw [Finset.sum_comm]
          simp only [Finset.smul_sum, smul_comm γ]
      _ = (γ * R) • ∑ a, P i a (Z i) := by
          rw [Finset.sum_congr rfl fun a _ => e1 a, mul_smul, ← Finset.smul_sum]
  have h3' : ∑ i, (σ i : A) • ∑ a, P i a (Z i) = 0 := by
    rw [Fintype.sum_sigma] at h3
    simpa only [Finset.smul_sum, Int.cast_smul_eq_zsmul] using h3
  calc (L * β) • G (∑ q : J × ι, ((σ q.1 : A) * ρ q.1 * cc q.1 q.2) • Wc q.1 q.2)
      = ∑ i, (σ i : A) • ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k)) := by
        rw [Fintype.sum_prod_type]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        congr 1
        ring
    _ = (γ * R) • ∑ i, (σ i : A) • ∑ a, P i a (Z i) := by
        simp only [hi, Finset.smul_sum (s := Finset.univ) (r := γ * R), smul_comm (γ * R)]
    _ = 0 := by rw [h3', smul_zero]
end

