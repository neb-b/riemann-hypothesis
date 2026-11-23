module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
section
open IsLocalRing

namespace GlobalTheory.PurityDisc
open TensorProduct

theorem trace_one_tmul (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] [Module.Free R A] [Module.Finite R A] (a : A) :
    Algebra.trace S (S ⊗[R] A) (1 ⊗ₜ a) = algebraMap R S (Algebra.trace R A a) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]

theorem discr_baseChange (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) :
    Algebra.discr S (Algebra.TensorProduct.basis S b) = algebraMap R S (Algebra.discr R b) := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, trace_one_tmul]

theorem trace_pi (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] (z : σ → K) :
    Algebra.trace K (σ → K) z = ∑ i, z i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K σ), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Pi.single_apply]

theorem traceForm_pi_nondegenerate (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] :
    (Algebra.traceForm K (σ → K)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h

theorem discr_ne_zero_of_etale (K A : Type) [Field K] [CommRing A] [Algebra K A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K A) [Algebra.Etale K A] :
    Algebra.discr K b ≠ 0 := by
  classical
  let L := AlgebraicClosure K
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[K] A)
  haveI : Module.Finite L (L ⊗[K] A) := Module.Finite.of_basis (Algebra.TensorProduct.basis L b)
  haveI : IsArtinianRing (L ⊗[K] A) := isArtinian_of_tower L inferInstance
  haveI : Fintype (PrimeSpectrum (L ⊗[K] A)) := Fintype.ofFinite _
  let c := (Algebra.TensorProduct.basis L b).map e.toLinearEquiv
  have hc : Algebra.discr L c ≠ 0 := by
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp
      (traceForm_pi_nondegenerate L (PrimeSpectrum (L ⊗[K] A)))
    rw [Algebra.discr_def]
    convert h using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have h2 : Algebra.discr L c = Algebra.discr L (Algebra.TensorProduct.basis L b) := by
    rw [Algebra.discr_eq_discr_of_algEquiv (Algebra.TensorProduct.basis L b) e]
    rfl
  rw [h2, discr_baseChange] at hc
  intro h
  exact hc (by rw [h, map_zero])

theorem exists_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    ∃ d : ι → A, ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0 := by
  classical
  set M := Algebra.traceMatrix R b
  have hM : IsUnit M.det := by rwa [Algebra.discr_def] at h
  refine ⟨fun j => ∑ k, M⁻¹ k j • b k, fun i j => ?_⟩
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have := congrFun (congrFun h1 i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← this, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp [M, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem formallyUnramified_of_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (d : ι → A)
    (hd : ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0) :
    Algebra.FormallyUnramified R A := by
  classical
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  set T := Algebra.trace R A

  have hrepr : ∀ (z : A) (i : ι), b.repr z i = T (z * d i) := by
    intro z i
    conv_rhs => rw [← b.sum_repr z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp

  have hnd : ∀ u : A, (∀ k, T (u * b k) = 0) → u = 0 := by
    intro u hu
    rw [← b.sum_repr u]
    refine Finset.sum_eq_zero fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrepr, ← b.sum_repr (d j), Finset.mul_sum, map_sum]
    simp_rw [mul_smul_comm, LinearMap.map_smul, hu, smul_zero, Finset.sum_const_zero, zero_smul]

  have hexp : ∀ z : A, ∑ i, T (z * b i) • d i = z := by
    intro z
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, mul_comm (d _) (b k), hd, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨∑ i, b i ⊗ₜ[R] d i, fun s => ?_, ?_⟩
  · rw [sub_mul, sub_eq_zero, Finset.mul_sum, Finset.mul_sum]
    simp_rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    symm
    calc ∑ i, (s * b i) ⊗ₜ[R] d i
        = ∑ i, ∑ j, (T (s * b i * d j) • b j) ⊗ₜ[R] d i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (s * b i)]
          rw [TensorProduct.sum_tmul]
          simp_rw [hrepr]
      _ = ∑ j, b j ⊗ₜ[R] (∑ i, T ((s * d j) * b i) • d i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul]
          congr 2
          ring_nf
      _ = ∑ j, b j ⊗ₜ[R] (s * d j) := by simp_rw [hexp]
  · rw [map_sum]
    simp_rw [Algebra.TensorProduct.lmul'_apply_tmul]
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum]
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hrepr]
    congr 1
    ring

theorem etale_of_isUnit_discr (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    Algebra.Etale R A := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  obtain ⟨d, hd⟩ := exists_dual R A b h
  haveI := formallyUnramified_of_dual R A b d hd
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  haveI : Algebra.FinitePresentation R A := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_height_one_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {x : R}
    (hx : x ≠ 0) (hu : ¬ IsUnit x) : ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ x ∈ P := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨P, hmin, -⟩ := Ideal.exists_minimalPrimes_le hxM
  have hP : P.IsPrime := hmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hmin.1.2
  have : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hP0 : P ≠ ⊥ := fun h => hx (by rw [h] at hxP; exact hxP)
  have h0 : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact ⟨P, hP, le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), hxP⟩

theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A],
    ¬ IsField R →
    (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p)
      (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ hR hp
  classical
  let b := Module.Free.chooseBasis R A
  have key : ∀ p : Ideal R, p.IsPrime → p.height = 1 → Algebra.discr R b ∉ p := by
    intro p hp' h1
    haveI := hp'
    haveI := hp p h1
    let Rp := Localization.AtPrime p
    let κ := ResidueField Rp
    have h := discr_ne_zero_of_etale κ (κ ⊗[Rp] (Rp ⊗[R] A))
      (Algebra.TensorProduct.basis κ (Algebra.TensorProduct.basis Rp b))
    rw [discr_baseChange, discr_baseChange] at h
    have hu : IsUnit (algebraMap R Rp (Algebra.discr R b)) := by
      by_contra hn
      exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Rp p _).mp hu
  have hd : IsUnit (Algebra.discr R b) := by
    by_contra hn
    by_cases h0 : Algebra.discr R b = 0
    · obtain ⟨y, hy0, hyu⟩ : ∃ y : R, y ≠ 0 ∧ ¬ IsUnit y := by
        by_contra H
        push_neg at H
        exact hR ⟨exists_pair_ne R, mul_comm, fun {a} ha => (H a ha).exists_right_inv⟩
      obtain ⟨P, hP, h1, hyP⟩ := exists_height_one_mem R hy0 hyu
      exact key P hP h1 (h0 ▸ P.zero_mem)
    · obtain ⟨P, hP, h1, hdP⟩ := exists_height_one_mem R h0 hn
      exact key P hP h1 hdP
  exact etale_of_isUnit_discr R A b hd

end GlobalTheory.PurityDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleLagrangianTransverseField
section
open Matrix

namespace GlobalTheory

theorem lagr_functional_kills_image {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S A C : Matrix (Fin n) (Fin n) k)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : Fin n → k) (hu : A *ᵥ u = 0) (w : Fin n → k) :
    ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) = 0 := by
  have h := congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso
  simp only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h
  have e1 : u ᵥ* (Aᵀ * S * C.map c) = 0 := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]
  have e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
    congr 1
    funext i
    exact (RingHom.map_mulVec c A w i).symm
  rw [e1, zero_dotProduct, zero_add, e2] at h
  exact h

def lagrRankOne {k : Type} [Field k] {n : ℕ} (S : Matrix (Fin n) (Fin n) k) (j : Fin n) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun a b => if a = j then S b j else 0

theorem lagrRankOne_adm {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hS : Sᵀ = -S.map c) (j : Fin n) :
    (lagrRankOne S j)ᵀ * S + S * (lagrRankOne S j).map c = 0 := by
  ext a b
  have h1 : c (S b j) = - S j b := by
    have h2 : Sᵀ b j = (-S.map c) b j := by rw [hS]
    rw [transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h2
    rw [h2, neg_neg]
  have h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0 := by
    intro l; split_ifs <;> simp
  simp [Matrix.mul_apply, lagrRankOne, h3, h1]

theorem lagrRankOne_mulVec {k : Type} [Field k] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k) :
    lagrRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [lagrRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [lagrRankOne, mulVec, dotProduct, h]

theorem lagr_step {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hSu : IsUnit S.det)
    (A C : Matrix (Fin n) (Fin n) k)
    (hinj : ∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : Fin n → k) (hu0 : u ≠ 0) (hu : A *ᵥ u = 0) :
    ∃ j : Fin n, (∀ w, (A + lagrRankOne S j * C) *ᵥ w = 0 → A *ᵥ w = 0) ∧
      (A + lagrRankOne S j * C) *ᵥ u ≠ 0 := by
  have hx : C *ᵥ u ≠ 0 := fun h => hu0 (hinj u hu h)
  have hxS : (C *ᵥ u) ᵥ* S ≠ 0 := by
    intro h
    have hI : Function.Injective fun v : Fin n → k => v ᵥ* S :=
      vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)
    apply hx
    apply hI
    simp only [h, zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxS
  simp only [Pi.zero_apply] at hj
  refine ⟨j, ?_, ?_⟩
  · intro w hw
    rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec] at hw
    set t := ((C *ᵥ w) ᵥ* S) j with ht
    have hAw : A *ᵥ w = - Pi.single j t := eq_neg_of_add_eq_zero_left hw
    have hφ := lagr_functional_kills_image c S A C hiso u hu w
    have hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t)) := by
      rw [hAw]
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    rw [hc, dotProduct_single] at hφ
    have hct : c t = 0 := by
      rcases mul_eq_zero.mp hφ with h | h
      · exact absurd h hj
      · exact neg_eq_zero.mp h
    have ht0 : t = 0 := (map_eq_zero c).mp hct
    rw [hAw, ht0, Pi.single_zero, neg_zero]
  · rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec, hu, zero_add]
    intro h
    have := congrFun h j
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hj this

theorem lagr_iso_update {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S A C X : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = 0 := by
  have e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c =
      (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem transpose_mul_add_mul_map_eq_zero_add {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S X Y : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0) (hY : Yᵀ * S + S * Y.map c = 0) :
    (X + Y)ᵀ * S + S * (X + Y).map c = 0 := by
  have e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c) := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [e, hX, hY, add_zero]

theorem lagrangian_transverse_field :
    ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  intro k _ c _ _ n S hSu hS A C hinj hiso
  suffices H : ∀ m : ℕ, ∀ A : Matrix (Fin n) (Fin n) k,
      Module.finrank k (LinearMap.ker A.mulVecLin) < m →
      (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from
    H _ A (Nat.lt_succ_self _) hinj hiso
  intro m
  induction m with
  | zero => intro A h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro A hm hinj hiso
    by_cases hdet : IsUnit A.det
    · exact ⟨0, by simp, by simpa using hdet⟩
    · have hd : A.det = 0 := by simpa [isUnit_iff_ne_zero] using hdet
      obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr hd
      obtain ⟨j, hker, hne⟩ := lagr_step c S hSu A C hinj hiso u hu0 hu
      have hX1 := lagrRankOne_adm c S hS j
      have hlt : LinearMap.ker (A + lagrRankOne S j * C).mulVecLin <
          LinearMap.ker A.mulVecLin := by
        refine lt_of_le_of_ne ?_ ?_
        · intro w hw
          simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
          exact hker w hw
        · intro heq
          apply hne
          have hmem : u ∈ LinearMap.ker A.mulVecLin := by
            simpa [LinearMap.mem_ker, mulVecLin_apply] using hu
          rw [← heq] at hmem
          rw [LinearMap.mem_ker, mulVecLin_apply] at hmem
          exact hmem
      have hfin := Submodule.finrank_lt_finrank_of_lt hlt
      have hinj' : ∀ w : Fin n → k, (A + lagrRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0 := by
        intro w h1 h2
        apply hinj w _ h2
        rw [add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero] at h1
        exact h1
      obtain ⟨X2, hX2, hdet2⟩ := ih (A + lagrRankOne S j * C) (by omega) hinj'
        (lagr_iso_update c S A C _ hX1 hiso)
      refine ⟨lagrRankOne S j + X2, transpose_mul_add_mul_map_eq_zero_add c S _ _ hX1 hX2, ?_⟩
      rwa [Matrix.add_mul, ← add_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxUnitPadicTensor
section
open scoped TensorProduct Classical

namespace GlobalTheory.PadicTensorApprox

variable {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem isIntegral_tmul (u : ℚ_[ℓ]) (hu : ‖u‖ ≤ 1) (c : E) (hc : IsIntegral ℤ c) :
    IsIntegral ℤ_[ℓ] (u ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
  have h1 : IsIntegral ℤ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) :=
    map_isIntegral_int (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := E)) hc
  have h2 : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
    obtain ⟨P, hP, hP'⟩ := h1
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hP']
    congr 1
  let v : ℤ_[ℓ] := ⟨u, hu⟩
  have h3 := h2.smul v
  have e : v • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = u ⊗ₜ[ℚ] c := by
    rw [TensorProduct.smul_tmul']
    congr 1
    change u * 1 = u
    exact mul_one u
  rwa [e] at h3

theorem exists_tmul_integral [FiniteDimensional ℚ E] (a : ℚ_[ℓ]) (c : E) :
    ∃ (a' : ℚ_[ℓ]) (c' : E), IsIntegral ℤ c' ∧ (a ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = a' ⊗ₜ[ℚ] c' := by
  have hq : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hz : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq
  obtain ⟨m, hm, hi⟩ := hz.exists_integral_multiple
  refine ⟨((m : ℚ)⁻¹) • a, m • c, hi, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]

theorem pow_mul_tmul (N : ℕ) (a : ℚ_[ℓ]) (c : E) :
    (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * (a ⊗ₜ[ℚ] c) = ((ℓ : ℚ_[ℓ]) ^ N * a) ⊗ₜ[ℚ] c := by
  have : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N = ((ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] (1 : E) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Algebra.TensorProduct.natCast_def]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem exists_pow_mul_isIntegral [FiniteDimensional ℚ E] (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ N : ℕ, IsIntegral ℤ_[ℓ] ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * x) := by
  have hl : IsIntegral ℤ_[ℓ] (ℓ : ℚ_[ℓ] ⊗[ℚ] E) := by
    have := isIntegral_algebraMap (R := ℤ_[ℓ]) (A := ℚ_[ℓ] ⊗[ℚ] E) (x := (ℓ : ℤ_[ℓ]))
    rwa [map_natCast] at this
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact isIntegral_zero⟩
  | add x y hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    refine ⟨M + N, ?_⟩
    have := ((hl.pow N).mul hM).add ((hl.pow M).mul hN)
    have e : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (M + N) * (x + y) = (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * x) +
        (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * y) := by ring
    rwa [e]
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖a'‖ hp
    refine ⟨N, ?_⟩
    rw [e, pow_mul_tmul]
    refine isIntegral_tmul _ ?_ _ hc
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact hN.le

theorem exists_sub_eq_pow_mul [FiniteDimensional ℚ E] (N : ℕ) (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ (b : E) (t : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] t ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = x + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, isIntegral_zero, by simp⟩
  | add x y hx hy =>
    obtain ⟨b, t, ht, e⟩ := hx
    obtain ⟨b', t', ht', e'⟩ := hy
    refine ⟨b + b', t + t', ht.add ht', ?_⟩
    rw [TensorProduct.tmul_add, e, e']
    ring
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    have hl : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    obtain ⟨q, hq⟩ := Padic.rat_dense ℓ a' (ε := ((ℓ : ℝ) ^ N)⁻¹) (by positivity)
    refine ⟨q • c', (((q : ℚ_[ℓ]) - a') / (ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] c', isIntegral_tmul _ ?_ _ hc, ?_⟩
    · rw [norm_div, norm_pow, Padic.norm_p, inv_pow, div_le_one (by positivity), norm_sub_rev]
      exact hq.le
    · rw [e, pow_mul_tmul, ← TensorProduct.add_tmul, ← TensorProduct.smul_tmul]
      congr 1
      rw [Rat.smul_one_eq_cast]
      field_simp
      ring

theorem exists_approx_unit (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) :
    ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_isIntegral ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) : ℚ_[ℓ] ⊗[ℚ] E)
  obtain ⟨b, t, ht, e⟩ := exists_sub_eq_pow_mul (N + 1) (z : ℚ_[ℓ] ⊗[ℚ] E)
  refine ⟨b, _, hN.mul ht, ?_⟩
  have h := z.mul_inv
  rw [e]
  linear_combination (-((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (N + 1) * t)) * h

end GlobalTheory.PadicTensorApprox
end

