module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
section
namespace UpperTheory.ConvolutionTheory.D

section

variable {S T : Type} [CommRing S] [CommRing T] [Algebra S T]

private theorem pow_succ_app (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = σ ((σ ^ j) t) := by
  rw [pow_succ', AlgEquiv.mul_apply]

private theorem pow_succ_app' (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = (σ ^ j) (σ t) := by
  rw [pow_succ, AlgEquiv.mul_apply]

private theorem exists_notMem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a : T)
    (ha : ∏ i ∈ Finset.range q, (σ ^ i) a = 1) (P : Ideal T) (hP : P ≠ ⊤) :
    ∃ z, a * σ z = z ∧ z ∉ P := by
  obtain ⟨s, x, y, hxy⟩ := h.sep
  let c : ℕ → T := fun j => ∏ i ∈ Finset.range j, (σ ^ i) a
  have hc : ∀ j, a * σ (c j) = c (j + 1) := by
    intro j
    simp only [c]
    rw [Finset.prod_range_succ', map_prod, mul_comm]
    simp only [pow_succ_app, pow_zero, AlgEquiv.one_apply]
  let z : T → T := fun t => ∑ j ∈ Finset.range q, c j * (σ ^ j) t
  have hz : ∀ t, a * σ (z t) = z t := by
    intro t
    have h1 : a * σ (z t) = ∑ j ∈ Finset.range q, c (j + 1) * (σ ^ (j + 1)) t := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [z, map_sum, Finset.mul_sum, map_mul, ← hc, pow_succ_app, mul_assoc]
    have h2 := Finset.sum_range_succ (fun j => c j * (σ ^ j) t) q
    rw [Finset.sum_range_succ'] at h2
    have h3 : c q = 1 := ha
    have h4 : c 0 = 1 := by simp [c]
    rw [h3, h4, h.pow, pow_zero] at h2
    rw [h1]
    exact add_right_cancel h2
  have hs : ∑ i, x i * z (y i) = 1 := by
    have : ∑ i, x i * z (y i) = ∑ j ∈ Finset.range q, c j * ∑ i, x i * (σ ^ j) (y i) := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_eq_single 0]
    · rw [hxy 0 h.pos]; simp [c]
    · intro j hj hj0
      rw [hxy j (Finset.mem_range.1 hj), if_neg hj0, mul_zero]
    · intro h0
      exact absurd (Finset.mem_range.2 h.pos) h0
  by_contra hcon
  push Not at hcon
  apply hP
  rw [Ideal.eq_top_iff_one, ← hs]
  exact P.sum_mem fun i _ => P.mul_mem_left _ (hcon _ (hz _))

private theorem mem_of_mem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a z : T) (hz : a * σ z = z)
    (P Q : Ideal T) [Q.IsPrime] (hPQ : P.comap (algebraMap S T) = Q.comap (algebraMap S T))
    (hzP : z ∈ P) : z ∈ Q := by
  have hd : ∀ j, (σ ^ j) z ∣ z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine dvd_trans ?_ ih
      rw [pow_succ_app']
      conv_rhs => rw [← hz, map_mul]
      exact dvd_mul_left _ _
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := h.pos; omega⟩
  have hN : σ (∏ j ∈ Finset.range (r + 1), (σ ^ j) z) = ∏ j ∈ Finset.range (r + 1), (σ ^ j) z := by
    rw [map_prod]
    simp only [← pow_succ_app]
    rw [Finset.prod_range_succ, h.pow, Finset.prod_range_succ' _ r, pow_zero]
  obtain ⟨n, hn⟩ := h.fix _ hN
  have h1 : algebraMap S T n ∈ P := by
    rw [hn, Finset.prod_range_succ']
    exact P.mul_mem_left _ (by simpa using hzP)
  have h2 : algebraMap S T n ∈ Q := by
    rw [← Ideal.mem_comap, ← hPQ]; exact h1
  rw [hn, Ideal.IsPrime.prod_mem_iff] at h2
  obtain ⟨j, -, hj⟩ := h2
  exact Q.mem_of_dvd (hd j) hj

end

private theorem finite_max (k S : Type) [CommRing k] [IsLocalRing k] [CommRing S] [Algebra k S]
    [Module.Finite k S] : Finite (MaximalSpectrum S) := by
  have hf := Algebra.QuasiFinite.finite_primesOver (R := k) (S := S) (IsLocalRing.maximalIdeal k)
  have : Finite ((IsLocalRing.maximalIdeal k).primesOver S) := hf
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal k).primesOver S)
    (fun m => ⟨m.asIdeal, m.isMaximal.isPrime, ⟨?_⟩⟩) ?_
  · have := m.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := k) m.asIdeal)).symm
  · intro m m' hm
    exact MaximalSpectrum.ext (congrArg Subtype.val hm)

theorem h90 : H90 := by
  intro k R _ _ _ _ S T _ _ _ _ _ σ q h a ha
  classical
  have hfin : Module.Finite S T := (galBase S T S σ q h).1
  have := finite_max k S
  have := Fintype.ofFinite (MaximalSpectrum S)
  have hloc : ∀ m : MaximalSpectrum S, ∃ z : T, a * σ z = z ∧
      ∀ P : Ideal T, P.IsMaximal → P.comap (algebraMap S T) = m.asIdeal → z ∉ P := by
    intro m
    by_cases hm : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.comap (algebraMap S T) = m.asIdeal
    · obtain ⟨Q, hQ, hQm⟩ := hm
      obtain ⟨z, hz, hzQ⟩ := exists_notMem h a ha Q hQ.ne_top
      exact ⟨z, hz, fun P _ hP hzP => hzQ (mem_of_mem h a z hz P Q (hP.trans hQm.symm) hzP)⟩
    · exact ⟨0, by simp, fun P hP hPm => (hm ⟨P, hP, hPm⟩).elim⟩
  choose z hz hzP using hloc
  have he : ∀ m : MaximalSpectrum S, ∃ e : S, e - 1 ∈ m.asIdeal ∧ ∀ m', m' ≠ m → e ∈ m'.asIdeal := by
    intro m
    obtain ⟨e, he⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum S => m.asIdeal)
      (fun m m' hne => MaximalSpectrum.isCoprime_of_ne hne) (Pi.single m 1)
    refine ⟨e, ?_, fun m' hne => ?_⟩
    · rw [← Ideal.Quotient.eq, he m, Pi.single_eq_same, map_one]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, he m', Pi.single_eq_of_ne hne]
  choose e he1 he0 using he
  have hu : IsUnit (∑ m, algebraMap S T (e m) * z m) := by
    by_contra hnu
    obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    let m : MaximalSpectrum S := ⟨P.comap (algebraMap S T), Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S) P⟩
    apply hzP m P hP rfl
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at hmem
    have h1 : ∑ m' ∈ Finset.univ.erase m, algebraMap S T (e m') * z m' ∈ P :=
      P.sum_mem fun m' hm' => P.mul_mem_right _ (he0 m' m (Finset.ne_of_mem_erase hm').symm)
    have h2 : algebraMap S T (e m - 1) * z m ∈ P := P.mul_mem_right _ (he1 m)
    have h3 := P.sub_mem (P.sub_mem hmem h1) h2
    rw [map_sub, map_one] at h3
    convert h3 using 1
    ring
  refine ⟨hu.unit, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hu.unit_spec, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, σ.commutes, mul_left_comm, hz]

end UpperTheory.ConvolutionTheory.D
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalExt
section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.galExt :
    UpperTheory.ConvolutionTheory.D.GalExt := by
  intro F E k _ _ _ _ _ σ q h
  exact (UpperTheory.ConvolutionTheory.D.galBase F E k σ q h).2.2.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmCent
section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem cent_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem cent_nm_sg (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ q (sg σ d) = sg σ (nm σ q d) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ext a b
  change (σ ^ m) (σ _) = σ ((σ ^ m) _)
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_succ, ← pow_succ']

private theorem cent_up_inj (h : Function.Injective (algebraMap k R)) :
    Function.Injective (up R : GL (Fin n) k → GL (Fin n) R) := by
  intro s t hst
  ext a b
  exact h (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hst)

private theorem cent_descend {σ : R ≃ₐ[k] R} {q : ℕ} (hσ : IsGal σ q) (x : GL (Fin n) R) (hx : sg σ x = x) :
    ∃ t : GL (Fin n) k, x = up R t := by
  have key : ∀ y : GL (Fin n) R, sg σ y = y → ∃ M : Matrix (Fin n) (Fin n) k,
      M.map (algebraMap k R) = (y : Matrix (Fin n) (Fin n) R) := by
    intro y hy
    have h : ∀ a b, ∃ c, algebraMap k R c = (y : Matrix (Fin n) (Fin n) R) a b := fun a b =>
      hσ.fix _ (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) a b) hy)
    choose M hM using h
    exact ⟨Matrix.of M, by ext a b; exact hM a b⟩
  obtain ⟨M, hM⟩ := key x hx
  obtain ⟨N, hN⟩ := key x⁻¹ (by rw [map_inv, hx])
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) hσ.inj
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext hM.symm⟩
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.mul_inv]
  · dsimp only
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), Units.inv_mul]

end

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.nmCent :
    UpperTheory.ConvolutionTheory.D.NmCent := by
  intro k R _ _ _ _ σ q hσ n a γ hsep ha x
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rw [cp, ← Matrix.charpoly_map] at h
    exact h
  have hc := (conjSep k R n _ hs).2.1
  have hfix : ∀ y, nm σ q (sgConj σ y a) = up R γ → y * up R γ = up R γ * y := by
    intro y hy
    rw [(nmPoly k R σ q hσ n a).2 y, ha, mul_assoc, inv_mul_eq_iff_eq_mul] at hy
    exact hy.symm
  have hag : a * up R γ = up R γ * a := by
    apply hfix
    rw [sgConj, inv_mul_cancel, one_mul, cent_nm_sg, ha, cent_sg_up]
  have hcomm : ∀ y : GL (Fin n) R, y * up R γ = up R γ * y → a * y = y * a := by
    intro y hy
    obtain ⟨p, hp⟩ := hc a.val (by simpa using congrArg Units.val hag)
    obtain ⟨p', hp'⟩ := hc y.val (by simpa using congrArg Units.val hy)
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hp, hp', ← map_mul, ← map_mul, mul_comm]
  constructor
  · intro hx
    have h1 := hfix x (by rw [hx, ha])
    have h2 := hcomm x h1
    have h3 : sg σ x = x := by
      rw [sgConj, mul_assoc, inv_mul_eq_iff_eq_mul, ← h2] at hx
      exact mul_left_cancel hx
    obtain ⟨t, rfl⟩ := cent_descend hσ x h3
    refine ⟨t, cent_up_inj hσ.inj ?_, rfl⟩
    rw [map_mul, map_mul, h1]
  · rintro ⟨t, ht, rfl⟩
    have h2 := hcomm (up R t) (by rw [← map_mul, ← map_mul, ht.eq])
    rw [sgConj, cent_sg_up, mul_assoc, h2, inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormProd
section
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

section SlopeTestRemainingChoices

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

private lemma tr_mem {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) (y : R) :
    ∃ t : k, algebraMap k R t = ∑ j ∈ Finset.range q, (σ ^ j) y := by
  apply h.fix
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have h1 := Finset.sum_range_succ (fun j => (σ ^ j) y) q
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) y) q
  rw [h2, h.pow, pow_zero] at h1
  have h3 := add_right_cancel h1
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

private lemma expand {σ : R ≃ₐ[k] R} {q s : ℕ} (hq : 0 < q) {x y : Fin s → R}
    (hs : ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0) (r : R) :
    ∑ i, (∑ j ∈ Finset.range q, (σ ^ j) (y i * r)) * x i = r := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ j ∈ Finset.range q, ∑ i, (σ ^ j) (y i * r) * x i = if j = 0 then r else 0 := by
    intro j hj
    have := hs j (Finset.mem_range.1 hj)
    have h2 : ∑ i, (σ ^ j) (y i * r) * x i = (∑ i, x i * (σ ^ j) (y i)) * (σ ^ j) r := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    rw [h2, this]
    split_ifs with h0
    · simp [h0]
    · simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' ]
  simp [hq]

private def phi (σ : R ≃ₐ[k] R) (q : ℕ) : R ⊗[k] R →ₐ[R] (Fin q → R) :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Fin q → R))
    (Pi.algHom k _ fun j : Fin q => ((σ ^ (j : ℕ) : R ≃ₐ[k] R) : R →ₐ[k] R)) fun _ _ => Commute.all _ _

private lemma phi_tmul (σ : R ≃ₐ[k] R) (q : ℕ) (a b : R) (j : Fin q) :
    phi σ q (a ⊗ₜ b) j = a * (σ ^ (j : ℕ)) b := by
  simp [phi, Algebra.ofId_apply]

private lemma phi_inj {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Function.Injective (phi σ q) := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  have key : ∀ z : R ⊗[k] R, ∑ i, (∑ j : Fin q, (σ ^ (j : ℕ)) (y i) * phi σ q z j) ⊗ₜ[k] x i = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      simp only [map_add (f := _), Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul, hu, hv]
    | tmul a b =>
      choose t ht using fun i => tr_mem h (y i * b)
      have hb := expand h.pos hs b
      conv_rhs => rw [← hb, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ht, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ht,
        Finset.sum_range, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [phi_tmul, map_mul]; ring
  intro u v huv
  rw [← key u, ← key v, huv]

private lemma phi_surj {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Function.Surjective (phi σ q) := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  have key : ∀ m j : Fin q, phi σ q (∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i)) j = if j = m then 1 else 0 := by
    intro m j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    simp_rw [phi_tmul, ← AlgEquiv.mul_apply, ← pow_add]
    rw [pow_eq_pow_mod _ h.pow, hs _ (Nat.mod_lt _ h.pos)]
    have hm := m.2
    have hj := j.2
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff]
    rcases lt_or_ge (j : ℕ) m with hl | hl
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  intro f
  refine ⟨∑ m : Fin q, f m • ∑ i, x i ⊗ₜ[k] (σ ^ (q - m)) (y i), ?_⟩
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  simp_rw [map_smul, Pi.smul_apply, key]
  simp

private lemma fin {σ : R ≃ₐ[k] R} {q : ℕ} (h : IsGal σ q) : Module.Finite k R := by
  obtain ⟨s, x, y, hs⟩ := h.sep
  refine Module.Finite.of_surjective (Fintype.linearCombination k x) fun b => ?_
  choose t ht using fun i => tr_mem h (y i * b)
  refine ⟨t, ?_⟩
  rw [Fintype.linearCombination_apply]
  simp_rw [Algebra.smul_def, ht]
  exact expand h.pos hs b

private lemma norm_pi {q : ℕ} (f : Fin q → R) : Algebra.norm R f = ∏ j, f j := by
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun R (Fin q)), ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.D

theorem UpperTheory.ConvolutionTheory.D.normProd :
    UpperTheory.ConvolutionTheory.D.NormProd := by
  intro k R _ _ _ _ σ q h r
  haveI := UpperTheory.ConvolutionTheory.D.fin h
  have h1 : algebraMap k R (Algebra.norm k r) = Algebra.norm R ((1 : R) ⊗ₜ[k] r) := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
    congr 1
    ext b
    simp
  let e := AlgEquiv.ofBijective (UpperTheory.ConvolutionTheory.D.phi σ q) ⟨UpperTheory.ConvolutionTheory.D.phi_inj h, UpperTheory.ConvolutionTheory.D.phi_surj h⟩
  rw [h1, ← Algebra.norm_eq_of_algEquiv e, UpperTheory.ConvolutionTheory.D.norm_pi, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (UpperTheory.ConvolutionTheory.D.phi_tmul σ q 1 r j).trans (one_mul _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.RepNmSucc
section
noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem rep_sg_succ (σ : R ≃ₐ[k] R) (i : ℕ) (d : GL (Fin n) R) :
    sg (σ ^ (i + 1)) d = sg σ (sg (σ ^ i) d) := by
  ext a b
  simp [sg, pow_succ', Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_one (d : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) d = d := by
  ext a b
  simp [sg, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_nm_succ (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ (q + 1) d = nm σ q d * sg (σ ^ q) d := by
  simp [nm, List.range_succ]

private theorem rep_shift (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    d * sg σ (nm σ q d) = nm σ q d * sg (σ ^ q) d := by
  induction q with
  | zero => simp [nm, rep_sg_one]
  | succ q ih => rw [rep_nm_succ, map_mul, ← mul_assoc, ih, rep_sg_succ]

private theorem rep_cp_up (γ : GL (Fin n) k) : cp (up R γ) = (cp γ).map (algebraMap k R) := by
  rw [cp, cp, ← Matrix.charpoly_map]
  rfl

end

theorem nmRep : NmRep := by
  intro k R _ _ _ _ σ q hσ n δ γ hsep hcp
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((nm σ q δ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rwa [← hcp] at h
  obtain ⟨x, hx⟩ := (conjSep k R n _ hs).1 ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
    ((rep_cp_up γ).trans hcp.symm)
  have hx' : nm σ q δ * x = x * up R γ := Units.ext (by simpa using hx)
  have h1 : nm σ q (sgConj σ x δ) = up R γ := by
    rw [(nmPoly k R σ q hσ n δ).2 x, mul_assoc, hx', inv_mul_cancel_left]
  refine ⟨x, h1, ?_⟩
  have h2 := rep_shift σ q (sgConj σ x δ)
  rw [h1, rep_sg_up, hσ.pow, rep_sg_one] at h2
  exact h2

end UpperTheory.ConvolutionTheory.D
end
end

