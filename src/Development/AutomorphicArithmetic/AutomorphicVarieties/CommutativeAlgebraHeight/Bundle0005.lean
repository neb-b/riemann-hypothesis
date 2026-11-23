module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DMatrix
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section SlopeTestRemainingChoices

variable {n : ℕ} {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  (F : ∀ (S : Type) [CommRing S] [Algebra k S], Matrix ι ι S →* S)
  (nat : ∀ (S T : Type) [CommRing S] [Algebra k S] [CommRing T] [Algebra k T] (f : S →ₐ[k] T) (M : Matrix ι ι S),
    F T (M.map f) = f (F S M))
  (hom : ∀ (S : Type) [CommRing S] [Algebra k S] (b : S) (M : Matrix ι ι S), F S (b • M) = b ^ n * F S M)

include nat in
private theorem dm_transv (S : Type) [CommRing S] [Algebra k S] {i j : ι} (hij : i ≠ j) (s : S) :
    F S (Matrix.transvection i j s) = 1 := by
  have hm : ∀ (S : Type) [CommRing S] [Algebra k S] (s : S),
      F S (Matrix.transvection i j s) = aeval s (F k[X] (Matrix.transvection i j X)) := by
    intro S _ _ s
    rw [← nat]
    congr 1
    ext a b
    simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, map_add (f := _)]
    split_ifs <;> simp
  have hu : IsUnit (F k[X] (Matrix.transvection i j X)) := by
    refine IsUnit.of_mul_eq_one (F k[X] (Matrix.transvection i j (-X))) ?_
    rw [← map_mul, Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero, map_one]
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 hu
  have h0 := hm k 0
  rw [Matrix.transvection_zero, map_one, ← hc] at h0
  rw [hm, ← hc]
  simp at h0
  simp [← h0]

private theorem dm_diag_prod (S : Type) [CommRing S] [Algebra k S] (d : ι → S) :
    F S (Matrix.diagonal d) = ∏ i, F S (Matrix.diagonal (Pi.mulSingle i (d i))) := by
  have := map_prod ((F S).comp (Matrix.diagonalRingHom ι S).toMonoidHom) (fun i => Pi.mulSingle i (d i)) Finset.univ
  rw [Finset.univ_prod_mulSingle] at this
  exact this

include nat in
private theorem dm_single (S : Type) [CommRing S] [Algebra k S] (i : ι) (s : S) :
    F S (Matrix.diagonal (Pi.mulSingle i s)) = aeval s (F k[X] (Matrix.diagonal (Pi.mulSingle i X))) := by
  rw [← nat]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.diagonal_apply, Pi.mulSingle_apply]
  split_ifs <;> simp

private theorem dm_swap (S : Type) [CommRing S] [Algebra k S] (i j : ι) (s : S) :
    F S (Matrix.diagonal (Pi.mulSingle i s)) = F S (Matrix.diagonal (Pi.mulSingle j s)) := by
  have h : Matrix.swap S i j * Matrix.diagonal (Pi.mulSingle i s) * Matrix.swap S i j =
      Matrix.diagonal (Pi.mulSingle j s) := by
    simp only [Matrix.swap, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Pi.mulSingle_apply, id, Equiv.symm_swap,
      EmbeddingLike.apply_eq_iff_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  rw [← h, map_mul, map_mul, mul_right_comm, ← map_mul, Matrix.swap_mul_self, map_one, one_mul]

include hom in
private theorem dm_X : ∏ i : ι, F k[X] (Matrix.diagonal (Pi.mulSingle i X)) = X ^ n := by
  have := hom k[X] X 1
  rw [map_one, mul_one, Matrix.smul_one_eq_diagonal, dm_diag_prod] at this
  exact this

include nat hom in
private theorem dm_diag [Nonempty ι] : ∃ m, n = m * Fintype.card ι ∧
    ∀ (S : Type) [CommRing S] [Algebra k S] (d : ι → S), F S (Matrix.diagonal d) = (Matrix.diagonal d).det ^ m := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h := dm_X F hom
  have hd : F k[X] (Matrix.diagonal (Pi.mulSingle i₀ X)) ∣ X ^ n := h ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i₀)
  obtain ⟨m, -, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X n).1 hd
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have h1 := dm_single F nat k i₀ 1
  rw [Pi.mulSingle_one, show (1 : ι → k) = fun _ => 1 from rfl, Matrix.diagonal_one, map_one] at h1
  have h2 := congrArg (aeval (1 : k)) hu
  rw [map_mul, ← h1, ← hc] at h2
  have hc1 : c = 1 := by simpa using h2
  rw [← hc, hc1, map_one, mul_one] at hu
  have hall : ∀ i : ι, F k[X] (Matrix.diagonal (Pi.mulSingle i X)) = X ^ m := fun i => (dm_swap F _ i i₀ _).trans hu
  refine ⟨m, ?_, fun S _ _ d => ?_⟩
  · simp only [hall, Finset.prod_const, Finset.card_univ, ← pow_mul] at h
    have := congrArg natDegree h
    simpa using this.symm
  · rw [dm_diag_prod, Matrix.det_diagonal, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dm_single F nat, hall]
    simp

include nat hom in
private theorem dm_main [Nonempty ι] : ∃ m, n = m * Fintype.card ι ∧
    ∀ (S : Type) [CommRing S] [Algebra k S] (M : Matrix ι ι S), F S M = M.det ^ m := by
  obtain ⟨m, hm, hd⟩ := dm_diag F nat hom
  refine ⟨m, hm, fun S _ _ M => ?_⟩
  have hK : ∀ (K : Type) [Field K] [Algebra k K] (M : Matrix ι ι K), F K M = M.det ^ m := by
    intro K _ _ M
    refine Matrix.diagonal_transvection_induction (fun M => F K M = M.det ^ m) M (fun d _ => hd K d)
      (fun t => ?_) (fun A B hA hB => ?_)
    · rw [t.det, one_pow]
      exact dm_transv F nat K t.hij t.c
    · rw [map_mul, hA, hB, Matrix.det_mul, mul_pow]
  let R := MvPolynomial (ι × ι) k
  let G : Matrix ι ι R := Matrix.of fun i j => MvPolynomial.X (i, j)
  have hG : F R G = G.det ^ m := by
    apply IsFractionRing.injective R (FractionRing R)
    have := nat R (FractionRing R) (IsScalarTower.toAlgHom k R (FractionRing R)) G
    rw [hK] at this
    rw [map_pow, RingHom.map_det]
    exact this.symm
  have h := nat R S (MvPolynomial.aeval fun p => M p.1 p.2) G
  rw [hG, map_pow, AlgHom.map_det] at h
  have hM : G.map (MvPolynomial.aeval fun p : ι × ι => M p.1 p.2 : R →ₐ[k] S) = M := by
    ext a b
    simp [G, R]
  rw [AlgHom.mapMatrix_apply, hM] at h
  exact h

private theorem dm_rep (S : Type) [CommRing S] [Algebra k S] (y : S ⊗[k] Matrix ι ι k) :
    matrixEquivTensor ι k S (Det.repS (AlgHom.id k _) S y) = y := by
  rw [← AlgEquiv.eq_symm_apply]
  induction y with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s x =>
    rw [Det.repS_tmul, matrixEquivTensor_apply_symm]
    ext a b
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.CA.d_matrix :
    ∀ {n d : ℕ} {k : Type} [Field k] (D : Det n k (Matrix (Fin (d + 1)) (Fin (d + 1)) k)), ∃ m, n = m * (d + 1) ∧ ∀ (S : Type) [CommRing S] [Algebra k S] (y : S ⊗[k] Matrix (Fin (d + 1)) (Fin (d + 1)) k), D.D S y = (Det.repS (AlgHom.id k _) S y).det ^ m := by
  intro n d k _ D
  obtain ⟨m, hm, h⟩ := dm_main (n := n) (k := k) (ι := Fin (d + 1))
    (fun S _ _ => (D.D S).comp (matrixEquivTensor (Fin (d + 1)) k S).toAlgHom.toMonoidHom)
    (fun S T _ _ _ _ f M => by
      change D.D T (matrixEquivTensor _ k T (M.map f)) = f (D.D S (matrixEquivTensor _ k S M))
      rw [← D.nat]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp [matrixEquivTensor_apply, map_sum])
    (fun S _ _ b M => by
      change D.D S (matrixEquivTensor _ k S (b • M)) = b ^ n * D.D S (matrixEquivTensor _ k S M)
      rw [← D.homog]
      congr 1
      simp [matrixEquivTensor_apply, Finset.smul_sum, smul_tmul'])
  refine ⟨m, by simpa using hm, fun S _ _ y => ?_⟩
  rw [← h]
  exact congrArg (D.D S) (dm_rep S y).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem chiS_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    (Det.ofRep h r).chiS S y = (Det.repS r S y).charpoly := by
  have h1 : Det.repS r (Polynomial S)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y) =
      (Det.repS r S y).map Polynomial.C := by
    induction y with
    | tmul s z =>
      ext1 a b
      simp [Det.repS_tmul, Polynomial.single_eq_monomial]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (map_add _)]
  change (Det.repS r (Polynomial S) _).det = _
  rw [map_sub, h1, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  ext1 a b
  by_cases hab : a = b <;>
    simp [hab, Matrix.one_apply, Matrix.diagonal_apply, Polynomial.single_eq_monomial]

private theorem chi_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E) :
    (Det.ofRep h r).chi x = (r x).charpoly := by
  change (Det.repS r (Polynomial A) _).det = _
  rw [map_sub, Det.repS_tmul, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp

private theorem coeff_repS {σ A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (r : E →ₐ[A] Matrix ι ι A) (α : σ →₀ ℕ) (z : MvPolynomial σ A ⊗[A] E) :
    r (TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E z)) =
      (Det.repS r (MvPolynomial σ A) z).map (AddMonoidAlgebra.coeff · α) := by
  induction z with
  | tmul s z =>
    ext a b
    simp only [Det.repS_tmul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MvPolynomial.algebraMap_eq]
    rw [mul_comm s, MvPolynomial.coeff_C_mul]
    simp [mul_comm]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (MvPolynomial.coeff_add α)]

theorem UpperTheory.V.CA.d_ofRep :
    ∀ {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E), (Det.ofRep h r).chi x = (r x).charpoly ∧ (Det.ofRep h r).val x = (r x).det ∧ (1 ≤ n → (Det.ofRep h r).tr x = (r x).trace) ∧ (x ∈ (Det.ofRep h r).CH → r x = 0) := by
  intro n A E ι _ _ _ _ _ h r x
  refine ⟨chi_ofRep h r x, ?_, fun hn => ?_, fun hx => ?_⟩
  · change (Det.repS r A (1 ⊗ₜ x)).det = _
    rw [Det.repS_tmul]
    simp
  · haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    rw [Det.tr, Det.lam, chi_ofRep, Matrix.trace_eq_neg_charpoly_coeff, h]
    simp
  · have hle : (Det.ofRep h r).CH ≤ TwoSidedIdeal.ker r := by
      rw [Det.CH, TwoSidedIdeal.span_le]
      rintro z ⟨k, y, α, rfl⟩
      change _ ∈ TwoSidedIdeal.ker r
      rw [TwoSidedIdeal.mem_ker, Det.chElt, coeff_repS, chiS_ofRep, ← Polynomial.aeval_algHom_apply,
        Matrix.aeval_self_charpoly]
      ext a b
      simp
    exact (TwoSidedIdeal.mem_ker r).1 (hle hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPolyExt
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_poly_ext :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (D' : Det n A E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (x : Fin k → E), (∀ a, x a ∈ M) → D.poly x = D'.poly x) → D = D' := by
  intro n A E _ _ _ D D' M hM h
  refine Det.ext' fun S _ _ y => ?_
  have h1 : ∀ x : E, (1 : S) ⊗ₜ[A] x ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' M) := by
    intro x
    have hx : x ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a z _ hz => rw [tmul_smul]; exact Submodule.smul_of_tower_mem _ a hz
  have h2 : y ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' M) := by
    induction y with
    | add a b ha hb => exact add_mem ha hb
    | tmul s x =>
      have : s ⊗ₜ[A] x = s • ((1 : S) ⊗ₜ[A] x) := by simp [smul_tmul']
      rw [this]; exact Submodule.smul_mem _ s (h1 x)
  obtain ⟨k, s, g, rfl⟩ := Submodule.mem_span_set'.1 h2
  choose x hxM hx using fun a => (g a).2
  have h3 : ∑ a, s a • (g a : S ⊗[A] E) =
      Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Det.gen, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X, AlgHom.id_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hx a]; simp [smul_tmul']
  rw [h3, D.nat, D'.nat]
  exact congrArg _ (h k x hxM)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E']
  [Algebra A E'] (f : E' →ₐ[A] E)

private theorem pull_D (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E') :
    (D.pull f).D S y = D.D S (Algebra.TensorProduct.map (AlgHom.id S S) f y) := rfl

private theorem map_gen {ι : Type} [Fintype ι] (x : ι → E') :
    Algebra.TensorProduct.map (AlgHom.id (MvPolynomial ι A) (MvPolynomial ι A)) f (Det.gen (A := A) x) =
      Det.gen (A := A) (fun a => f (x a)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Det.gen, map_sum]

private theorem pull_chiS (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E') :
    (D.pull f).chiS S y = D.chiS S (Algebra.TensorProduct.map (AlgHom.id S S) f y) := by
  unfold Det.chiS
  rw [pull_D]
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem map_coeff {ι : Type} (α : ι →₀ ℕ) (y : MvPolynomial ι A ⊗[A] E') :
    f (TensorProduct.lid A E' ((MvPolynomial.lcoeff A α).rTensor E' y)) =
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E
        (Algebra.TensorProduct.map (AlgHom.id (MvPolynomial ι A) (MvPolynomial ι A)) f y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem map_chElt {k : ℕ} (x : Fin k → E') (α : Fin k →₀ ℕ) :
    f ((D.pull f).chElt x α) = D.chElt (fun a => f (x a)) α := by
  unfold Det.chElt
  rw [map_coeff, pull_chiS, ← Polynomial.aeval_algHom_apply, map_gen]

private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) :=
  by apply _root_.UpperTheory.Reformulated.B.Qk2.map_surj <;> assumption

end

theorem UpperTheory.V.CA.d_pull :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E' →ₐ[A] E), (∀ x, (D.pull f).chi x = D.chi (f x)) ∧ (∀ x, f x ∈ D.ker → x ∈ (D.pull f).ker) ∧ (∀ x ∈ (D.pull f).CH, f x ∈ D.CH) ∧ (Function.Surjective f → (∀ x, x ∈ (D.pull f).ker → f x ∈ D.ker) ∧ ∀ y ∈ D.CH, ∃ x ∈ (D.pull f).CH, f x = y) := by
  intro n A E _ _ _ D E' _ _ f
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun hf => ⟨fun x hx => ?_, fun y hy => ?_⟩⟩
  · unfold Det.chi
    rw [pull_D]
    simp
  · rw [Det.mem_ker] at hx ⊢
    intro S _ _ y u v
    rw [pull_D, pull_D, map_add (f := _), map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one]
    exact hx S _ _ _
  · unfold Det.CH at hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x h =>
      obtain ⟨k, z, α, rfl⟩ := h
      exact TwoSidedIdeal.subset_span ⟨k, _, α, map_chElt D f z α⟩
    | zero => rw [map_zero]; exact D.CH.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact D.CH.add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact D.CH.neg_mem hx
    | left_absorb a x _ hx => rw [map_mul]; exact D.CH.mul_mem_left _ _ hx
    | right_absorb b x _ hx => rw [map_mul]; exact D.CH.mul_mem_right _ _ hx
  · rw [Det.mem_ker] at hx ⊢
    intro S _ _ y u v
    obtain ⟨y, rfl⟩ := map_surj f hf S y
    obtain ⟨u, rfl⟩ := map_surj f hf S u
    obtain ⟨v, rfl⟩ := map_surj f hf S v
    have := hx S y u v
    rwa [pull_D, pull_D, map_add, map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one] at this
  · unfold Det.CH at hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y h =>
      obtain ⟨k, z, α, rfl⟩ := h
      choose w hw using fun a => hf (z a)
      refine ⟨(D.pull f).chElt w α, TwoSidedIdeal.subset_span ⟨k, w, α, rfl⟩, ?_⟩
      rw [map_chElt]
      simp only [hw]
    | zero => exact ⟨0, (D.pull f).CH.zero_mem, map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', (D.pull f).CH.add_mem hx' hy', map_add f _ _⟩
    | neg x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨-x', (D.pull f).CH.neg_mem hx', map_neg f _⟩
    | left_absorb a x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hf a
      exact ⟨a * x', (D.pull f).CH.mul_mem_left _ _ hx', map_mul f _ _⟩
    | right_absorb a x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hf a
      exact ⟨x' * a, (D.pull f).CH.mul_mem_right _ _ hx', map_mul f _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G), D.toDet.chi y = D.chi y ∧ (∀ i, D.toDet.lam i y = D.lam i y) ∧ D.toDet.tr y = D.tr y ∧ (D.toDet.Kills y ↔ D.Kills y) := by
  intro n A G _ _ D y
  have hchi : D.toDet.chi y = D.chi y := by
    change D.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
    rfl
  have hlam : ∀ i, D.toDet.lam i y = D.lam i y := fun i => by
    unfold Det.lam GDet.lam
    rw [hchi]
  refine ⟨hchi, hlam, hlam 1, ?_⟩
  have key : ∀ (B : Type) [CommRing B] [Algebra A B] (h : B ⊗[A] MonoidAlgebra A G),
      D.toDet.D B (1 + h * (1 ⊗ₜ y)) =
        D.D B (1 + ofT A G B h * MonoidAlgebra.mapRingHom G (algebraMap A B) y) := by
    intro B _ _ h
    change D.D B (ofT A G B (1 + h * (1 ⊗ₜ y))) = _
    rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
  constructor
  · intro hk B _ _ h
    have := hk B (toT A G B h)
    rwa [key, ofT_toT] at this
  · intro hk B _ _ h
    rw [key]
    exact hk B _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem D_congr {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext i j h
  subst this; rfl

private theorem ofT_gen {A G : Type} [CommRing A] [Group G] {m : ℕ} (y : Fin m → MonoidAlgebra A G) :
    ofT A G (MvPolynomial (Fin m) A) (Det.gen (A := A) y) = GDet.gen y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Det.gen, GDet.gen, map_sum, ofT_tmul]
  rfl

private theorem ofT_map {A G : Type} [CommRing A] [Group G] (S : Type) [CommRing S] [Algebra A S]
    (x : S ⊗[A] MonoidAlgebra A G) :
    ofT A G S[X] (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A _) x) =
      MonoidAlgebra.mapRingHom G (C : S →+* S[X]) (ofT A G S x) := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s y => ext1; ext1 g; simp [ofT_tmul]

private theorem chiS_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (x : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) :
    D.toDet.chiS (MvPolynomial (Fin m) A) x =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (ofT A G _ x) := by
  have h : ofT A G (MvPolynomial (Fin m) A)[X] (X ⊗ₜ 1 -
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X])
        (AlgHom.id A _) x) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (ofT A G _ x) := by
    rw [map_sub, ofT_map, ofT_tmul, map_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  refine (congrArg (D.D (MvPolynomial (Fin m) A)[X]) h).trans ?_
  exact D_congr D (MvPolynomial (Fin m) A)[X] inferInstance
    ((algebraMap (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X]).comp MvPolynomial.C).toAlgebra (fun a => rfl) _

private theorem coeff_lid {A G : Type} [CommRing A] [Group G] {m : ℕ} (β : Fin m →₀ ℕ)
    (w : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) (g : G) :
    (TensorProduct.lid A (MonoidAlgebra A G) ((MvPolynomial.lcoeff A β).rTensor _ w)).coeff g =
      AddMonoidAlgebra.coeff ((ofT A G _ w).coeff g) β := by
  induction w with
  | add a b ha hb => simp only [map_add (f := _), MonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_add, ha, hb]
  | tmul s y => simp [ofT_tmul, mul_comm s, MvPolynomial.coeff_C_mul, mul_comm (y.coeff g)]

private theorem chElt_coeff {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) (g : G) :
    (D.toDet.chElt y β).coeff g = AddMonoidAlgebra.coeff ((Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))).coeff g)
      β := by
  rw [Det.chElt, coeff_lid, chiS_eq, ← Polynomial.aeval_algHom_apply, ofT_gen]

theorem UpperTheory.V.CA.d_toDet_CH :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.toDet.CH = TwoSidedIdeal.span D.CH := by
  intro n A G _ _ D
  rw [Det.CH]
  congr 1
  ext1 z
  constructor
  · rintro ⟨m, y, β, rfl⟩
    exact ⟨m, y, β, chElt_coeff D y β⟩
  · rintro ⟨m, y, β, h⟩
    refine ⟨m, y, β, ?_⟩
    ext g
    rw [h, chElt_coeff]
end

