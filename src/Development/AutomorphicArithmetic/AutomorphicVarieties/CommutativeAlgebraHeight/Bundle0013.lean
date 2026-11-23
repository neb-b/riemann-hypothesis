module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FgChi
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem fg_ev {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E) (r : ℕ)
    (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r) (b : A[X]) : D.D A[X] (1 + (b - 1) ⊗ₜ e) = b ^ r := by
  have h2 := D.nat A[X] A[X] (aeval (b - 1)) (1 + X ⊗ₜ e)
  rw [h] at h2
  simpa using h2

private theorem fg_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (he : IsIdempotentElem e) (r s : ℕ) (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r)
    (h' : D.D A[X] (1 + X ⊗ₜ (1 - e)) = (1 + X) ^ s) : D.chi e = X ^ s * (X - 1) ^ r := by
  rw [← fg_ev D e r h, ← fg_ev D (1 - e) s h', ← map_mul, Det.chi]
  congr 1
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, he.one_sub_mul_self, tmul_zero]
  simp only [one_mul, mul_one, tmul_sub, sub_tmul, ← Algebra.TensorProduct.one_def]
  abel

private theorem fg_one {k : Type} [Field k] {r s m : ℕ} (h : (X : k[X]) ^ s * (X - 1) ^ r = (X - 1) * X ^ m) :
    r = 1 := by
  rcases r with _ | _ | r
  · simpa using congrArg (eval 1) h
  · rfl
  · have h0 : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
    rw [pow_succ' _ (r + 1), mul_left_comm] at h
    simpa using congrArg (eval 1) (mul_left_cancel₀ h0 h)

theorem UpperTheory.V.CA.f_gma :
    ∀ {n : ℕ} {B E k : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Ring E] [Algebra B E] [Field k] [Algebra B k] [IsLocalHom (algebraMap B k)] (D : Det n B E) (π : E →ₐ[B] (Fin n → k)), D.IsCH → Function.Surjective π → (∀ x, (D.chi x).map (algebraMap B k) = ∏ i, (X - C (π x i))) → (∀ x, π x = 0 ↔ x ∈ Ring.jacobson E) ∧ ∃ e : Fin n → E, IsGMA D e ∧ ∀ i, π (e i) = Pi.single i 1 := by
  intro n B E k _ _ _ _ _ _ _ _ _ D π hD hs hchi
  obtain ⟨hu, hint⟩ := d_unit D hD
  have hunit : ∀ x, π x = 1 → IsUnit x := by
    intro x hx
    rw [hu, ← (d_chi D x).2.2.2.1, Det.lam, Nat.sub_self]
    refine (isUnit_one.neg.pow n).mul ?_
    refine (isUnit_map_iff (algebraMap B k) _).1 ?_
    rw [← coeff_map, hchi, hx, coeff_zero_eq_eval_zero, isUnit_iff_ne_zero]
    simp [eval_prod]
  have hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E := by
    intro x hx
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro y
    obtain ⟨u, hu'⟩ := hunit (y * x + 1) (by simp [hx])
    refine ⟨↑u⁻¹, ?_⟩
    rw [Ideal.mem_bot, sub_eq_zero, ← u.inv_mul, hu', mul_add, mul_one, mul_assoc]
  refine ⟨fun x => ⟨hk x, fun hx => ?_⟩, ?_⟩
  · rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff] at hx
    funext i
    by_contra hi
    obtain ⟨y, hy⟩ := hs fun _ => -(π x i)⁻¹
    obtain ⟨z, hz⟩ := hx y
    rw [Ideal.mem_bot] at hz
    have h1 := congrFun (congrArg π hz) i
    have hi' : π x i ≠ 0 := hi
    simp only [map_sub, map_add (f := _), map_mul, map_one, map_zero, hy, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      Pi.one_apply, Pi.zero_apply] at h1
    rw [mul_assoc, neg_mul, inv_mul_cancel₀ hi'] at h1
    simp at h1
  · obtain ⟨e, he, he'⟩ := d_lift_idem π hs hk (fun i => Pi.single i 1)
      (CompleteOrthogonalIdempotents.single fun _ : Fin n => k)
    refine ⟨e, ⟨hD, he, fun i => ?_⟩, he'⟩
    obtain ⟨r, -, hr⟩ := d_idem_rank D (e i) (he.idem i)
    obtain ⟨s, -, hs'⟩ := d_idem_rank D (1 - e i) (he.idem i).one_sub
    have h1 := hchi (e i)
    rw [fg_chi D _ (he.idem i) r s hr hs', he', ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Finset.prod_congr rfl (g := fun _ => X) (fun j hj => by
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]), Finset.prod_const] at h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one,
      Pi.single_eq_same, map_one] at h1
    rw [hr, fg_one h1, pow_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.LeftInvOfJac
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem left_inv_of_jac {A E K : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing K] [Algebra A K]
    [Module.Finite A K] {m : ℕ} (s : Fin m → K) (z : Fin m → E) (hz : ∀ i, z i ∈ Ring.jacobson E) :
    ∃ v : K ⊗[A] E, v * (1 + ∑ i, s i ⊗ₜ z i) = 1 := by
  let w : E ⊗[A] K := ∑ i, z i ⊗ₜ s i
  have hw : ∀ y : E ⊗[A] K, y * w ∈ Module.jacobson E (E ⊗[A] K) := by
    intro y
    induction y with
    | add a b ha hb => rw [add_mul]; exact add_mem ha hb
    | tmul e a =>
      rw [Finset.mul_sum]
      refine Submodule.sum_mem _ fun i _ => Ring.jacobson_smul_top_le E _ ?_
      have : (e ⊗ₜ[A] a) * (z i ⊗ₜ[A] s i) = (e * z i) • ((1 : E) ⊗ₜ[A] (a * s i)) := by
        simp [smul_tmul']
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (hz i)) Submodule.mem_top
  let f : E ⊗[A] K →ₗ[E] E ⊗[A] K :=
    { toFun := fun y => y * (1 + w)
      map_add' := fun a b => add_mul _ _ _
      map_smul' := fun e y => smul_mul_assoc e y _ }
  have htop : LinearMap.range f = ⊤ := by
    rcases eq_top_or_exists_le_coatom (LinearMap.range f) with h | ⟨N, hN, hle⟩
    · exact h
    · exfalso
      refine hN.1 (eq_top_iff.2 fun y _ => ?_)
      have h1 : y * (1 + w) ∈ N := hle ⟨y, rfl⟩
      have h2 : y * w ∈ N := (sInf_le hN : Module.jacobson E (E ⊗[A] K) ≤ N) (hw y)
      have := N.sub_mem h1 h2
      rwa [mul_add, mul_one, add_sub_cancel_right] at this
  obtain ⟨v, hv⟩ : (1 : E ⊗[A] K) ∈ LinearMap.range f := htop ▸ Submodule.mem_top
  refine ⟨Algebra.TensorProduct.comm A E K v, ?_⟩
  have hv' : v * (1 + w) = 1 := hv
  have h := congrArg (Algebra.TensorProduct.comm A E K) hv'
  rw [map_mul, map_one] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [w, map_sum] using h

private theorem kills_of_jac {n : ℕ} {k R : Type} [Field k] [Ring R] [Algebra k R] (D : Det n k R) (x : R)
    (hx : x ∈ Ring.jacobson R) : D.Kills x := by
  refine UpperTheory.V.CA.d_kills_poly D x Set.univ (by simp) fun m h _ => ?_
  set P := D.D (MvPolynomial (Fin m) k) (1 + Det.gen h * (1 ⊗ₜ x)) with hP
  have key : ∀ (K : Type) [CommRing K] [Algebra k K] (φ : MvPolynomial (Fin m) k →ₐ[k] K),
      φ P = D.D K (1 + ∑ i, φ (MvPolynomial.X i) ⊗ₜ (h i * x)) := by
    intro K _ _ φ
    rw [hP, ← D.nat]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum, Finset.sum_mul]
  have hu : IsUnit P := by
    by_contra hnu
    obtain ⟨M, hM, hPM⟩ := exists_max_ideal_of_mem_nonunits hnu
    letI := Ideal.Quotient.field M
    haveI : Module.Finite k (MvPolynomial (Fin m) k ⧸ M) := finite_of_finite_type_of_isJacobsonRing _ _
    obtain ⟨v, hv⟩ := left_inv_of_jac (A := k) (fun i => Ideal.Quotient.mkₐ k M (MvPolynomial.X i))
      (fun i => h i * x) (fun i => Ideal.mul_mem_left _ _ hx)
    have h1 := congrArg (D.D _) hv
    rw [map_mul, map_one, ← key, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hPM, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨c, -, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
  have h0 := key k (MvPolynomial.aeval fun _ => 0)
  rw [hc] at h0 ⊢
  simp at h0
  simp [h0]

theorem UpperTheory.V.CA.d_rad :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] (D : Det n A E), D.IsCH → ∀ x : E, (1 : ResidueField A) ⊗ₜ[A] x ∈ (D.baseChange (ResidueField A)).ker ↔ x ∈ Ring.jacobson E := by
  intro n A E _ _ _ _ D hCH x
  rw [(UpperTheory.V.CA.d_ker _ _).1]
  constructor
  · intro hx
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro y
    have h0 := hx (ResidueField A) (1 ⊗ₜ (1 ⊗ₜ y))
    rw [(UpperTheory.V.CA.d_bc D (ResidueField A)).1] at h0
    have h1 : algebraMap A (ResidueField A) (D.val (y * x + 1)) = 1 := by
      have := D.nat A (ResidueField A) (Algebra.ofId A _) (1 ⊗ₜ (y * x + 1))
      refine this.symm.trans (Eq.trans (congrArg _ ?_) h0)
      simp [Det.cancel_tmul, tmul_add, add_comm, Algebra.TensorProduct.one_def]
    have h2 : IsUnit (y * x + 1) :=
      ((UpperTheory.V.CA.d_unit D hCH).1 _).2
        ((residue_ne_zero_iff_isUnit _).1 fun h0 => one_ne_zero (h1.symm.trans h0))
    obtain ⟨u, hu⟩ := h2
    refine ⟨(↑u⁻¹ : E), ?_⟩
    have h3 : (↑u⁻¹ : E) * (y * x + 1) = 1 := by rw [← hu, Units.inv_mul]
    rw [Ideal.mem_bot, sub_eq_zero, ← h3, mul_add, mul_one, mul_assoc]
  · intro hx
    refine kills_of_jac _ _ ?_
    let f : E →+* ResidueField A ⊗[A] E :=
      (Algebra.TensorProduct.includeRight : E →ₐ[A] ResidueField A ⊗[A] E).toRingHom
    haveI : RingHomSurjective f := ⟨fun t => by
      induction t with
      | add a b ha hb =>
        obtain ⟨a, rfl⟩ := ha
        obtain ⟨b, rfl⟩ := hb
        exact ⟨a + b, map_add _ _ _⟩
      | tmul c e =>
        obtain ⟨a, rfl⟩ := residue_surjective c
        refine ⟨a • e, ?_⟩
        change (1 : ResidueField A) ⊗ₜ[A] (a • e) = _
        rw [← smul_tmul, ← Algebra.algebraMap_eq_smul_one]
        rfl⟩
    exact Ring.le_comap_jacobson f hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.LiftEq
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lift_eq {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) C) (z : MonoidAlgebra B G) :
    MonoidAlgebra.lift B _ G ρ z = GDet.repAlg ρ C (MonoidAlgebra.mapRingHom G (algebraMap B C) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => ext i j; simp [GDet.repAlg, Algebra.smul_def]

private theorem lift_CH {n : ℕ} {B C G : Type} [CommRing B] [CommRing C] [Algebra B C] [Group G]
    (D : GDet n B G) (ρ : G →* Matrix (Fin n) (Fin n) C) (h : D.map (algebraMap B C) = GDet.ofRep ρ)
    (z : MonoidAlgebra B G) (hz : z ∈ D.CH) : MonoidAlgebra.lift B _ G ρ z = 0 := by
  rw [lift_eq]
  refine (d_ofRep (Fintype.card_fin n) (GDet.repAlg ρ C) _).2.2.2 ?_
  rw [← d_toDet_ofRep.1 ρ, d_toDet_CH, ← h, g_chmap]
  exact TwoSidedIdeal.subset_span ⟨z, hz, rfl⟩

theorem UpperTheory.V.CA.f_rep :
    ∀ {n : ℕ} {B C G : Type} [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (J : Ideal C) [IsHausdorff J C] (D : GDet n B G) (ρ : G →* Matrix (Fin n) (Fin n) C) (Z : Set (MonoidAlgebra B G)), maximalIdeal B ≤ J.comap (algebraMap B C) → (∀ a b, AdicCont J fun g => ρ g a b) → D.map (algebraMap B C) = GDet.ofRep ρ → (∀ z ∈ Z, MonoidAlgebra.lift B _ G ρ z = 0) → ∃ r : D.CHQuot Z →ₐ[B] Matrix (Fin n) (Fin n) C, ∀ g, r (D.toQuot Z (MonoidAlgebra.single g 1)) = ρ g := by
  intro n B C G _ _ _ _ _ _ _ _ _ J _ D ρ Z hm hc hD hZ
  have key : ∀ z ∈ D.chBar Z, MonoidAlgebra.lift B _ G ρ z = 0 := by
    intro z hz
    ext a b
    refine IsHausdorff.haus (I := J) inferInstance _ fun N => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hU : IsOpen (⋂ a, ⋂ b, {g : G | Ideal.Quotient.mk (J ^ N) (ρ g a b) = Ideal.Quotient.mk (J ^ N) (ρ 1 a b)}) :=
      isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => (hc a b N).isOpen_fiber _
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU (by simp)
    let φ : MonoidAlgebra B G →+* Matrix (Fin n) (Fin n) (C ⧸ J ^ N) :=
      (Ideal.Quotient.mk (J ^ N)).mapMatrix.comp (MonoidAlgebra.lift B _ G ρ).toRingHom
    have hφ : ∀ y, φ y = (MonoidAlgebra.lift B _ G ρ y).map (Ideal.Quotient.mk (J ^ N)) := fun _ => rfl
    have hle : D.chBar Z ≤ TwoSidedIdeal.ker φ := by
      refine (iInf₂_le N H).trans ?_
      rw [TwoSidedIdeal.span_le]
      intro y hy
      change _ ∈ TwoSidedIdeal.ker φ
      rw [TwoSidedIdeal.mem_ker]
      rcases hy with ((hy | hy) | ⟨x, hx, rfl⟩) | ⟨h, hh, rfl⟩
      · rw [hφ, lift_CH D ρ hD y hy]; simp
      · rw [hφ, hZ y hy]; simp
      · have hx' : algebraMap B C x ∈ J ^ N :=
          Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hm) N
            (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx)
        ext i j
        rw [hφ, MonoidAlgebra.lift_single, Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, Matrix.zero_apply,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ hx'
      · rw [map_sub, map_one, sub_eq_zero, ← φ.map_one]
        ext i j
        have := Set.mem_iInter.1 (Set.mem_iInter.1 (hH hh) i) j
        rw [hφ, hφ, map_one, MonoidAlgebra.lift_single, one_smul, ← ρ.map_one]
        exact this
    have := congrFun (congrFun ((TwoSidedIdeal.mem_ker φ).1 (hle hz)) a) b
    rw [hφ] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  refine ⟨RingCon.liftₐ _ (MonoidAlgebra.lift B _ G ρ) fun x y hxy => ?_, fun g => ?_⟩
  · have := key _ ((TwoSidedIdeal.rel_iff _ _ _).1 hxy)
    rwa [map_sub, sub_eq_zero] at this
  · change MonoidAlgebra.lift B _ G ρ _ = _
    simp
end

