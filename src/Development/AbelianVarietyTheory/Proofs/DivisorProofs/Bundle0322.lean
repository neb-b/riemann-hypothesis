module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepth
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatOfHankelEventuallyZero
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.Kron

open Polynomial

variable {F : Type} [Field F] (c : ℕ → F)

def ev : F[X] →ₗ[F] F := Polynomial.lsum fun i => c i • LinearMap.id

theorem ev_monomial (n : ℕ) (a : F) : ev c (monomial n a) = c n * a := by
  simp [ev, Polynomial.lsum_apply]

theorem ev_expand (q p : F[X]) (n : ℕ) (hp : p.natDegree < n) :
    ev c (q * p) = ∑ j ∈ Finset.range n, p.coeff j * ev c (q * X ^ j) := by
  conv_lhs => rw [p.as_sum_range' n hp]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial, show q * (C (p.coeff j) * X ^ j) = p.coeff j • (q * X ^ j) by
    rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]

theorem ev_zero_of_lt (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree < s) : ev c (q * p) = 0 := by
  rw [ev_expand c q p s hp]
  exact Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero]

theorem ev_top (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree ≤ s) : ev c (q * p) = p.coeff s * ev c (q * X ^ s) := by
  rw [ev_expand c q p (s + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ,
    Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero], zero_add]

theorem ev_X_pow_mul (m : ℕ) (q : F[X]) :
    ev c (q * X ^ m) = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * c (m + j) := by
  rw [mul_comm, ev_expand c _ q _ (Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_add, ← monomial_one_right_eq_X_pow, ev_monomial, mul_one]

theorem exists_kill (n : ℕ) (h : hankel c n = 0) :
    ∃ r : F[X], r ≠ 0 ∧ r.natDegree ≤ n ∧ ∀ j ≤ n, ev c (r * X ^ j) = 0 := by
  classical
  unfold hankel at h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine ⟨∑ k : Fin (n + 1), monomial (k : ℕ) (v k), ?_, ?_, ?_⟩
  · intro h0
    apply hv0
    funext k
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h0
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finsupp.single_apply, Fin.val_inj] using this
  · exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 k.2)
  · intro j hj
    have := congrFun hv ⟨j, Nat.lt_succ_of_le hj⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [monomial_mul_X_pow, ev_monomial, add_comm]

theorem exists_annihilator (N : ℕ) (hN : ∀ n, N ≤ n → hankel c n = 0) :
    ∃ q : F[X], q ≠ 0 ∧ ∀ j, ev c (q * X ^ j) = 0 := by
  classical
  have hex : ∃ d, ∃ q : F[X], q ≠ 0 ∧ q.natDegree = d ∧ d ≤ N ∧ ∀ j ≤ N, ev c (q * X ^ j) = 0 := by
    obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c N (hN N le_rfl)
    exact ⟨_, r, hr0, rfl, hrd, hr⟩
  obtain ⟨q0, hq00, hq0d, hdN, hq0⟩ := Nat.find_spec hex
  have hmin : ∀ r : F[X], r ≠ 0 → r.natDegree < Nat.find hex → ¬ ∀ j ≤ N, ev c (r * X ^ j) = 0 :=
    fun r hr0 hrd hr => Nat.find_min hex hrd ⟨r, hr0, rfl, by omega, hr⟩
  have hlc : (q0.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.2 hq00)
  obtain ⟨q, hqm, hqd, hqe⟩ : ∃ q : F[X], q.Monic ∧ q.natDegree = Nat.find hex ∧
      ∀ j, ev c (q * X ^ j) = (q0.leadingCoeff)⁻¹ * ev c (q0 * X ^ j) := by
    refine ⟨q0 * C (q0.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq00, ?_, fun j => ?_⟩
    · rw [natDegree_mul_C hlc, hq0d]
    · rw [show q0 * C (q0.leadingCoeff)⁻¹ * X ^ j = (q0.leadingCoeff)⁻¹ • (q0 * X ^ j) by
        rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]
  refine ⟨q, hqm.ne_zero, ?_⟩
  by_contra hne
  push_neg at hne
  have hs : ev c (q * X ^ Nat.find hne) ≠ 0 := Nat.find_spec hne
  have hlt : ∀ j < Nat.find hne, ev c (q * X ^ j) = 0 := fun j hj => by
    by_contra h; exact Nat.find_min hne hj h
  generalize Nat.find hne = s at hs hlt
  generalize Nat.find hex = d at hmin hqd hdN
  have hNs : N < s := by
    by_contra h
    push_neg at h
    apply hs
    rw [hqe, hq0 s h, mul_zero]
  obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c s (hN s hNs.le)
  have hrk : ∀ p : F[X], p.natDegree ≤ s → ev c (r * p) = 0 := fun p hp => by
    rw [ev_top c r p s (fun j hj => hr j hj.le) hp, hr s le_rfl, mul_zero]
  obtain ⟨r0, r1, hdiv, hr0deg⟩ : ∃ r0 r1 : F[X], r0 + q * r1 = r ∧ r0.degree < q.degree :=
    ⟨_, _, modByMonic_add_div r q, degree_modByMonic_lt r hqm⟩
  subst hdiv
  have hr0s : r0.natDegree < s := by
    by_cases hz : r0 = 0
    · rw [hz, natDegree_zero]; omega
    · have := natDegree_lt_natDegree hz hr0deg; omega
  by_cases h1 : r1 = 0
  · subst h1
    rw [mul_zero, add_zero] at hr0 hrd hr
    apply hmin r0 hr0 (hqd ▸ natDegree_lt_natDegree hr0 hr0deg)
    intro j hj
    exact hr j (by omega)
  · have hdeg : d + r1.natDegree ≤ s := by
      rw [← hqd, ← natDegree_mul hqm.ne_zero h1]
      have : q * r1 = r0 + q * r1 - r0 := by ring
      rw [this]
      exact (natDegree_sub_le _ _).trans (max_le hrd hr0s.le)
    have key := hrk (q * X ^ (s - d - r1.natDegree))
      (by rw [natDegree_mul_X_pow _ hqm.ne_zero, hqd]; omega)
    rw [add_mul, map_add (f := _)] at key
    have h0 : ev c (r0 * (q * X ^ (s - d - r1.natDegree))) = 0 := by
      rw [show r0 * (q * X ^ (s - d - r1.natDegree)) = q * (r0 * X ^ (s - d - r1.natDegree)) by ring]
      apply ev_zero_of_lt c q _ s hlt
      by_cases hz : r0 = 0
      · rw [hz, zero_mul, natDegree_zero]; omega
      · rw [natDegree_mul_X_pow _ hz]
        have := natDegree_lt_natDegree hz hr0deg
        omega
    have hne1 : r1 * q ≠ 0 := mul_ne_zero h1 hqm.ne_zero
    have hs' : s = (r1 * q).natDegree + (s - d - r1.natDegree) := by
      rw [natDegree_mul h1 hqm.ne_zero, hqd]; omega
    have hcoef : (r1 * q * X ^ (s - d - r1.natDegree)).coeff s = r1.leadingCoeff := by
      have := coeff_mul_X_pow (r1 * q) (s - d - r1.natDegree) (r1 * q).natDegree
      rw [← hs'] at this
      rw [this, coeff_natDegree, leadingCoeff_mul, hqm.leadingCoeff, mul_one]
    have h2 : ev c (q * r1 * (q * X ^ (s - d - r1.natDegree))) = r1.leadingCoeff * ev c (q * X ^ s) := by
      rw [show q * r1 * (q * X ^ (s - d - r1.natDegree)) = q * (r1 * q * X ^ (s - d - r1.natDegree)) by ring,
        ev_top c q _ s hlt (by rw [natDegree_mul_X_pow _ hne1]; omega), hcoef]
    rw [h0, h2, zero_add] at key
    exact hs ((mul_eq_zero.1 key).resolve_left (leadingCoeff_ne_zero.2 h1))

theorem isRat_of_ann (φ : PowerSeries F) (q : F[X]) (hq : q ≠ 0)
    (h : ∀ j, ev (fun i => PowerSeries.coeff i φ) (q * X ^ j) = 0) : IsRat φ := by
  classical
  let R : F[X] := ∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k) * X ^ (q.natDegree - k)
  refine ⟨PowerSeries.trunc q.natDegree ((R : PowerSeries F) * φ), R, ?_, ?_⟩
  · intro h0
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h0
    simp only [R, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single q.natDegree] at this
    · simp only [Nat.sub_self, if_true] at this
      exact hq (leadingCoeff_eq_zero.1 this)
    · intro k hk hkd
      have := Finset.mem_range.1 hk
      rw [if_neg (by omega)]
    · intro hk; exact absurd (Finset.self_mem_range_succ _) hk
  · ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + q.natDegree := ⟨n - q.natDegree, by omega⟩
      have hR : (R : PowerSeries F) = ∑ k ∈ Finset.range (q.natDegree + 1),
          PowerSeries.C (q.coeff k) * PowerSeries.X ^ (q.natDegree - k) := by
        show Polynomial.coeToPowerSeries.ringHom R = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp [Polynomial.coeToPowerSeries.ringHom_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hR, Finset.sum_mul, map_sum, ← h m, ev_X_pow_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
      rw [show m + q.natDegree - (q.natDegree - k) = m + k by omega]

end GlobalTheory.Nef.Kron

namespace GlobalTheory.Nef

theorem isRat_of_hankel_eventually_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ),
    (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  intro F _ φ N hN
  obtain ⟨q, hq, h⟩ := Kron.exists_annihilator _ N hN
  exact Kron.isRat_of_ann φ q hq h

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorPullbackEqMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open GlobalTheory.HilbAff in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C))
      (U : Z.affineOpens),
      (letI := (GlobalTheory.HilbAff.secAlg A
        (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U ∧
         RingHom.ker (GlobalTheory.HilbAff.kappa A B
           (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))
           ((GlobalTheory.HilbAff.xI A B C J).comap
             (GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) =
         J.map (Algebra.TensorProduct.map φ (AlgHom.id A B))) := by
  intro A B C _ _ _ _ _ J Z h U
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let g := h ≫ f
  let W := pullback.snd (str A B) g ⁻¹ᵁ (U : Z.Opens)
  let := (secAlg A g U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        have hs : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ U (by simp) =
            CommRingCat.ofHom (algebraMap A C) ≫
              (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) := by
          calc
            _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
                h.appLE ⊤ U (by simp) :=
              congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h f ⊤ U (by simp))
            _ = _ := (Scheme.ΓSpecIso_inv_naturality_assoc
              (CommRingCat.ofHom (algebraMap A C)) (h.appLE ⊤ U (by simp))).symm
        exact (congrArg (fun F => F.hom a) hs).symm }
  refine ⟨φ, rfl, ?_⟩
  have : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have hTensor : ((bc A B f h).appLE ⊤ W (by simp)).hom.comp (psi A B C) =
      (theta A B g U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
    have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (pullback.snd (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have hpsi (c : C) (b : B) : psi A B C (c ⊗ₜ[A] b) =
        (pullback.fst (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
        (pullback.snd (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
      have h1 := congrArg (fun F => F.hom b) eL
      have h2 := congrArg (fun F => F.hom c) eR
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      rw [h1, h2, ← map_mul, ← map_mul]
      simp [psi]
    have eF : (pullback.fst (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        (pullback.fst (str A B) g).appLE ⊤ W (by simp) := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
    have eS : (pullback.snd (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        h.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) g ≫ h)
        (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
      have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
      rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, mul_comm]
      let : Algebra A Γ(pullback (str A B) g, W) :=
        (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      symm
      change theta A B g U (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) g).app U).hom (secAlg C h U c) *
          ((pullback.fst (str A B) g).appLE ⊤ W (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B f h)) ⟨W, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine,
    GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, hTensor,
    ← Ideal.map_map, Ideal.comap_map_of_bijective _
      (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalisesStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyOrigin_retraction_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  first | (exact @GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (exact GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (intros; apply GlobalTheory.KeyOriginEnlargeLoc.retract_localises  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentVarUnit (A : Type) [CommRing A] : (LaurentPolynomial A)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← LaurentPolynomial.T_add]; simp

def laurentVar (A : Type) [CommRing A] : (Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.toMonoidHom (laurentVarUnit A)

namespace GmPhi

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn; subst hi; rfl

end GmPhi

def gmPhi (q : ℕ) (A : Type) [CommRing A] (i : ℤ) : Ht q (sp A) 0 (i - 1) →+ Ht q (sp (LaurentPolynomial A)) 1 i where
  toFun a := (cup q (pull _ (spMap (LaurentPolynomial.C : A →+* LaurentPolynomial A)) (tw q (i - 1)) 0 a)
    (kum q (laurentVar A))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add (f := _), AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfEtalePunctured
section
open IsLocalRing

namespace GlobalTheory.LiftHom

theorem liftHom_of_etale_punctured : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] (φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B)), ∃ ψ : A →ₐ[R] B, (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R B))).comp ψ = φ := by
  intro R _ _ hcomp hdim f hf hf0 A _ _ _ he B _ _ _ _ φ
  have hfe := _root_.GlobalTheory.EtaleAway.formallyEtale_away R A he
  generalize hJ : (Ideal.span {f}).map (algebraMap R B) = J at φ ⊢
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨default, ?_⟩
    haveI : Subsingleton (B ⧸ J) := Ideal.Quotient.subsingleton_iff.2 (Subsingleton.elim _ _)
    exact AlgHom.ext fun x => Subsingleton.elim _ _
  haveI : IsAdicComplete (Ideal.span {f}) R :=
    _root_.GlobalTheory.isAdicComplete_of_le_maximalIdeal R hcomp _ ((Ideal.span_singleton_le_iff_mem _).2 hf)
  haveI : IsAdicComplete J B := hJ ▸ GlobalTheory.isAdicComplete_map_of_finite (Ideal.span {f}) B
  have hd : ∀ k : ℕ, ReciprocityTheory.CA.ModDepthGE R (B ⧸ J ^ (k + 1)) 2 := fun k =>
    hJ ▸ GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing R hdim f hf hf0 B (k + 1) (Nat.le_add_left 1 k)
  have hle : ∀ k : ℕ, J ^ (k + 2) ≤ J ^ (k + 1) := fun k => Ideal.pow_le_pow_right (by omega)
  have step : ∀ (k : ℕ) (φk : A →ₐ[R] B ⧸ J ^ (k + 1)),
      ∃ ψ : A →ₐ[R] B ⧸ J ^ (k + 2), (Ideal.Quotient.factorₐ R (hle k)).comp ψ = φk := by
    intro k φk
    refine _root_.GlobalTheory.SquareZeroLift.squareZeroLift R A hfe (B ⧸ J ^ (k + 2)) (B ⧸ J ^ (k + 1)) (hd (k + 1))
      ((hd k).mono (by norm_num)) (Ideal.Quotient.factorₐ R (hle k))
      (Ideal.Quotient.factor_surjective (hle k)) ?_ φk
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker] at hx hy
    change Ideal.Quotient.mk _ a = 0 at hx
    change Ideal.Quotient.mk _ b = 0 at hy
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx hy
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : a * b ∈ J ^ (k + 1) * J ^ (k + 1) := Ideal.mul_mem_mul hx hy
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this
  let φs : (n : ℕ) → A →ₐ[R] B ⧸ J ^ (n + 1) := fun n => Nat.rec
    ((Ideal.quotientEquivAlgOfEq R (pow_one J).symm).toAlgHom.comp φ)
    (fun k φk => Classical.choose (step k φk)) n
  have hφs : ∀ k x, Ideal.Quotient.factor (hle k) (φs (k + 1) x) = φs k x := fun k x =>
    congrArg (fun F : A →ₐ[R] B ⧸ J ^ (k + 1) => F x) (Classical.choose_spec (step k (φs k)))

  have hcc : ∀ {a b c : ℕ} (h1 : J ^ a ≤ J ^ b) (h2 : J ^ b ≤ J ^ c) (y : B ⧸ J ^ a),
      Ideal.Quotient.factor h2 (Ideal.Quotient.factor h1 y) = Ideal.Quotient.factor (h1.trans h2) y := by
    intro a b c h1 h2 y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.Quotient.factor_mk]
  have hchain : ∀ m n (hmn : m ≤ n) x,
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : m + 1 ≤ n + 1) : J ^ (n + 1) ≤ J ^ (m + 1))
        (φs n x) = φs m x := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
      intro x
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φs m x)
      rw [← hb, Ideal.Quotient.factor_mk]
    | succ n hmn ih =>
      intro x
      rw [← ih x, ← hφs n x, hcc]
  let F : (n : ℕ) → A →ₐ[R] B ⧸ J ^ n := fun n =>
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (φs n)
  have hF : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (F n) = F m := by
    intro m n hmn
    ext x
    show Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) (φs n x)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m)) (φs m x)
    rw [← hchain m n hmn x, hcc, hcc]
  refine ⟨IsAdicComplete.liftAlgHom J F hF, ?_⟩
  ext x
  have h1 := IsAdicComplete.mk_liftAlgHom J F hF 1 x
  have h2 : F 1 x = φs 0 x := hφs 0 x
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φ x)
  have h3 : φs 0 x = Ideal.Quotient.mk (J ^ 1) b := by
    show (Ideal.quotientEquivAlgOfEq R (pow_one J).symm) (φ x) = _
    rw [← hb]
    rfl
  rw [h2, h3, Ideal.Quotient.eq, pow_one] at h1
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← hb, Ideal.Quotient.eq]
  exact h1

end GlobalTheory.LiftHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocForallFinset
section
open CategoryTheory AlgebraicGeometry

universe u

namespace GlobalTheory.LocalizedFinsetForAll

theorem loc_forall_finset {U : Scheme.{0}} {ι : Type u} (s : Finset ι)
    {P : ι → (V : Scheme.{0}) → (V ⟶ U) → Prop} (h : ∀ i ∈ s, GlobalTheory.EtC.Loc U (P i)) :
    GlobalTheory.EtC.Loc U fun (V : Scheme.{0}) (g : V ⟶ U) ↦ ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨S, hS, hSP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨T, hT, hTP⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨S ⊓ T, GrothendieckTopology.intersection_covering _ hS hT, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hSP V g hg.1
    · exact hTP V g hg.2 i hi

end GlobalTheory.LocalizedFinsetForAll
end

