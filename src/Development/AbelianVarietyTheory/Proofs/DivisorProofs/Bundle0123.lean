module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarExistsFractionLocalisationNormalisation
section
open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

set_option maxHeartbeats 1000000 in
theorem exists_frac_closure : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)), Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal] (w : Localization.AtPrime Q), ∃ x z : Localization.AtPrime Q, x ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ nonZeroDivisors (Localization.AtPrime Q) ∧ z * w = x := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ _ _ _ _ Q _ w

  have hS : ∀ r : S, algebraMap D (Localization.AtPrime Q) (algebraMap S D r) =
      locHom Q (algebraMap _ _ (algebraMap S (integralClosure S L) r)) := by
    intro r
    rw [locHom_algebraMap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
      (Localization.AtPrime Q)]
    congr 1
    apply Subtype.ext
    simp only [toNorm_coe, Subalgebra.coe_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [TensorProduct.smul_tmul]
  have hD : ∀ d : D, algebraMap D (Localization.AtPrime Q) d ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro d
    rw [← ψ.symm_apply_apply d]
    generalize ψ d = a
    have hd : a ∈ Algebra.adjoin S ({AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)} : Set _) := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    induction hd using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subring.subset_closure (Or.inr rfl)
    | algebraMap r =>
      rw [AlgEquiv.commutes, hS]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

  have hT : ∀ u : TensorProduct S D (integralClosure S L), ∃ b : integralClosure D (TensorProduct S D L),
      (b : TensorProduct S D L) = Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u ∧
      algebraMap _ (Localization.AtPrime Q) b ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul d o =>
      refine ⟨algebraMap D _ d * toNorm S L D o, ?_, ?_⟩
      · simp [toNorm_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      · rw [map_mul, ← IsScalarTower.algebraMap_apply, ← locHom_algebraMap]
        exact mul_mem (hD d) (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
    | add u v hu hv =>
      obtain ⟨b1, h1, m1⟩ := hu
      obtain ⟨b2, h2, m2⟩ := hv
      exact ⟨b1 + b2, by simp [h1, h2], by rw [(algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)).map_add]; exact add_mem m1 m2⟩
  have hI : ∀ y : TensorProduct S D L, ∃ σ : S, σ ≠ 0 ∧ ∃ u : TensorProduct S D (integralClosure S L),
      Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u = σ • y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul d l =>
      have hl : IsAlgebraic S l := (IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)
      obtain ⟨σ, hσ, hint⟩ := hl.exists_integral_multiple
      exact ⟨σ, hσ, d ⊗ₜ ⟨σ • l, hint⟩, by simp [TensorProduct.tmul_smul]⟩
    | add y1 y2 h1 h2 =>
      obtain ⟨σ1, n1, u1, e1⟩ := h1
      obtain ⟨σ2, n2, u2, e2⟩ := h2
      refine ⟨σ1 * σ2, mul_ne_zero n1 n2, σ2 • u1 + σ1 • u2, ?_⟩
      rw [map_add (f := _), map_smul, map_smul, e1, e2, smul_add, smul_smul, smul_smul, mul_comm σ1 σ2]
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl w
  obtain ⟨σ1, n1, u1, e1⟩ := hI (b : TensorProduct S D L)
  obtain ⟨σ2, n2, u2, e2⟩ := hI ((s : integralClosure D (TensorProduct S D L)) : TensorProduct S D L)
  obtain ⟨bb, hbb, mb⟩ := hT (σ2 • u1)
  obtain ⟨ss, hss, ms⟩ := hT (σ1 • u2)
  set a : integralClosure D (TensorProduct S D L) := algebraMap D _ (algebraMap S D (σ1 * σ2)) with ha
  have hcoe : ∀ y : integralClosure D (TensorProduct S D L), ((a * y : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = (σ1 * σ2) • (y : TensorProduct S D L) := by
    intro y
    rw [ha, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have hbb' : bb = a * b := by
    apply Subtype.ext
    rw [hcoe, hbb, map_smul, e1, smul_smul, mul_comm σ2 σ1]
  have hss' : ss = a * s := by
    apply Subtype.ext
    rw [hcoe, hss, map_smul, e2, smul_smul]
  have hL : algebraMap S L (σ1 * σ2) ≠ 0 := by
    intro h
    rw [IsScalarTower.algebraMap_apply S K L, map_eq_zero, IsFractionRing.to_map_eq_zero_iff] at h
    exact mul_ne_zero n1 n2 h
  have hU : IsUnit (algebraMap S (TensorProduct S D L) (σ1 * σ2)) := by
    rw [← (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes]
    exact (IsUnit.mk0 _ hL).map _
  have haN : a ∈ nonZeroDivisors (integralClosure D (TensorProduct S D L)) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have := congrArg Subtype.val hy
    rw [mul_comm, hcoe, Algebra.smul_def, ZeroMemClass.coe_zero] at this
    exact Subtype.ext (by simpa using (hU.mul_right_eq_zero).1 this)
  refine ⟨algebraMap _ _ bb, algebraMap _ _ ss, mb, ms, ?_, ?_⟩
  · rw [hss', map_mul]
    have h1 : algebraMap _ (Localization.AtPrime Q) a ∈ nonZeroDivisors (Localization.AtPrime Q) :=
      IsLocalization.map_nonZeroDivisors_le Q.primeCompl (Localization.AtPrime Q)
        (Submonoid.mem_map_of_mem (algebraMap _ (Localization.AtPrime Q)) haN)
    exact mul_mem h1 (IsLocalization.map_units (Localization.AtPrime Q) s).mem_nonZeroDivisors
  · rw [hss', hbb', map_mul, map_mul, mul_assoc, IsLocalization.mk'_spec']

end GlobalTheory.AbhyankarLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarExistsLocalKummerElement
section
open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

open TensorProduct


set_option maxHeartbeats 1000000 in
theorem exists_kummer_element (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ)
    (D : Type) [CommRing D] [Algebra S D]
    (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) :
    Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D]
    (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal] (m k : ℕ)
    (ϖ : Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D)))
    (u : (Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D)))ˣ), m * k = e →
    algebraMap S _ π = ϖ ^ m *
      (u : Localization.AtPrime (Q.comap (GlobalTheory.AbhyankarLocal.toNorm S L D))) →
    ∃ y : Localization.AtPrime Q, y ^ m = GlobalTheory.AbhyankarLocal.locHom Q u ∧
      (algebraMap D (Localization.AtPrime Q)
        (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))) ^ k =
        GlobalTheory.AbhyankarLocal.locHom Q ϖ * y := by
  intro hπ he _ _ Q _ m k ϖ u hmk hrel
  generalize hU : (u : Localization.AtPrime (Q.comap (toNorm S L D))) = U at hrel ⊢
  have hm : m ≠ 0 := by rintro rfl; simp at hmk; omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set t := ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) with ht_def
  have ht : t ^ e = algebraMap S D π := by
    have h0 := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h0
    have h1 : AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S) ^ e =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) π := by
      rw [AdjoinRoot.algebraMap_eq]; exact sub_eq_zero.mp h0
    have := congrArg ψ.symm h1
    rw [map_pow, AlgEquiv.commutes] at this
    exact this
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (Q.comap (toNorm S L D)).primeCompl ϖ
  obtain ⟨⟨a', s'⟩, hs'⟩ := IsLocalization.mk'_surjective (Q.comap (toNorm S L D)).primeCompl
    U
  simp only at hs hs'
  have hsA : ϖ * algebraMap _ (Localization.AtPrime (Q.comap (toNorm S L D))) (s : integralClosure S L) =
      algebraMap _ _ a := by rw [← hs]; exact IsLocalization.mk'_spec _ a s
  have hs'A : U *
      algebraMap _ (Localization.AtPrime (Q.comap (toNorm S L D))) (s' : integralClosure S L) =
      algebraMap _ _ a' := by rw [← hs']; exact IsLocalization.mk'_spec _ a' s'
  have hinj : Function.Injective (algebraMap (integralClosure S L)
      (Localization.AtPrime (Q.comap (toNorm S L D)))) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (Q.comap (toNorm S L D)))
  have hO : algebraMap S (integralClosure S L) π * (s : integralClosure S L) ^ (n + 1) *
      (s' : integralClosure S L) = a ^ (n + 1) * a' := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hrel,
      ← hsA, ← hs'A]
    ring
  have hL := congrArg (fun x : integralClosure S L => (x : L)) hO
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] at hL
  have hSL : Function.Injective (algebraMap S L) := by
    rw [IsScalarTower.algebraMap_eq S K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
  have hπL : algebraMap S L π ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap S L)]; exact fun h => hπ.ne_zero (hSL h)
  have hne : ∀ x : (Q.comap (toNorm S L D)).primeCompl, ((x : integralClosure S L) : L) ≠ 0 := by
    intro x hx
    apply x.2
    have : (x : integralClosure S L) = 0 := Subtype.ext hx
    rw [this]; exact Ideal.zero_mem _
  have haL : (a : L) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero n), zero_mul] at hL
    exact mul_ne_zero (mul_ne_zero hπL (pow_ne_zero _ (hne s))) (hne s') hL
  set w : TensorProduct S D L := (t ^ k) ⊗ₜ[S] (((s' : integralClosure S L) : L) *
    ((s : integralClosure S L) : L) / (a : L)) with hw
  have hwm : w ^ (n + 1) = ((toNorm S L D ((s' : integralClosure S L) ^ n * a') :
      integralClosure D (TensorProduct S D L)) : TensorProduct S D L) := by
    rw [toNorm_coe, hw, Algebra.TensorProduct.tmul_pow, ← pow_mul, mul_comm k, hmk, ht,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    push_cast
    rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero _ haL)]
    linear_combination ((s' : integralClosure S L) : L) ^ n * hL
  have hwint : IsIntegral D w := IsIntegral.of_pow (Nat.succ_pos n)
    (by rw [hwm]; exact (toNorm S L D _).2)
  let b : integralClosure D (TensorProduct S D L) := ⟨w, hwint⟩
  have hbm : b ^ (n + 1) = toNorm S L D ((s' : integralClosure S L) ^ n * a') :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hwm)
  have hbrel : toNorm S L D a * b = toNorm S L D ((s : integralClosure S L) * s') *
      algebraMap D (integralClosure D (TensorProduct S D L)) (t ^ k) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, toNorm_coe, toNorm_coe, Subalgebra.coe_algebraMap,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show ((1 : D) ⊗ₜ[S] (a : L)) * w = _
    rw [hw, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    congr 1
    push_cast
    rw [mul_comm (a : L), div_mul_cancel₀ _ haL]
    ring
  have hσ : toNorm S L D (s' : integralClosure S L) ∈ Q.primeCompl := s'.2
  have hσ2 : toNorm S L D (s : integralClosure S L) ∈ Q.primeCompl := s.2
  obtain ⟨y, hy⟩ : ∃ y : Localization.AtPrime Q,
      y * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s') = algebraMap _ _ b :=
    ⟨_, IsLocalization.mk'_spec _ b (⟨_, hσ⟩ : Q.primeCompl)⟩
  have hu1 : IsUnit (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')) :=
    IsLocalization.map_units _ (⟨_, hσ⟩ : Q.primeCompl)
  have hu2 : IsUnit (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s)) :=
    IsLocalization.map_units _ (⟨_, hσ2⟩ : Q.primeCompl)
  have hϖW : locHom Q ϖ * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s) =
      algebraMap _ _ (toNorm S L D a) := by
    have := congrArg (locHom Q) hsA
    rw [map_mul, locHom_algebraMap Q (s : integralClosure S L), locHom_algebraMap Q a] at this
    exact this
  have huW : locHom Q U *
      algebraMap _ (Localization.AtPrime Q) (toNorm S L D s') =
      algebraMap _ _ (toNorm S L D a') := by
    have := congrArg (locHom Q) hs'A
    rw [map_mul, locHom_algebraMap Q (s' : integralClosure S L), locHom_algebraMap Q a'] at this
    exact this
  refine ⟨y, ?_, ?_⟩
  · rw [← (hu1.pow (n + 1)).mul_left_inj, ← mul_pow, hy, ← map_pow, hbm, pow_succ'
      (algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')), ← mul_assoc, huW]
    simp only [map_mul, map_pow]
    ring
  · rw [← (hu1.mul hu2).mul_left_inj]
    calc _ = algebraMap _ (Localization.AtPrime Q) (toNorm S L D ((s : integralClosure S L) * s') *
          algebraMap D (integralClosure D (TensorProduct S D L)) (t ^ k)) := by
          simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
          ring
      _ = algebraMap _ (Localization.AtPrime Q) (toNorm S L D a * b) := by rw [hbrel]
      _ = (locHom Q ϖ * algebraMap _ (Localization.AtPrime Q) (toNorm S L D s)) *
          (y *
            algebraMap _ (Localization.AtPrime Q) (toNorm S L D s')) := by
          rw [hϖW, hy, map_mul]
      _ = _ := by ring

end GlobalTheory.AbhyankarLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarRootMemMaximalIdealNonZeroDivisors
section
open IsLocalRing

namespace GlobalTheory.AbhyankarRootUnit

open scoped TensorProduct

theorem root_not_isUnit (S : Type) [CommRing S] [IsLocalRing S] (π : S)
    (hπ : π ∈ maximalIdeal S) (e : ℕ) (he : 0 < e) :
    ¬ IsUnit (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) := by
  intro hu
  have hev : (Polynomial.X ^ e - Polynomial.C π : Polynomial S).eval₂
      (algebraMap S (ResidueField S)) 0 = 0 := by
    simp [Polynomial.eval₂_sub, zero_pow he.ne']
    exact hπ
  have := hu.map (AdjoinRoot.lift (algebraMap S (ResidueField S)) 0 hev)
  rw [AdjoinRoot.lift_root] at this
  exact not_isUnit_zero this

theorem root_pow (S : Type) [CommRing S] (π : S) (e : ℕ) :
    AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S) ^ e =
      algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)) π := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h]; rfl

theorem mem_maximalIdeal_and_mem_nonZeroDivisors_of_pow (S L : Type) [CommRing S] [Field L]
    [Algebra S L] (π : S) (hπL : algebraMap S L π ≠ 0) (e : ℕ) (he : 0 < e) (D : Type)
    [CommRing D] [IsLocalRing D] [Algebra S D] (t : D) (ht : t ^ e = algebraMap S D π)
    (htu : ¬ IsUnit t) (Q : Ideal (integralClosure D (D ⊗[S] L))) [Q.IsMaximal] :
    algebraMap D (Localization.AtPrime Q) t ∈ maximalIdeal (Localization.AtPrime Q) ∧
      algebraMap D (Localization.AtPrime Q) t ∈ nonZeroDivisors (Localization.AtPrime Q) := by
  have htDm : t ∈ maximalIdeal D := htu
  haveI hQmax : (Q.comap (algebraMap D (integralClosure D (D ⊗[S] L)))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) Q
  have hcomap : Q.comap (algebraMap D (integralClosure D (D ⊗[S] L))) = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal hQmax
  have htQ : algebraMap D (integralClosure D (D ⊗[S] L)) t ∈ Q := by
    rw [← Ideal.mem_comap, hcomap]; exact htDm
  have hsc : algebraMap D (Localization.AtPrime Q) t =
      algebraMap (integralClosure D (D ⊗[S] L)) (Localization.AtPrime Q)
        (algebraMap D (integralClosure D (D ⊗[S] L)) t) :=
    IsScalarTower.algebraMap_apply D (integralClosure D (D ⊗[S] L)) _ t
  refine ⟨?_, ?_⟩
  · rw [hsc, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q]
    exact htQ
  · rw [hsc]
    apply IsLocalization.nonZeroDivisors_le_comap Q.primeCompl (Localization.AtPrime Q)
    have hpow : (algebraMap D (D ⊗[S] L) t) ^ e =
        Algebra.TensorProduct.includeRight (algebraMap S L π) := by
      rw [← map_pow, ht, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.algebraMap_eq_smul_one π, Algebra.algebraMap_eq_smul_one π,
        TensorProduct.smul_tmul]
    have hunit : IsUnit (algebraMap D (D ⊗[S] L) t) := by
      rw [← isUnit_pow_iff he.ne', hpow]
      exact (Ne.isUnit hπL).map _
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · apply Subtype.ext
      have h1 := congrArg (fun x : integralClosure D (D ⊗[S] L) => (x : D ⊗[S] L)) hb
      simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h1
      simpa using hunit.mul_right_eq_zero.1 h1
    · apply Subtype.ext
      have h1 := congrArg (fun x : integralClosure D (D ⊗[S] L) => (x : D ⊗[S] L)) hb
      simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h1
      simpa using hunit.mul_left_eq_zero.1 h1

theorem root_mem_maximalIdeal_and_mem_nonZeroDivisors : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)), Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal], algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S))) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧ algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S))) ∈ nonZeroDivisors (Localization.AtPrime Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ hπ he _ _ Q _
  have hπm : π ∈ maximalIdeal S := hπ.not_isUnit
  have hπL : algebraMap S L π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S K L]
    intro h0
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h0
    exact hπ.ne_zero h0
  refine mem_maximalIdeal_and_mem_nonZeroDivisors_of_pow S L π hπL e he D _ ?_ ?_ Q
  · rw [← map_pow, root_pow, AlgEquiv.commutes]
  · intro h
    exact root_not_isUnit S π hπm e he (by simpa using h.map ψ)

end GlobalTheory.AbhyankarRootUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPa
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory.NormLe

theorem absNorm_le_abs_norm {F : Type} [Field F] [NumberField F] (𝔟 : Frac F) {b : F}
    (hb : b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (hb0 : b ≠ 0) :
    FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ |Algebra.norm ℚ b| := by
  set B : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  set S : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.spanSingleton (𝓞 F)⁰ b
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * S
  have hSB : S ≤ B := (FractionalIdeal.spanSingleton_le_iff_mem).2 hb
  have hSJ : S = B * J := by
    simp only [J, B, ← mul_assoc, Units.mul_inv, one_mul]
  have hJ1 : J ≤ 1 := by
    have : J ≤ ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * B := by
      simp only [J]; gcongr
    simpa [B, Units.inv_mul] using this
  obtain ⟨I₀, hI₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  have hS0 : S ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb0
  have hJ0 : J ≠ 0 := by
    rintro h; rw [h, mul_zero] at hSJ; exact hS0 hSJ
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI₀, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I₀ ≠ 0 := by
      intro h
      rw [Ideal.absNorm_eq_zero_iff] at h
      apply hJ0; rw [← hI₀, h]; simp
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have key : FractionalIdeal.absNorm S = FractionalIdeal.absNorm B * FractionalIdeal.absNorm J := by
    rw [hSJ, map_mul]
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 F) b]
  change FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm S
  rw [key]
  have := FractionalIdeal.absNorm_nonneg B
  nlinarith

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟),
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by
  intro F _ _ _ 𝔞 𝔟 p
  obtain ⟨⟨ν, b⟩, h𝔞, h𝔟, hpos⟩ := p
  dsimp only at h𝔞 h𝔟 hpos ⊢
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have τ : Emb F := w.embedding_of_isReal (IsTotallyReal.isReal w)
  have hνb : ν * b ≠ 0 := fun h => by have := hpos τ; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hle := absNorm_le_abs_norm 𝔟 h𝔟 hb0
  have hB0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔟.ne_zero
  have hnpos : 0 < nrm 𝔟 := by
    unfold nrm
    have h1 := FractionalIdeal.absNorm_nonneg (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
    have h2 : FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      fun h => hB0 (FractionalIdeal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
  have hle' : nrm 𝔟 ≤ |(Algebra.norm ℚ b : ℝ)| := by
    unfold nrm; rw [← Rat.cast_abs]; exact_mod_cast hle
  rw [le_div_iff₀ hnpos, map_mul, Rat.cast_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hle' (abs_nonneg _)

end GlobalTheory.NormLe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionMapInvariants
section
namespace GlobalTheory


open AdicCompletion in
theorem adicCompletion_map_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first
  | exact @_root_.GlobalTheory.LinearMapDifferenceFormula.main
  | exact _root_.GlobalTheory.LinearMapDifferenceFormula.main
  | (apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearMapDifferenceFormula.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearMapDifferenceFormula.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinHomExtendOfDenominator
section
namespace GlobalTheory

theorem adjoin_hom_extend_of_denominator (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hψ : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first
  | exact @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | (apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootUniformiserIsDVRStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_uniformiser_isDVR) | (exact GlobalTheory.adjoinRoot_uniformiser_isDVR) | (intros; apply GlobalTheory.adjoinRoot_uniformiser_isDVR  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootXPowSubUniformizerIsDomainStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (exact GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (intros; apply GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain  <;> assumption)
end

