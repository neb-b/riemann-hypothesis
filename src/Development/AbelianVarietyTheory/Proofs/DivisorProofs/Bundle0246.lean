module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAll
section
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem tmul_smul_eq_cenMap_mul {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ_[ℓ]) (c : F) (v : B) :
    q ⊗ₜ[ℚ] (c • v) = cenMap ℓ F B (q ⊗ₜ c) * ((1 : ℚ_[ℓ]) ⊗ₜ v) := by
  rw [cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]

def combMap {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B) :
    (Fin d → ℚ_[ℓ] ⊗[ℚ] F) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] B where
  toFun c := ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_mul_assoc]

theorem combMap_apply {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B)
    (c : Fin d → ℚ_[ℓ] ⊗[ℚ] F) :
    combMap ℓ v c = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := rfl

theorem combMap_surjective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Module.Basis (Fin d) F B) :
    Function.Surjective (combMap (F := F) ℓ v) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul q b =>
    rw [← v.sum_repr b, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ⟨Pi.single i (q ⊗ₜ[ℚ] v.repr b i), ?_⟩
    rw [combMap_apply, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]) (by simp),
      Pi.single_eq_same, ← tmul_smul_eq_cenMap_mul]
  | add x y hx hy => exact add_mem hx hy

theorem combMap_injective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ}
    (v : Module.Basis (Fin d) F B) : Function.Injective (combMap (F := F) ℓ v) := by
  haveI : FiniteDimensional ℚ B := Module.Finite.trans F B
  have hdim : Module.finrank ℚ_[ℓ] (Fin d → ℚ_[ℓ] ⊗[ℚ] F) = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) := by
    rw [Module.finrank_pi_fintype, Module.finrank_baseChange, Module.finrank_baseChange,
      ← Module.finrank_mul_finrank ℚ F B, Module.finrank_eq_card_basis v]
    simp [mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 (combMap_surjective ℓ v)

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

theorem exists_basis_mem {F B : Type} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (Λ : Subring B) (hspan : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) :
    ∃ v : Module.Basis (Fin (Module.finrank F B)) F B, ∀ i, v i ∈ Λ := by
  let e := Module.finBasis F B
  choose m hm hmΛ using hspan
  let u : Fin (Module.finrank F B) → Fˣ := fun i =>
    Units.mk0 (m (e i) : F) (Nat.cast_ne_zero.2 (hm (e i)).ne')
  refine ⟨e.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def]
  have h : (u i : F) • e i = (m (e i) : B) * e i := by
    simp [u, Algebra.smul_def]
  rw [h]
  exact hmΛ _

theorem exists_den {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    (Λ : Subring B) (hfin : Module.Finite ℤ Λ) {ι : Type} [Fintype ι] (v : Module.Basis ι F B) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.SepModel.exists_nat_integral
    (Finset.univ.image fun p : s × ι => v.repr ((p.1 : Λ) : B) p.2)
  refine ⟨D, hD, fun x hx => ?_⟩
  let P : Submodule ℤ Λ :=
    { carrier := {y | ∀ i, IsIntegral ℤ ((D : F) * v.repr (y : B) i)}
      add_mem' := by
        intro y z hy hz i
        simp only [Set.mem_setOf_eq, Subring.coe_add, map_add (f := _), Finsupp.add_apply, mul_add] at hy hz ⊢
        exact (hy i).add (hz i)
      zero_mem' := by
        intro i
        simp
        exact isIntegral_zero
      smul_mem' := by
        intro c y hy i
        simp only [Set.mem_setOf_eq] at hy ⊢
        have h2 : v.repr ((c • y : Λ) : B) i = (c : F) * v.repr (y : B) i := by
          rw [show ((c • y : Λ) : B) = c • (y : B) from rfl, map_zsmul, Finsupp.smul_apply,
            zsmul_eq_mul]
        have hc : IsIntegral ℤ (c : F) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := c))
        rw [h2, mul_left_comm]
        exact hc.mul (hy i) }
  have hsP : (s : Set Λ) ⊆ P := fun y hy i =>
    hDs _ (Finset.mem_image.2 ⟨(⟨y, hy⟩, i), Finset.mem_univ _, rfl⟩)
  have hmem : (⟨x, hx⟩ : Λ) ∈ P := by
    have h := Submodule.span_le.mpr hsP
    rw [hs] at h
    exact h Submodule.mem_top
  exact hmem

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

theorem exists_coeffs {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Subring B) {d : ℕ}
    (v : Module.Basis (Fin d) F B) (D : ℕ)
    (hD : ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i)) (hℓ : ¬ ℓ ∣ D)
    (z : ℚ_[ℓ] ⊗[ℚ] B) (hz : z ∈ locOrder ℓ Λ) :
    ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := by
  let S : Submodule ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) :=
    { carrier := {z | ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)}
      add_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        exact ⟨c + c', by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c, rfl⟩
        refine ⟨r • c, ?_⟩
        simp only [Pi.smul_apply, Subalgebra.coe_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul ℚ_[ℓ] r ((c i : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F), map_smul, smul_mul_assoc,
          algebraMap_smul] }
  have gen : ∀ x ∈ Λ, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x ∈ S := by
    intro x hx
    refine ⟨fun i => ⟨_, GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hD x hx i)⟩, ?_⟩
    conv_lhs => rw [← v.sum_repr x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact tmul_smul_eq_cenMap_mul ℓ 1 _ _
  have hz' : z ∈ Subalgebra.toSubmodule (locOrder ℓ Λ) := hz
  rw [locOrder, Algebra.adjoin_eq_span] at hz'
  have hcl : (Submonoid.closure ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (Λ : Set B)) :
      Set (ℚ_[ℓ] ⊗[ℚ] B)) ⊆ S := by
    intro y hy
    have hy' : y ∈ Λ.toSubmonoid.map
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] B) := by
      refine (Submonoid.closure_le.2 ?_) hy
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy'
    exact gen x hx
  exact Submodule.span_le.2 hcl hz'

theorem locOrder_free : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  intro F B _ _ _ _ _ _ _ Λ hΛ hfin hspan
  obtain ⟨v, hvΛ⟩ := exists_basis_mem (F := F) Λ hspan
  obtain ⟨D, hD, hDΛ⟩ := exists_den Λ hfin v
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  let w : Fin (Module.finrank F B) → locOrder ℓ Λ := fun i =>
    ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩
  have hsmul : ∀ (c : cenOrder ℓ F) (x : locOrder ℓ Λ),
      ((c • x : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * x := fun c x => rfl
  have hsum : ∀ c : Fin (Module.finrank F B) → cenOrder ℓ F,
      ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum, combMap_apply]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent (cenOrder ℓ F) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : combMap (F := F) ℓ v (fun i => (g i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by
      rw [← hsum, hg, map_zero]
      rfl
    exact Subtype.ext (congrFun (combMap_injective ℓ v h0) i)
  have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w) := by
    rintro ⟨z, hz⟩ -
    obtain ⟨c, hc⟩ := exists_coeffs ℓ Λ v D hDΛ hℓ z hz
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩
  haveI : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  let bas := Module.Basis.mk hli hsp
  exact ⟨Module.Free.of_basis bas, by rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]⟩

end GlobalTheory.LocMatrix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairSplitSum
section
open IsLocalRing Polynomial

open scoped TensorProduct

namespace GlobalTheory.KeyOriginCut

theorem etale_of_isZTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (h : IsZTorsor B D q act) :
    Algebra.Etale B D := by
  obtain ⟨hfin, hproj, hff, hbij⟩ := h
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) with hΦ
  have hmul : ∀ x : D ⊗[B] D, Algebra.TensorProduct.lmul' B x = Φ x 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [hΦ, Algebra.TensorProduct.productMap_apply_tmul]
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  have hidem : IsIdempotentElem (KaehlerDifferential.ideal B D) := by
    obtain ⟨e, he⟩ := hbij.2 (1 - Pi.single (1 : Multiplicative (ZMod q)) (1 : D))
    have heI : e ∈ KaehlerDifferential.ideal B D := by
      rw [KaehlerDifferential.ideal, RingHom.mem_ker]
      change Algebra.TensorProduct.lmul' B e = 0
      rw [hmul, he]; simp
    apply le_antisymm Ideal.mul_le_left
    intro x hx
    have hx0 : Φ x 1 = 0 := by
      rw [← hmul]
      exact (RingHom.mem_ker).1 hx
    have hxe : x = x * e := by
      apply hbij.1
      rw [map_mul, he]
      funext g
      by_cases hg : g = 1
      · subst hg; simp [hx0]
      · simp [Pi.single_apply, hg]
    rw [hxe]
    exact Ideal.mul_mem_mul hx heI
  haveI : Subsingleton Ω[D⁄B] := (Ideal.cotangent_subsingleton_iff _).2 hidem
  haveI : Algebra.FormallyUnramified B D := ⟨inferInstance⟩
  haveI : Module.Flat B D := inferInstance
  haveI : Module.FinitePresentation B D := Module.finitePresentation_of_projective B D
  haveI : Algebra.FinitePresentation B D :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite B D).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory.KeyOriginCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparable
section
open Polynomial Matrix

namespace GlobalTheory.LocalCommutant

open GlobalTheory.ClassParam

variable {S : Type} [CommRing S] {n : ℕ}

theorem krylov_mulVec (Y : Matrix (Fin n) (Fin n) S) (v c : Fin n → S) :
    krylov Y v *ᵥ c = ∑ j, c j • (Y ^ (j : ℕ) *ᵥ v) := by
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem aeval_sum_monomial (Y : Matrix (Fin n) (Fin n) S) (c : Fin n → S) :
    aeval Y (∑ j : Fin n, monomial (j : ℕ) (c j)) = ∑ j : Fin n, c j • Y ^ (j : ℕ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, aeval_monomial, Algebra.smul_def]

theorem exists_isUnit_krylov (R : Type) [CommRing R] [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R)
    (hs : Y.charpoly.Separable) : ∃ v, IsUnit (krylov Y v) := by
  obtain ⟨w, hw⟩ := exists_cyclic_field (Y.map (IsLocalRing.residue R)) (by rw [charpoly_map]; exact hs.map)
  choose e he using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨e, (Matrix.isUnit_iff_isUnit_det _).2 ?_⟩
  have h1 : w = (IsLocalRing.residue R) ∘ e := funext fun i => (he i).symm
  rw [h1, ← krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hw
  exact (isUnit_map_iff (IsLocalRing.residue R) _).1 (isUnit_iff_ne_zero.2 hw)

theorem exists_aeval_of_comm (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ)
    (Y T : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) (hc : T * Y = Y * T) :
    ∃ p : R[X], T = aeval Y p := by
  obtain ⟨e, hK⟩ := exists_isUnit_krylov R Y hs
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hK
  set K := krylov Y e
  set c := K⁻¹ *ᵥ (T *ᵥ e)
  refine ⟨∑ j : Fin n, monomial (j : ℕ) (c j), ?_⟩
  set p : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  set D := T - aeval Y p
  have hKc : K *ᵥ c = T *ᵥ e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hDe : D *ᵥ e = 0 := by
    have h2 : aeval Y p *ᵥ e = K *ᵥ c := by
      rw [aeval_sum_monomial, Matrix.sum_mulVec, krylov_mulVec]
      simp [Matrix.smul_mulVec]
    rw [Matrix.sub_mulVec, h2, hKc, sub_self]
  have hpY : aeval Y p * Y = Y * aeval Y p := by
    calc aeval Y p * Y = aeval Y (p * X) := by simp
      _ = aeval Y (X * p) := by rw [mul_comm]
      _ = Y * aeval Y p := by simp
  have hDY : Commute D Y := Commute.sub_left hc hpY
  have hDK : D * K = 0 := by
    ext i j
    have h2 : D *ᵥ (Y ^ (j : ℕ) *ᵥ e) = 0 := by
      rw [Matrix.mulVec_mulVec, (hDY.pow_right _).eq, ← Matrix.mulVec_mulVec, hDe, Matrix.mulVec_zero]
    have := congrFun h2 i
    simpa [K, krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hD : D = 0 := by
    calc D = D * K * K⁻¹ := by rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
      _ = 0 := by rw [hDK, zero_mul]
  exact sub_eq_zero.1 hD

end GlobalTheory.LocalCommutant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationNormalizationRootAdjoinIsDVR
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LocNormDVR

theorem artinian (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D]
    [Module.Finite S D] : IsArtinianRing (TensorProduct S D L) := by
  haveI : IsArtinianRing (TensorProduct S L D) := IsArtinianRing.of_finite L _
  exact RingEquiv.isArtinianRing (Algebra.TensorProduct.comm S L D).toRingEquiv

theorem main : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∃ _ : IsDomain (Localization.AtPrime Q), IsDiscreteValuationRing (Localization.AtPrime Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he _ _ Q _
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : FaithfulSMul S D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 : algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) a =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) b := by
      rw [← φ.commutes, ← φ.commutes, hab]
    set pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne') with hpb
    have hd : 0 < pb.dim := by
      rw [hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C _]; exact he0
    have h0 : pb.basis ⟨0, hd⟩ = 1 := by rw [PowerBasis.coe_basis]; simp
    have key : ∀ s : S, pb.basis.repr (algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) s)
        ⟨0, hd⟩ = s := by
      intro s
      rw [Algebra.algebraMap_eq_smul_one, ← h0, map_smul, Module.Basis.repr_self]
      simp
    rw [← key a, ← key b, h1]
  haveI : Module.Finite D (integralClosure D (TensorProduct S D L)) := _root_.GlobalTheory.NormFin.main S K L D
  haveI : IsArtinianRing (TensorProduct S D L) := artinian S L D
  haveI : IsReduced (TensorProduct S D L) := GlobalTheory.T.kummer_uniformiser_adjoinRoot_tensor_isReduced S K L π e D ⟨φ⟩ hπ he
  obtain ⟨hdom, hic⟩ := _root_.GlobalTheory.localization_integralClosure_isDomain_isIntegrallyClosed D (TensorProduct S D L) Q
  refine ⟨hdom, ?_⟩
  haveI : IsNoetherianRing (integralClosure D (TensorProduct S D L)) :=
    IsNoetherianRing.of_finite D _
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  have htf : ∀ a : D, a ≠ 0 → ∀ x : integralClosure D (TensorProduct S D L), a • x = 0 → x = 0 := by
    intro a ha x hax
    have hinj : Function.Injective (LinearMap.rTensor L (LinearMap.mulLeft S a)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun y z h => (mul_right_injective₀ ha) h)
    have hsmul : ∀ z : TensorProduct S D L,
        a • z = LinearMap.rTensor L (LinearMap.mulLeft S a) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul y l => simp [TensorProduct.smul_tmul']
      | add u v hu hv => rw [smul_add, map_add (f := _), hu, hv]
    have h1 : a • (x : TensorProduct S D L) = 0 := congrArg Subtype.val hax
    rw [hsmul, ← map_zero (LinearMap.rTensor L (LinearMap.mulLeft S a))] at h1
    exact Subtype.ext (hinj h1)
  have hQu : Q.comap (algebraMap D (integralClosure D (TensorProduct S D L))) = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := D) Q)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hϖQ : algebraMap D (integralClosure D (TensorProduct S D L)) ϖ ∈ Q := by
    rw [← Ideal.mem_comap, hQu]; exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hnf : ¬ IsField (Localization.AtPrime Q) := by
    intro hF
    have hmax : maximalIdeal (Localization.AtPrime Q) = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).1 hF
    have hmem : algebraMap _ (Localization.AtPrime Q)
        (algebraMap D (integralClosure D (TensorProduct S D L)) ϖ) ∈
        maximalIdeal (Localization.AtPrime Q) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hϖQ
    rw [hmax, Ideal.mem_bot, IsLocalization.map_eq_zero_iff Q.primeCompl] at hmem
    obtain ⟨⟨t, ht⟩, hts⟩ := hmem
    have ht0 : t = 0 := htf ϖ hϖ.ne_zero t (by rw [Algebra.smul_def, mul_comm]; exact hts)
    exact ht (ht0 ▸ Q.zero_mem)
  refine ((IsDiscreteValuationRing.TFAE (Localization.AtPrime Q) hnf).out 1 4).2
    (⟨hic, ?_⟩ : IsIntegrallyClosed (Localization.AtPrime Q) ∧
      ∃! P : Ideal (Localization.AtPrime Q), P ≠ ⊥ ∧ P.IsPrime)
  refine ⟨maximalIdeal _, ⟨⟨?_, inferInstance⟩, ?_⟩⟩
  · intro h; exact hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  · rintro P ⟨hP0, hP⟩
    by_contra hne
    have hlt : P < maximalIdeal _ := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.ne_top) hne
    have hbl : (⊥ : Ideal (Localization.AtPrime Q)) < P := bot_lt_iff_ne_bot.2 hP0
    have h1 : (⊥ : Ideal (Localization.AtPrime Q)).comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) <
        P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) := (IsLocalization.orderEmbedding Q.primeCompl (Localization.AtPrime Q)).strictMono hbl
    have h2 : P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) <
        (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) :=
      (IsLocalization.orderEmbedding Q.primeCompl (Localization.AtPrime Q)).strictMono hlt
    have hc : (maximalIdeal (Localization.AtPrime Q)).comap
        (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.under_maximalIdeal
    rw [hc] at h2
    haveI : ((⊥ : Ideal (Localization.AtPrime Q)).comap
        (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).IsPrime := Ideal.comap_isPrime _ _
    haveI : (P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).IsPrime := Ideal.comap_isPrime _ _
    have k1 := Ideal.IsIntegral.comap_lt_comap (R := D) h1
    have k2 := Ideal.IsIntegral.comap_lt_comap (R := D) h2
    change _ < Q.comap (algebraMap D (integralClosure D (TensorProduct S D L))) at k2
    rw [hQu] at k2
    have hp1 : ((P.comap (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q))).comap
        (algebraMap D (integralClosure D (TensorProduct S D L)))).IsPrime := Ideal.comap_isPrime _ _
    have hmx := hp1.isMaximal (ne_bot_of_gt k1)
    exact (ne_of_lt k2) (IsLocalRing.eq_maximalIdeal hmx)

end GlobalTheory.LocNormDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleFaithfullyFlatStatement
section
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat : ∀ (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D), IsPushout f f j₁ j₂ → IsPushout j₂ j₁ d₁₂ d₂₃ → j₁ ≫ d₁₃ = j₁ ≫ d₁₂ → j₂ ≫ d₁₃ = j₂ ≫ d₂₃ → f.hom.FaithfullyFlat → ∀ c : Cˣ, d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C) → ∀ P : Ideal R, P.IsPrime → ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  first | exact @GlobalTheory.UnitCocycle.exists_local | exact GlobalTheory.UnitCocycle.exists_local | (intros; apply GlobalTheory.UnitCocycle.exists_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal
section
open IsLocalRing RingTheory.Sequence

namespace GlobalTheory

theorem modDepthGE_three_of_free_of_isRegularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  intro R _ _ hd M _ _ _ _ _
  obtain ⟨xs, h, hl⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg : IsRegular R xs := isRegular_of_ofList_eq_maximalIdeal h hl.le
  have h3 : 3 ≤ xs.length := by
    rw [← hl] at hd
    exact_mod_cast hd
  have hm : ∀ r ∈ xs.take 3, r ∈ maximalIdeal R := fun r hr =>
    h ▸ Ideal.subset_span (List.mem_of_mem_take hr)
  have hw : IsWeaklyRegular R (xs.take 3) := by
    have := hreg.1
    rw [← List.take_append_drop 3 xs, isWeaklyRegular_append_iff] at this
    exact this.1
  have hwM : IsWeaklyRegular M (xs.take 3) := by
    have := hw.isWeaklyRegular_lTensor (M₂ := M)
    exact ((TensorProduct.rid R M).isWeaklyRegular_congr _).mp this
  refine ⟨xs.take 3, by simp [h3], hm, ?_⟩
  exact (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hwM

end GlobalTheory
end

