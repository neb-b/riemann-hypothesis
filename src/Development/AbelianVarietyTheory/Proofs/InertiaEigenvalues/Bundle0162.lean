module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualStableLatticeUnitOrbitsFinite
section
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.OrbitFinite

theorem orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B hsep x hxu hxσ
  by_cases h0 : ∃ L0, L0 ∈ B.X x
  swap
  · push_neg at h0
    haveI : IsEmpty (B.X x) := ⟨fun L => h0 L.1 L.2⟩
    refine ⟨?_, fun L hL => absurd hL (h0 L)⟩
    unfold Orb
    infer_instance
  obtain ⟨L0, hL0⟩ := h0
  have hgi : IsIntegral K.O B.g := isIntegral_of_isLat_stable L0 hL0.1 B.g hL0.2.1
  obtain ⟨c, hc0, hc⟩ := _root_.GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin K B hsep hgi

  have hadj : ∀ L ∈ B.X x, ∀ a ∈ Algebra.adjoin K.O ({B.g} : Set B.A), ∀ y ∈ L, a * y ∈ L := by
    intro L hL a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hL.2.1
    | algebraMap r =>
      intro y hy
      rw [← Algebra.smul_def]
      exact L.smul_mem r hy
    | add a b _ _ ha hb =>
      intro y hy
      rw [add_mul]
      exact L.add_mem (ha y hy) (hb y hy)
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb y hy)
  have hcL : ∀ L ∈ B.X x, ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L :=
    fun L hL u hu y hy => hadj L hL _ (hc u hu) y hy
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hSf, hSl, hS⟩ := _root_.GlobalTheory.HullClasses.exists_unit_mulLat_mem_of_selfDual_lattice K B hsep x hxu hxσ c hc0
    set W : Set (Submodule K.O B.A) :=
      (⋃ J ∈ S, {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) J ≤ M ∧ M ≤ J}) ∩ B.X x with hW
    have hWf : W.Finite :=
      (hSf.biUnion fun J hJ => GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B J (hSl J hJ) c hc0).subset Set.inter_subset_left
    haveI : Finite W := hWf.to_subtype
    let f : W → Orb K.O B.T (B.X x) := fun M => Quot.mk _ ⟨M.1, M.2.2⟩
    apply Finite.of_surjective f
    intro o
    set L := (Quot.out o).1 with hLdef
    have hL : L ∈ B.X x := (Quot.out o).2
    obtain ⟨J, hJl, hJs, hJ1, hJ2, hJc, hLJ⟩ := _root_.GlobalTheory.HullLat.exists_hull K B x c hc0 L hL (hcL L hL)
    obtain ⟨t, ht, htS⟩ := hS J hJl hJs hJ1 hJ2
    have hcomm : mulLat K.O (algebraMap K.O B.A c) (mulLat K.O (t : B.A) J) =
        mulLat K.O (t : B.A) (mulLat K.O (algebraMap K.O B.A c) J) := by
      unfold mulLat
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext y
      simp [mul_left_comm]
    have hmem : mulLat K.O (t : B.A) L ∈ W := by
      refine ⟨Set.mem_biUnion htS ⟨?_, Submodule.map_mono hLJ⟩, _root_.GlobalTheory.UnitLemma.TorusAction.torus_mem_X K B x t ht L hL⟩
      rw [hcomm]
      exact Submodule.map_mono hJc
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [← Quot.out_eq o]
    exact (Quot.sound ⟨t, ht, rfl⟩).symm
  · intro L hL
    refine ⟨?_, _root_.GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero K B L hL.1 c hc0 (hcL L hL)⟩
    rintro t ⟨hs, -⟩
    refine ⟨isIntegral_of_isLat_stable L hL.1 (t : B.A) fun y hy => (hs y).mp hy, ?_⟩
    refine isIntegral_of_isLat_stable L hL.1 _ fun y hy => (hs _).mpr ?_
    rw [← mul_assoc, Units.mul_inv, one_mul]
    exact hy

end GlobalTheory.UnitLemma.OrbitFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMul
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.FibSum

theorem fib_card (K : UQ) (B₁ B₂ : InvAlg K) (hg₁ : B₁.σ B₁.g = B₁.g) (hg₂ : B₂.σ B₂.g = B₂.g)
    (hres : resultant B₁.P B₂.P ≠ 0)
    (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A) (h₁ : M₁ ∈ B₁.Lin) (h₂ : M₂ ∈ B₂.Lin) :
    (Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ) =
      (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) := by
  have hI := _root_.GlobalTheory.StableLatCount.card_stable_lattices K.O K.E B₁.A B₂.A B₁.g B₂.g hres M₁ M₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  have hH := _root_.GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq K B₁ B₂ hg₁ hg₂ M₁ M₂ h₁ h₂
  have e : {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ≃
      {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} :=
    { toFun := fun M => ⟨M.1, ⟨M.2.1.2.1, M.2.1.2.2⟩, M.2.2⟩
      invFun := fun M => ⟨M.1, ⟨GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd K B₁ B₂ M.1 (by rw [M.2.2.1]; exact h₁.1)
          (by rw [M.2.2.2]; exact h₂.1), M.2.1.1, M.2.1.2⟩, M.2.2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e]
  have hq2 : (Nat.card (IsLocalRing.ResidueField K.O) : ℚ) = (K.q : ℚ) ^ 2 := by
    rw [K.card_res]; push_cast; ring
  rw [hq2] at hI
  have hqpos : (0 : ℚ) < K.q := by
    have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
    rw [K.card_res] at this
    exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
  have hsq : ((Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ)) ^ 2 =
      ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
    have hpw : ((K.q : ℚ) ^ 2) ^ val K.O (resultant B₁.P B₂.P) = ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hP₁ : (LinearMap.mulLeft K.E B₁.g).charpoly = B₁.P := rfl
    have hP₂ : (LinearMap.mulLeft K.E B₂.g).charpoly = B₂.P := rfl
    rw [hP₁, hP₂, hpw] at hI
    rw [← hI]
    exact_mod_cast hH
  exact (pow_left_inj₀ (by positivity) (zpow_pos hqpos _).le two_ne_zero).1 hsq

theorem fibsum : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  intro K B₁ B₂ hg₁ hg₂ hsep φ₁ φ₂ hf₁ hf₂
  have hres : resultant B₁.P B₂.P ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
  set v := val K.O (resultant B₁.P B₂.P) with hv
  set π : Submodule K.O (B₁.prod B₂).A → Submodule K.O B₁.A × Submodule K.O B₂.A := fun M =>
    (M.comap (LinearMap.inl K.O B₁.A B₂.A), M.map (LinearMap.snd K.O B₁.A B₂.A)) with hπ
  suffices key : ∀ F : Submodule K.O (B₁.prod B₂).A → ℚ, (∀ M, F M =
      φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A))) →
      {M | M ∈ (B₁.prod B₂).Lin ∧ F M ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M =
        (K.q : ℚ) ^ v * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) from key _ (fun _ => rfl)
  intro F hF
  set s₁ := hf₁.toFinset
  set s₂ := hf₂.toFinset
  have hs₁ : ∀ M, M ∈ s₁ ↔ M ∈ B₁.Lin ∧ φ₁ M ≠ 0 := fun M => by simp [s₁]
  have hs₂ : ∀ M, M ∈ s₂ ↔ M ∈ B₂.Lin ∧ φ₂ M ≠ 0 := fun M => by simp [s₂]
  have hfibfin : ∀ p ∈ s₁ ×ˢ s₂, {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p}.Finite := by
    intro p hp
    rw [Finset.mem_product, hs₁, hs₂] at hp
    have hc := fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp.1.1 hp.2.1
    have hqpos : (0 : ℚ) < K.q := by
      have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
      rw [K.card_res] at this
      exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
    have hne : Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact (zpow_pos hqpos v).ne' (by simpa using hc.symm)
    have := Nat.finite_of_card_ne_zero hne
    refine (Set.finite_coe_iff.1 ?_)
    have e : {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p} = {M | M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} := by
      ext M; simp only [Set.mem_setOf_eq, hπ, Prod.ext_iff]
    rw [e]; exact this
  set W := {M | M ∈ (B₁.prod B₂).Lin ∧ π M ∈ s₁ ×ˢ s₂} with hW
  have hWfin : W.Finite := by
    refine (Set.Finite.biUnion (t := fun p => {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p})
      (s₁ ×ˢ s₂).finite_toSet hfibfin).subset ?_
    intro M hM
    exact Set.mem_biUnion (x := π M) hM.2 (show M ∈ {M' | M' ∈ (B₁.prod B₂).Lin ∧ π M' = π M} from ⟨hM.1, rfl⟩)
  have hsupp : ∀ M ∈ (B₁.prod B₂).Lin, F M ≠ 0 → M ∈ W := by
    intro M hM hFM
    have hl := _root_.GlobalTheory.UnitLemma.InvAlg.lin_fst_snd K B₁ B₂ M hM
    rw [hF M] at hFM
    refine ⟨hM, Finset.mem_product.2 ⟨(hs₁ _).2 ⟨hl.1, left_ne_zero_of_mul hFM⟩,
      (hs₂ _).2 ⟨hl.2, right_ne_zero_of_mul hFM⟩⟩⟩
  refine ⟨hWfin.subset fun M hM => hsupp M hM.1 hM.2, ?_⟩
  have hL : ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M = ∑ M ∈ hWfin.toFinset, F M := by
    have hset : (B₁.prod B₂).Lin ∩ Function.support F = W ∩ Function.support F := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun h => ⟨hsupp M h.1 h.2, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hWfin, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := W), hset]
  have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ M = ∑ M ∈ s₁, φ₁ M := by
    have hset : B₁.Lin ∩ Function.support φ₁ = {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0} ∩ Function.support φ₁ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₁, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0}), hset]
  have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ M = ∑ M ∈ s₂, φ₂ M := by
    have hset : B₂.Lin ∩ Function.support φ₂ = {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0} ∩ Function.support φ₂ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₂, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0}), hset]
  rw [hL, h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := hWfin.toFinset) (t := s₁ ×ˢ s₂) (g := π)
    (fun M hM => ((Set.Finite.mem_toFinset hWfin).1 hM).2), Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hin : ∀ M ∈ hWfin.toFinset.filter (fun M => π M = p), F M = φ₁ p.1 * φ₂ p.2 := by
    intro M hM
    have hM' := (Finset.mem_filter.1 hM).2
    rw [hF, ← hM']
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hp' := hp
  rw [Finset.mem_product, hs₁, hs₂] at hp'
  rw [← fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp'.1.1 hp'.2.1]
  congr 1
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro M
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hW, hπ, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨h, ?_⟩, h'⟩
    rw [Finset.mem_product]; rw [h'.1, h'.2]; exact Finset.mem_product.1 hp

end GlobalTheory.UnitLemma.FibSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoBadWindowDivRho
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc


open Classical in
noncomputable def badWinBox {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) : Finset ℤ :=
  if i ∈ S then (if i ∈ I then Finset.Icc (2 * (k : ℤ) - L) (2 * k + L) else Finset.Icc (-(L : ℤ)) L)
  else if i = i₀ then Finset.Ico (-(L : ℤ)) L ∪ Finset.Ioc (2 * (k : ℤ) - L) (2 * k + L)
  else Finset.Icc (-(L : ℤ)) (2 * k + L)

open Classical in
theorem card_badWinBox_le {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) :
    (badWinBox S I L k i₀ i).card ≤
      2 * (2 * L + 1) * (if i ∈ insert i₀ S then 1 else k + 1) := by
  unfold badWinBox
  by_cases hS : i ∈ S
  · have : i ∈ insert i₀ S := Finset.mem_insert_of_mem hS
    rw [if_pos hS, if_pos this]
    split_ifs <;> simp [Int.card_Icc] <;> omega
  · rw [if_neg hS]
    by_cases h0 : i = i₀
    · subst h0
      rw [if_pos rfl, if_pos (Finset.mem_insert_self _ _)]
      refine (Finset.card_union_le _ _).trans ?_
      simp [Int.card_Ico, Int.card_Ioc]; omega
    · rw [if_neg h0, if_neg (by simp [h0, hS])]
      simp [Int.card_Icc]
      nlinarith

open Classical in
theorem card_piFinset_badWinBox_le {ι : Type} [Fintype ι] (S I : Finset ι) (L k : ℕ) (i₀ : ι) (h₀ : i₀ ∉ S) :
    (Fintype.piFinset (badWinBox S I L k i₀)).card ≤
      (2 * (2 * L + 1)) ^ Fintype.card ι * (k + 1) ^ (Fintype.card ι - S.card - 1) := by
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun i _ => card_badWinBox_le S I L k i₀ i).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_ite, Finset.prod_const_one,
    one_mul, Finset.prod_const]
  have : (Finset.univ.filter fun i => i ∉ insert i₀ S).card = Fintype.card ι - S.card - 1 := by
    have h : (Finset.univ.filter fun i => i ∉ insert i₀ S) = (insert i₀ S)ᶜ := by ext; simp
    rw [h, Finset.card_compl, Finset.card_insert_of_notMem h₀]; omega
  rw [this]

end GlobalTheory.UnitLemma.Desc

namespace GlobalTheory.UnitLemma.Desc

theorem tendsto_badWindow_div_rho : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ (I I' : Finset ι), (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N L : ℕ) (D : ℚ) (f : ℕ → Submodule K.O B.A → ℚ), (∀ M ∈ B.Lin, ∃ p, Pos B a e N M p) → (∀ k M, |f k M| ≤ D) → (∀ k, L ≤ k → ∀ M ∈ B.Lin, ∀ p, Pos B a e N M p → f k M ≠ 0 → Win I I' L k p ∧ ¬ Mid S L k p) → Tendsto (fun k : ℕ => ((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 0) := by
  intro K B ι _ e π S a hsep ha hfr I I' hI N L D f hpos hD hsupp
  classical
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le K B ι e π S a hsep ha hfr N
  have hrho := _root_.GlobalTheory.UnitLemma.Desc.rho_lower K B ι e π S a hsep ha hfr
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 ⊥)
  set n := Fintype.card ι
  set m := n - S.card
  set A : ℕ := 2 * (2 * L + 1)
  have key : ∀ k, L ≤ k → |∑ᶠ M ∈ B.Lin, f k M| ≤ D * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℚ) := by
    intro k hk
    let W : Finset (ι → ℤ) :=
      (Finset.univ.filter (· ∉ S)).biUnion fun i₀ => Fintype.piFinset (badWinBox S I L k i₀)
    have hWcard : W.card ≤ m * A ^ n * (k + 1) ^ (m - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      have h1 : ∀ i₀ ∈ Finset.univ.filter (· ∉ S),
          (Fintype.piFinset (badWinBox S I L k i₀)).card ≤ A ^ n * (k + 1) ^ (m - 1) := by
        intro i₀ hi₀
        exact card_piFinset_badWinBox_le S I L k i₀ (Finset.mem_filter.1 hi₀).2
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, smul_eq_mul]
      have h2 : (Finset.univ.filter (· ∉ S)).card = m := by
        have h : (Finset.univ.filter (· ∉ S)) = Sᶜ := by ext; simp
        rw [h, Finset.card_compl]
      rw [h2, mul_assoc]
    have hmem : ∀ M ∈ B.Lin, f k M ≠ 0 → ∃ p ∈ W, Pos B a e N M p := by
      intro M hM hf
      obtain ⟨p, hp⟩ := hpos M hM
      obtain ⟨hw, hmid⟩ := hsupp k hk M hM p hp hf
      refine ⟨p, ?_, hp⟩
      simp only [W, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      unfold Mid at hmid
      push_neg at hmid
      obtain ⟨i₀, hi₀, h₀⟩ := hmid
      refine ⟨i₀, hi₀, fun i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := hw i
      unfold badWinBox
      by_cases hS : i ∈ S
      · rw [if_pos hS]
        by_cases hiI : i ∈ I
        · rw [if_pos hiI]; simp only [Finset.mem_Icc]; exact ⟨h3 hiI, h2⟩
        · rw [if_neg hiI]
          have := (hI i hS).resolve_left hiI
          simp only [Finset.mem_Icc]; exact ⟨h1, h4 this⟩
      · rw [if_neg hS]
        by_cases h0 : i = i₀
        · subst h0
          rw [if_pos rfl]
          simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
          by_cases hl : (L : ℤ) ≤ p i
          · exact Or.inr ⟨h₀ hl, h2⟩
          · exact Or.inl ⟨h1, lt_of_not_ge hl⟩
        · rw [if_neg h0]; simp only [Finset.mem_Icc]; exact ⟨h1, h2⟩
    let T : Finset (Submodule K.O B.A) := W.biUnion fun p => (hC p).1.toFinset
    have hTcard : T.card ≤ W.card * C := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun p _ => ?_).trans (by rw [Finset.sum_const, smul_eq_mul])
      rw [← Set.ncard_eq_toFinset_card _ (hC p).1]
      exact (hC p).2
    have hfs : ∑ᶠ M ∈ B.Lin, f k M = ∑ M ∈ T.filter (· ∈ B.Lin), f k M := by
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hM, hf⟩
        refine ⟨⟨?_, hM⟩, hf⟩
        obtain ⟨p, hpW, hp⟩ := hmem M hM hf
        simp only [T, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact ⟨p, hpW, hp⟩
      · rintro ⟨⟨_, hM⟩, hf⟩
        exact ⟨hM, hf⟩
    rw [hfs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun M _ => hD k M).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have : (T.filter (· ∈ B.Lin)).card ≤ m * A ^ n * (k + 1) ^ (m - 1) * C :=
      (Finset.card_filter_le _ _).trans (hTcard.trans (Nat.mul_le_mul_right _ hWcard))
    exact_mod_cast this
  have hm : ∀ k : ℕ, m * (k + 1) ^ (m - 1) * (k + 1) = m * (k + 1) ^ m := by
    intro k
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel h]
  set c : ℝ := (D : ℝ) * (A : ℝ) ^ n * (m : ℝ) * (C : ℝ)
  have hlim : Tendsto (fun k : ℕ => c * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop L] with k hk
  have hr : ((k + 1 : ℕ) : ℝ) ^ m ≤ (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by exact_mod_cast hrho k
  have hpos' : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hk' := key k hk
  have hk'' : |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)| ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hk'
    push_cast at this ⊢
    simpa [Rat.cast_abs] using this
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos' hr)]
  calc |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)|
      ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := hk''
    _ = c * (1 / ((k : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ m := by
        have h := congrArg (fun x : ℕ => (x : ℝ)) (hm k)
        push_cast at h ⊢
        field_simp
        simp only [c]
        linear_combination (D : ℝ) * (A : ℝ) ^ n * (C : ℝ) * h
    _ ≤ c * (1 / ((k : ℝ) + 1)) * (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by
        refine mul_le_mul_of_nonneg_left hr ?_
        simp only [c]; positivity

end GlobalTheory.UnitLemma.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1Eq
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

theorem transfer_card_H0_H1 : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  intro O _ G G' _ _ _ _ i M _ _ ρ p r _ c h
  letI := levZ (M := M) p r h

  have hact : ∀ (g' : G') (x : Lev M c),
      levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = levRep ρ c (i.symm g') x :=
    fun g' x => rfl
  constructor
  · apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro x
    show (∀ g, levRep ρ c g x = x) ↔ ∀ g', levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom) g' x = x
    constructor
    · intro hx g'; rw [hact]; exact hx _
    · intro hx g
      have := hx (i g)
      rw [hact, ContinuousMulEquiv.symm_apply_apply] at this
      exact this
  · apply Nat.card_congr
    let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
    have hs : Continuous (i.symm : G' → G) := i.symm.continuous
    have hi : Continuous (i : G → G') := i.continuous
    let e : Z1 (levRep ρ c) ≃ Z1 ρ' :=
      { toFun := fun f => ⟨(f : G → Lev M c) ∘ i.symm, f.2.1.comp hs, fun a b => by
          show (f : G → Lev M c) (i.symm (a * b)) = (f : G → Lev M c) (i.symm a) + ρ' a ((f : G → Lev M c) (i.symm b))
          rw [map_mul, f.2.2]; rfl⟩
        invFun := fun f => ⟨(f : G' → Lev M c) ∘ i, f.2.1.comp hi, fun a b => by
          show (f : G' → Lev M c) (i (a * b)) = (f : G' → Lev M c) (i a) + levRep ρ c a ((f : G' → Lev M c) (i b))
          rw [map_mul, f.2.2, hact, ContinuousMulEquiv.symm_apply_apply]⟩
        left_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G → Lev M c) (i.symm (i g)) = _
          rw [ContinuousMulEquiv.symm_apply_apply]
        right_inv := fun f => by
          apply Subtype.ext; funext g; show (f : G' → Lev M c) (i (i.symm g)) = _
          rw [ContinuousMulEquiv.apply_symm_apply] }
    refine Quotient.congr e ?_
    intro a b
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.coe_subtype, Submodule.coe_subtype, mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g' => ?_⟩
      have := hm (i.symm g')
      rw [hact]
      exact this
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (i g)
      rw [hact] at this
      change (a : G → Lev M c) (i.symm (i g)) - (b : G → Lev M c) (i.symm (i g)) = _ at this
      rw [ContinuousMulEquiv.symm_apply_apply] at this
      exact this

end GlobalTheory.ShapeNeg
end
end

