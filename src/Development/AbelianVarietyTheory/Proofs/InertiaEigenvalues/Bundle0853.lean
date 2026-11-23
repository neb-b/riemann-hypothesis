module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0842
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0847

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedParahoricBlockVectorOfIdempotent
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem conv_sum {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (T : G → W →ₗ[ℂ] W) (f : G → W)
    (hT : ∀ g h, T g (f h) = f (g * h)) (a b : MonoidAlgebra ℂ G) :
    (a.coeff.sum fun g c => c • T g (b.coeff.sum fun h d => d • f h)) = (a * b).coeff.sum fun k c => c • f k := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [add_mul, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index', ha, ha']
      <;> intros <;> simp [add_smul]
  | single g c =>
    rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      rw [mul_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add, Finsupp.sum_add_index', Finsupp.sum_add_index',
        map_add (f := _), smul_add, hb, hb'] <;> intros <;> simp [add_smul]
    | single h d =>
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
        Finsupp.sum_single_index, Finsupp.sum_single_index, map_smul, hT, smul_smul] <;> simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}

def ee (r t : ℕ) : Fin r ⊕ Fin t ≃ Fin (r + t) := stdSum (rfl : r + t = r + t)

theorem ee_inl (i : Fin r) : ee r t (Sum.inl i) = Fin.castAdd t i := by ext; simp [ee]

theorem ee_inr (j : Fin t) : ee r t (Sum.inr j) = Fin.natAdd r j := by ext; simp [ee]


variable (F) in
def dg (r t : ℕ) : GL (Fin r) F →* GL (Fin (r + t)) F := (emb₂ F (ee r t)).comp (MonoidHom.inl _ _)


variable (F) in
def bl (r t : ℕ) : GL (Fin (r + t)) F →* GL (Fin r ⊕ Fin t) F := reix F (ee r t).symm

theorem bl_apply (g : GL (Fin (r + t)) F) (a b : Fin r ⊕ Fin t) : (bl F r t g).val a b = g.val (ee r t a) (ee r t b) := by
  rw [bl, val_reix, Equiv.symm_symm]

theorem eq_of_bl {g g' : GL (Fin (r + t)) F} (H : (bl F r t g).val = (bl F r t g').val) : g = g' := by
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun H a) b
  rwa [bl_apply, bl_apply] at this

theorem dg_bl (A : GL (Fin r) F) : (bl F r t (dg F r t A)).val = fromBlocks A.val 0 0 1 := by
  ext a b
  rw [bl_apply]
  have := val_emb₂ F (ee r t) (A, 1)
  simp only [dg, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [this, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem bl_21 (g : GL (Fin (r + t)) F) (i : Fin t) (j : Fin r) :
    (bl F r t g).val.toBlocks₂₁ i j = g.val (Fin.natAdd r i) (Fin.castAdd t j) := by
  simp only [toBlocks₂₁, of_apply, bl_apply, ee_inr, ee_inl]

theorem bl_11 (g : GL (Fin (r + t)) F) (i j : Fin r) :
    (bl F r t g).val.toBlocks₁₁ i j = g.val (Fin.castAdd t i) (Fin.castAdd t j) := by
  simp only [toBlocks₁₁, of_apply, bl_apply, ee_inl]

theorem bl_22 (g : GL (Fin (r + t)) F) :
    (bl F r t g).val.toBlocks₂₂ = g.val.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  simp only [toBlocks₂₂, of_apply, bl_apply, ee_inr, submatrix_apply]

theorem intM_dg {A : GL (Fin r) F} (hA : IntM A.val) : IntM (dg F r t A).val := by
  intro a b
  obtain ⟨a, rfl⟩ := (ee r t).surjective a
  obtain ⟨b, rfl⟩ := (ee r t).surjective b
  have := congrFun (congrFun (dg_bl (t := t) A) a) b
  rw [bl_apply] at this
  rw [this]
  exact intM_fromBlocks.2 ⟨hA, intM_zero, intM_zero, intM_one⟩ a b

theorem dg_mem_KO {A : GL (Fin r) F} (hA : A ∈ KO F (Fin r)) : dg F r t A ∈ KO F (Fin (r + t)) :=
  GlobalTheory.StepData.mem_KO.2 ⟨intM_dg (GlobalTheory.StepData.mem_KO.1 hA).1,
    by rw [← map_inv]; exact intM_dg (GlobalTheory.StepData.mem_KO.1 hA).2⟩

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r t : ℕ}
  {χ : Fˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin (r + t)) F) W}

theorem isBlockVec_add {v w : W} (hv : IsBlockVec χ π v) (hw : IsBlockVec χ π w) : IsBlockVec χ π (v + w) :=
  fun h hh h1 h2 u hu => by rw [map_add (f := _), hv h hh h1 h2 u hu, hw h hh h1 h2 u hu, smul_add]

theorem isBlockVec_smul (c : ℂ) {v : W} (hv : IsBlockVec χ π v) : IsBlockVec χ π (c • v) :=
  fun h hh h1 h2 u hu => by rw [map_smul, hv h hh h1 h2 u hu, smul_comm]

theorem isBlockVec_zero : IsBlockVec χ π (0 : W) := fun _ _ _ _ _ _ => by simp

theorem dg_fix {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KOne F (Fin r)) :
    π (dg F r t κ) v = v := by
  have key := hv _ (dg_mem_KO (GlobalTheory.StepData.KOne_le_KO hκ))
    (fun i j => by rw [← bl_21, dg_bl, toBlocks_fromBlocks₂₁]; simp)
    (fun i j => by
      rw [← bl_11, dg_bl, toBlocks_fromBlocks₁₁]
      have := (GlobalTheory.StepData.mem_KOne.1 hκ) i j
      rwa [Matrix.sub_apply, Matrix.one_apply] at this)
    1 (by rw [← bl_22, dg_bl, toBlocks_fromBlocks₂₂, det_one, Units.val_one])
  rw [key, map_one, Units.val_one, one_smul]

theorem dg_isBlockVec {v : W} (hv : IsBlockVec χ π v) {κ : GL (Fin r) F} (hκ : κ ∈ KO F (Fin r)) :
    IsBlockVec χ π (π (dg F r t κ) v) := by
  intro h hh h1 h2 u hu
  have hd := dg_mem_KO (t := t) hκ
  have hK : (dg F r t κ)⁻¹ * h * dg F r t κ ∈ KO F (Fin (r + t)) := mul_mem (mul_mem (inv_mem hd) hh) hd
  obtain ⟨A, B, C, D, hE⟩ : ∃ A B C D, (bl F r t h).val = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hΦ : (bl F r t ((dg F r t κ)⁻¹ * h * dg F r t κ)).val =
      fromBlocks ((κ⁻¹).val * A * κ.val) ((κ⁻¹).val * B) (C * κ.val) D := by
    rw [← map_inv (dg F r t) κ, map_mul, map_mul, Units.val_mul, Units.val_mul, dg_bl, dg_bl, hE,
      fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_assoc]
  have hC : MaxM C := fun i j => by
    rw [show C i j = h.val (Fin.natAdd r i) (Fin.castAdd t j) by rw [← bl_21, hE, toBlocks_fromBlocks₂₁]]
    exact h1 i j
  have hA : MaxM (A - 1) := fun i j => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    rw [show A i j = h.val (Fin.castAdd t i) (Fin.castAdd t j) by rw [← bl_11, hE, toBlocks_fromBlocks₁₁]]
    exact h2 i j
  have key := hv _ hK
    (fun i j => by rw [← bl_21, hΦ, toBlocks_fromBlocks₂₁]; exact hC.mul_intM (intM_of_mem_KO hκ) i j)
    (fun i j => by
      rw [← bl_11, hΦ, toBlocks_fromBlocks₁₁]
      have e : (κ⁻¹).val * A * κ.val - 1 = (κ⁻¹).val * (A - 1) * κ.val := by
        rw [mul_sub, sub_mul, mul_one, Units.inv_mul]
      have := ((((GlobalTheory.StepData.mem_KO.1 hκ).2).mul_maxM hA).mul_intM (intM_of_mem_KO hκ)) i j
      rw [← e, Matrix.sub_apply, Matrix.one_apply] at this
      exact this)
    u (by
      rw [← bl_22, hΦ, toBlocks_fromBlocks₂₂]
      rw [← bl_22, hE, toBlocks_fromBlocks₂₂] at hu
      exact hu)
  have hh' : h * dg F r t κ = dg F r t κ * ((dg F r t κ)⁻¹ * h * dg F r t κ) := by group
  calc π h (π (dg F r t κ) v) = π (dg F r t κ) (π ((dg F r t κ)⁻¹ * h * dg F r t κ) v) := by
        rw [← Module.End.mul_apply, ← map_mul, hh', map_mul, Module.End.mul_apply]
    _ = (χ u : ℂ) • π (dg F r t κ) v := by rw [key, map_smul]

theorem exists_of_isLiftN {p : ℕ} {g : GL (Fin r) (ZMod p)} {h : GL (Fin (r + t)) F} (H : IsLiftN g h) :
    ∃ A : GL (Fin r) F, dg F r t A = h ∧ IsLift g A := by
  set M : Matrix (Fin r) (Fin r) F := fun i j => h.val (Fin.castAdd t i) (Fin.castAdd t j) with hM
  have hΦ : (bl F r t h).val = fromBlocks M 0 0 1 := by
    ext (a | a) (b | b)
    · rw [bl_apply, ee_inl, ee_inl, fromBlocks_apply₁₁]
    · have := H (Fin.castAdd t a) (Fin.natAdd r b)
      rw [dite_eq_right (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.castAdd t a ≠ Fin.natAdd r b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.castAdd t b)
      rw [dite_eq_right (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      have hne : Fin.natAdd r a ≠ Fin.castAdd t b := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      simp [bl_apply, ee_inl, ee_inr, this, hne]
    · have := H (Fin.natAdd r a) (Fin.natAdd r b)
      rw [dite_eq_right (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)] at this
      simp [bl_apply, ee_inr, this, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (bl F r t h).val.det := (Matrix.isUnit_iff_isUnit_det _).1 (bl F r t h).isUnit
    rwa [hΦ, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one] at h1
  refine ⟨Matrix.nonsingInvUnit M hdet, eq_of_bl ?_, fun a b => ?_⟩
  · rw [dg_bl, hΦ]; rfl
  · have := H (Fin.castAdd t a) (Fin.castAdd t b)
    rw [dite_eq_left (show ((Fin.castAdd t a : Fin (r + t)) : ℕ) < r ∧ ((Fin.castAdd t b : Fin (r + t)) : ℕ) < r
      from ⟨a.isLt, b.isLt⟩)] at this
    exact this

end GlobalTheory.BlockIdem

namespace GlobalTheory.BlockIdem

open ValuativeRel Matrix GlobalTheory.StepData

theorem exists_fixed_blockVec : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (x : W), resCard F = p → z * z = z → IsBlockVec χ π x → NotKilled π z x → ∃ y : W, y ≠ 0 ∧ IsBlockVec χ π y ∧ ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y := by
  intro F _ _ _ _ p _ r t χ W _ _ π z x hp hz hx hnk
  obtain ⟨ℓ', hℓ', hne⟩ := hnk
  have hA : ∀ g, ∃ A : GL (Fin r) F, dg F r t A = ℓ' g ∧ IsLift g A := fun g => exists_of_isLiftN (hℓ' g)
  choose ℓ hℓ1 hℓ2 using hA
  have hx1 : ∀ h ∈ KOne F (Fin r), (π.comp (dg F r t)) h x = x := fun h hh => dg_fix hx hh
  have hT : ∀ g h, π (dg F r t (ℓ g)) (π (dg F r t (ℓ h)) x) = π (dg F r t (ℓ (g * h))) x := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    exact IsLift.apply_eq hp (π := π.comp (dg F r t)) hx1 ((hℓ2 g).mul hp (hℓ2 h)) (hℓ2 (g * h))
  refine ⟨z.coeff.sum fun g c => c • π (dg F r t (ℓ g)) x, ?_, ?_, ℓ, hℓ2, ?_⟩
  · simpa only [hℓ1] using hne
  · rw [Finsupp.sum]
    exact Finset.sum_induction _ _ (fun a b => isBlockVec_add) isBlockVec_zero
      (fun g _ => isBlockVec_smul _ (dg_isBlockVec hx ((hℓ2 g).mem_KO hp)))
  · have := conv_sum (fun g => π (dg F r t (ℓ g))) (fun h => π (dg F r t (ℓ h)) x) hT z z
    rw [hz] at this
    exact this

end GlobalTheory.BlockIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalIntegerCongrTameGeneratorCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChiTameUnit

theorem exists_int_cong_tg : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal ∧ ∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 := by
  intro D k v
  set w := D.naut.plGw k v with hw
  set A := D.nd.plOm.1 w with hAdef
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hp : (D.host.g k).Prime := D.host.g_prime k
  have hN : normV w = D.host.g k := GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split k) (D.naut.plGw_over k v)
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := D.naut.plGw_over k v
  have hn : 0 < normV w - 1 := by rw [hN]; have := hp.two_le; omega
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
    (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E)) hn
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  set ζ := D.ntypes.tg k v π / π with hζ
  have hζn : ζ ^ (normV w - 1) = 1 := by
    rw [hζ, div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ h0)]
  have hv1 : A.valuation ζ = 1 := by
    have heq : (A.valuation ζ) ^ (normV w - 1) = (1 : A.ValueGroup) ^ (normV w - 1) := by
      rw [← map_pow, hζn, map_one, one_pow]
    exact pow_left_injective hn.ne' heq

  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp hv1.le
  haveI hcp : CharP (IsLocalRing.ResidueField A) (D.host.g k) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    have := (hA _).mpr hgw
    simpa using this
  haveI : Fact (D.host.g k).Prime := ⟨hp⟩
  set z := IsLocalRing.residue A ⟨ζ, hζA⟩ with hz
  have hzp : z ^ (D.host.g k) - z = 0 := by
    have e : (⟨ζ, hζA⟩ : A) ^ (normV w - 1) = 1 := Subtype.ext (by simpa using hζn)
    have e2 : z ^ (normV w - 1) = 1 := by rw [hz, ← map_pow, e, map_one]
    rw [hN] at e2
    have : z ^ (D.host.g k) = z := by
      rw [← Nat.sub_add_cancel hp.one_lt.le, pow_succ, e2, one_mul]
    rw [this, sub_self]
  have hmon : (X ^ (D.host.g k) - X : (ZMod (D.host.g k))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.one_lt)
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod (D.host.g k))
  rw [ZMod.card] at hroots
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, Polynomial.natDegree_X_pow_sub_X hp.one_lt, Finset.card_val, Finset.card_univ,
      ZMod.card])
  have hev := congrArg (fun P => (P.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField A))).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, Multiset.map_map, eval_sub, eval_X, eval_C, eval_pow, hzp] at hev
  obtain ⟨a, -, hy0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)

  have hcong : A.valuation (ζ - ((a.val : ℕ) : D.nd.Om)) < 1 := by
    have : (⟨ζ, hζA⟩ : A) - ((a.val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hz, map_natCast, ZMod.natCast_val]
      simpa using hy0
    rw [ValuationSubring.valuation_lt_one_iff] at this
    simpa [-ZMod.natCast_val] using this
  have hu : ((a.val : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hm
    have h3 := (hA _).mpr hm
    simp only [map_natCast] at h3
    have h4 := Valuation.map_add_lt _ hcong h3
    rw [sub_add_cancel, hv1] at h4
    exact lt_irrefl _ h4
  refine ⟨((a.val : ℕ) : 𝓞 D.host.E), ?_, hu, ϖ, π, h1, h2, hπ, ?_⟩
  · intro h
    apply hu
    have : ((a.val : ℕ) : 𝓞 D.host.E) = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  · have e : algebraMap D.host.E D.nd.Om (((a.val : ℕ) : 𝓞 D.host.E) : D.host.E) = ((a.val : ℕ) : D.nd.Om) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_natCast]
    rw [e]
    exact hcong

end GlobalTheory.ChiTameUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleDetTwistOfStdTraceTwoBlock
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType.RestrictionTwo

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdBlock_iff (a : ℕ) (y : Gn p (a + 1)) :
    StdBlock a y ↔ InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = 1 := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · rw [h i j (by omega)]
      have : i ≠ j := fun e => by rw [e] at hi; omega
      simp [this]
    · ext i j
      have hi : (i : ℕ) < a + 1 := by omega
      have hj : (j : ℕ) < a + 1 := by omega
      have := h ⟨i, hi⟩ ⟨j, hj⟩ (by first | omega | simp | (simp; omega))
      simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this ⊢
      exact this
  · rintro ⟨h1, h2⟩ i j hij
    have hj : (j : ℕ) < a := by omega
    by_cases hi : (i : ℕ) < a
    · have := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
      have hi' : (i : ℕ) < a + 1 := by omega
      have hj' : (j : ℕ) < a + 1 := by omega
      simp only [tl, entN, hi', hj', and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this
      simp only [Fin.ext_iff]
      exact this
    · have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rw [if_neg hne]
      exact h1 i j hj (by omega)

theorem det_eq_of_stdBlock (a : ℕ) (y : Gn p (a + 1)) (h : StdBlock a y) :
    Matrix.GeneralLinearGroup.det y = Matrix.GeneralLinearGroup.det (toG (br a 1 (y : Mt p (a + 1)))) := by
  obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 h
  rw [GlobalTheory.GLq.LabelDet.det_par a 1 y h1, h2, GlobalTheory.GLq.LabelDet.toG_one, map_one, one_mul]

theorem br_eq_iff (a : ℕ) (y : Gn p (a + 1)) (h : InPar a (y : Mt p (a + 1))) (x : Gn p 1) :
    br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) ↔ x = toG (br a 1 (y : Mt p (a + 1))) := by
  have hd := GlobalTheory.GLq.LabelDet.det_inPar a 1 _ h
  have h0 : (tl a (y : Mt p (a + 1))).det * (br a 1 (y : Mt p (a + 1))).det ≠ 0 := hd ▸ y.det_ne_zero
  have hu : IsUnit (br a 1 (y : Mt p (a + 1))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (right_ne_zero_of_mul h0))
  have hv : ((toG (br a 1 (y : Mt p (a + 1))) : Gn p 1) : Mt p 1) = br a 1 (y : Mt p (a + 1)) := by
    unfold toG; rw [dif_pos hu]; exact IsUnit.unit_spec hu
  constructor
  · intro e; apply Units.ext; rw [hv, e]
  · intro e; rw [e, hv]

theorem sum_res_eq (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : Gn p (a + 1) → ℂ) :
    ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x =
      ((p : ℂ) ^ a)⁻¹ * stdTrace a θ α := by
  rw [stdTrace, Finset.mul_sum]
  unfold res
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hs : StdBlock a y
  · obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 hs
    rw [if_pos hs]
    have e : ∀ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * (((p : ℂ) ^ (a * 1))⁻¹ *
        if InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = ((1 : Gn p a) : Mt p a) ∧
          br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) then α y else 0) =
        if x = toG (br a 1 (y : Mt p (a + 1))) then
          ((p : ℂ) ^ a)⁻¹ * ((((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * α y) else 0 := by
      intro x
      by_cases hx : x = toG (br a 1 (y : Mt p (a + 1)))
      · rw [if_pos ⟨h1, by rw [h2, Units.val_one], (br_eq_iff a y h1 x).2 hx⟩, if_pos hx, det_eq_of_stdBlock a y hs, ← hx,
          MonoidHom.inv_apply, Nat.mul_one]
        ring
      · rw [if_neg (fun h => hx ((br_eq_iff a y h1 x).1 h.2.2)), if_neg hx, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_ite_eq']
    simp
  · rw [if_neg hs, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg, mul_zero, mul_zero]
    rintro ⟨h1, h2, -⟩
    exact hs ((stdBlock_iff a y).2 ⟨h1, by rw [h2, Units.val_one]⟩)

theorem exists_irr_hc_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ)
    (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 →
    ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ
      (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  intro p _ a θ α hα hne
  have key : ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x ≠ 0 := by
    rw [sum_res_eq]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))) hne
  obtain ⟨σ, hσ, h⟩ := (GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv p a α hα θ⁻¹).1 key
  exact ⟨σ, hσ, by simpa only [inv_inv] using h⟩

end GlobalTheory.LevelType.RestrictionTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCellStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_nat_bump_rankinSelbergCell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  first | exact @GlobalTheory.RSParams.exists_level_nat_bump | exact GlobalTheory.RSParams.exists_level_nat_bump | (intros; apply GlobalTheory.RSParams.exists_level_nat_bump <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  first | (exact @GlobalTheory.ZEulLocal.localTerm_eq) | (exact GlobalTheory.ZEulLocal.localTerm_eq) | (intros; apply GlobalTheory.ZEulLocal.localTerm_eq  <;> assumption)
end

