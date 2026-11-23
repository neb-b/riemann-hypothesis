module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0001
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0504

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomExtLocalization
section
open IsLocalRing

namespace GlobalTheory.IndEtaleHensel

theorem algHom_ext_localization {R A P : Type} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] (q : Ideal A) [q.IsPrime]
    (φ₁ φ₂ : Localization.AtPrime q →ₐ[R] P)
    (h : φ₁.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)) =
      φ₂.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))) : φ₁ = φ₂ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext q.primeCompl
  exact RingHom.ext fun a => DFunLike.congr_fun h a

theorem bijective_of_algEquiv {R X Y T : Type} [CommRing R] [CommRing X] [CommRing Y] [CommRing T]
    [Algebra R X] [Algebra R Y] [Algebra R T] [IsLocalRing T] (e : X ≃ₐ[R] Y)
    (h : Function.Bijective
      (fun φ : X →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective
      (fun φ : Y →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  constructor
  · intro φ₁ φ₂ hφ
    have hc : φ₁.comp (e : X →ₐ[R] Y) = φ₂.comp (e : X →ₐ[R] Y) := by
      apply h.1
      simp only at hφ ⊢
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
    ext y
    have := DFunLike.congr_fun hc (e.symm y)
    simpa using this
  · intro ψ
    obtain ⟨φ, hφ⟩ := h.2 (ψ.comp (e : X →ₐ[R] Y))
    refine ⟨φ.comp (e.symm : Y →ₐ[R] X), ?_⟩
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, hφ]
    ext y; simp

theorem bijective_localization {R A T : Type} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [IsLocalRing T] (q : Ideal A) [q.IsPrime]
    (hA : Function.Bijective
      (fun φ : A →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective (fun φ : Localization.AtPrime q →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  set π := IsScalarTower.toAlgHom R T (ResidueField T)
  set ι := IsScalarTower.toAlgHom R A (Localization.AtPrime q)
  constructor
  · intro φ₁ φ₂ hφ
    apply algHom_ext_localization q
    apply hA.1
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
  · intro ψ
    obtain ⟨φ, hφ⟩ := hA.2 (ψ.comp ι)
    simp only at hφ
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
      intro y
      have h1 : IsUnit (ψ (algebraMap A (Localization.AtPrime q) y)) :=
        (IsLocalization.map_units (Localization.AtPrime q) y).map ψ
      have h2 : π (φ y) = ψ (algebraMap A (Localization.AtPrime q) y) := DFunLike.congr_fun hφ (y : A)
      rw [← h2] at h1
      have h3 : π (φ y) = residue T (φ y) := by
        simp [π, IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq]
      rw [h3] at h1
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1.ne_zero
    refine ⟨IsLocalization.liftAlgHom (M := q.primeCompl) (S := Localization.AtPrime q) hu, ?_⟩
    apply algHom_ext_localization q
    ext a
    have := DFunLike.congr_fun hφ a
    simp only [AlgHom.comp_apply] at this ⊢
    rw [← this]
    congr 1
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

theorem bijective_residue_comp : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [HenselianLocalRing T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → Function.Bijective (fun φ : S →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  intro R S T _ _ _ _ _ _ hS
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := hS
  have hbij : ∀ i, Function.Bijective (fun φ : Si i →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    exact bijective_of_algEquiv e (bijective_localization q (_root_.GlobalTheory.EtaleHensel.bijective_residue_comp R A T))
  have dir : Directed (· ≤ ·) Si := hmono.directed_le
  have htop : (⊤ : Subalgebra R S) ≤ iSup Si := fun s _ => by
    obtain ⟨i, hi⟩ := hcov s
    exact le_iSup Si i hi
  constructor
  · intro φ₁ φ₂ h
    simp only at h
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have hc : φ₁.comp (Si i).val = φ₂.comp (Si i).val := by
      apply (hbij i).1
      simp only
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]
    exact DFunLike.congr_fun hc ⟨s, hi⟩
  · intro ψ
    choose f hf using fun i => (hbij i).2 (ψ.comp (Si i).val)
    simp only at hf
    have compat : ∀ i j (h : Si i ≤ Si j), f i = (f j).comp (Subalgebra.inclusion h) := by
      intro i j h
      apply (hbij i).1
      simp only
      rw [hf i, ← AlgHom.comp_assoc, hf j]
      ext x; rfl
    refine ⟨(Subalgebra.iSupLift Si dir f compat ⊤ htop).comp
      (Subalgebra.topEquiv.symm : S ≃ₐ[R] (⊤ : Subalgebra R S)).toAlgHom, ?_⟩
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have h1 := DFunLike.congr_fun (hf i) ⟨s, hi⟩
    simp only [AlgHom.comp_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    congr 1
    exact Subalgebra.iSupLift_of_mem (K := Si) (dir := dir) (f := f) (hf := compat)
      (T := ⊤) (hT := htop) ⟨s, trivial⟩ hi

end GlobalTheory.IndEtaleHensel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadEltIdemCentral
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount.IdemCen

variable (D : D7)

local instance neZeroTypePrime (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def fac (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  if h : kv.1 = k then h.symm ▸ D.ntypes.eSer k (t (h ▸ kv.2)) else 1

variable {D}

theorem fac_self (k : Fin 2) (t : Tup D k) (v : D.nd.PlG k) : fac D k t ⟨k, v⟩ = D.ntypes.eSer k (t v) := by
  simp [fac]

theorem fac_ne (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) (h : kv.1 ≠ k) : fac D k t kv = 1 := by
  simp [fac, h]


open Classical in
theorem prod_fac_coeff (k : Fin 2) (t : Tup D k) (g : G0g D.nd) :
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (fac D k t kv).coeff (g kv) =
      if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
        ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  rw [Fintype.prod_sigma, Fintype.prod_eq_mul_prod_compl k]
  simp only [fac_self]
  have h2 : ∏ k' ∈ ({k}ᶜ : Finset (Fin 2)), ∏ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) =
      if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then 1 else 0 := by
    have e : ∀ k' ∈ ({k}ᶜ : Finset (Fin 2)), ∏ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) =
        if ∀ v : D.nd.PlG k', g ⟨k', v⟩ = 1 then 1 else 0 := by
      intro k' hk'
      have hk : k' ≠ k := by simpa using hk'
      have hv : ∀ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) = if g ⟨k', v⟩ = 1 then 1 else 0 := by
        intro v
        rw [fac_ne k t ⟨k', v⟩ hk, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single_apply]
        by_cases hg : g ⟨k', v⟩ = 1
        · rw [if_pos hg.symm, if_pos hg]
        · rw [if_neg (Ne.symm hg), if_neg hg]
      simp only [hv]
      by_cases hc : ∀ v : D.nd.PlG k', g ⟨k', v⟩ = 1
      · rw [if_pos hc]
        exact Finset.prod_eq_one fun v _ => if_pos (hc v)
      · rw [if_neg hc]
        push_neg at hc
        obtain ⟨v, hv'⟩ := hc
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv')
    rw [Finset.prod_congr rfl e, Finset.prod_boole]
    by_cases hc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1
    · rw [if_pos hc, if_pos]
      intro k' hk' v
      exact hc ⟨k', v⟩ (by simpa using hk')
    · rw [if_neg hc, if_neg]
      intro h
      apply hc
      rintro ⟨k', v⟩ hk
      exact h k' (by simpa using hk) v
  rw [h2]
  split_ifs <;> simp

theorem badElt_eq_sum (k : Fin 2) (S : Finset (Tup D k)) :
    badElt D k S = ∑ t ∈ S, Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t) := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [Formalism.BasicNotions.Examples₂.NZ.tens_coeff, prod_fac_coeff]
  simp only [badElt, MonoidAlgebra.coeff_ofCoeff, Finsupp.equivFunOnFinite_symm_apply_apply]
  split_ifs with hc
  · rfl
  · simp

theorem fac_mul_self (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) :
    fac D k t kv * fac D k t kv = fac D k t kv := by
  rcases kv with ⟨k', v⟩
  by_cases h : k' = k
  · subst h
    rw [fac_self, D.ntypes.eSer_idem]
  · rw [fac_ne k t ⟨k', v⟩ h, one_mul]

theorem fac_central (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) (a) :
    fac D k t kv * a = a * fac D k t kv := by
  rcases kv with ⟨k', v⟩
  by_cases h : k' = k
  · subst h
    rw [fac_self, D.ntypes.eSer_central]
  · rw [fac_ne k t ⟨k', v⟩ h, one_mul, mul_one]

theorem tens_fac_mul_of_ne (k : Fin 2) {t t' : Tup D k} (h : t ≠ t') :
    Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t) * Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t') = 0 := by
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  rw [Formalism.BasicNotions.Examples₂.NZ.tens_mul]
  refine Formalism.BasicNotions.Examples₂.NZ.tens_eq_zero _ ⟨k, v⟩ ?_
  simp only [fac_self]
  exact D.ntypes.eSer_orth k _ _ hv

theorem badElt_idem_central : ∀ (D : D7) (k : Fin 2) (S : Finset (Tup D k)),
    badElt D k S * badElt D k S = badElt D k S ∧ ∀ a, badElt D k S * a = a * badElt D k S := by
  intro D k S
  rw [badElt_eq_sum]
  refine ⟨?_, fun a => ?_⟩
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_eq_single_of_mem t ht fun t' _ hne => tens_fac_mul_of_ne k (Ne.symm hne),
      Formalism.BasicNotions.Examples₂.NZ.tens_mul]
    exact congrArg _ (funext fun kv => fac_mul_self k t kv)
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ =>
      Formalism.BasicNotions.Examples₂.NZ.tens_central _ (fun kv b => fac_central k t kv b) a

end GlobalTheory.BadCount.IdemCen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSumman
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem trace_rho_eq_zero_of_free {K Γ V X : Type} [Field K] [Group Γ] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ)
    [MulAction H X] (hfree : ∀ (h : H) (x : X), h • x = x → h = 1)
    (A : X → Submodule K V) (hA : DirectSum.IsInternal A)
    (hmap : ∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) (h : H) (hne : h ≠ 1) :
    LinearMap.trace K V (ρ h) = 0 := by
  classical
  refine LinearMap.trace_eq_zero_of_mapsTo_ne hA (fun x => h • x) (fun x hx => hne (hfree h x hx)) ?_
  intro x v hv
  exact hmap h x v hv

theorem card_mul_finrank_eig_of_free : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap Hb hle lam
  classical
  haveI : Fintype Hb := Fintype.ofFinite Hb
  set n : K := (Fintype.card Hb : K) with hn
  have hn0 : n ≠ 0 := by simp [hn, Fintype.card_ne_zero]
  let P : Module.End K V := n⁻¹ • ∑ h : Hb, (((lam h)⁻¹ : Kˣ) : K) • ρ h
  have hproj : LinearMap.IsProj (eig ρ Hb lam) P := by
    constructor
    · intro v
      rw [mem_eig]
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
      rw [smul_comm]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul, mul_inv, Units.val_mul]
      congr 1
      simp only [← Units.val_mul]
      congr 1
      group
    · intro v hv
      rw [mem_eig] at hv
      simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, hv, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← hn, inv_mul_cancel₀ hn0, one_smul]
  have htr : LinearMap.trace K V P = n⁻¹ * (finrank K V : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_smul, map_sum, smul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp [LinearMap.trace_one]
    · intro h _ hne
      have h0 : LinearMap.trace K V (ρ h) = 0 :=
        trace_rho_eq_zero_of_free ρ H hfree A hA hmap ⟨h, hle h.2⟩ (by
          intro e; apply hne; ext; simpa using congrArg Subtype.val e)
      rw [h0, mul_zero]
    · simp
  have h1 := hproj.trace
  rw [htr] at h1
  rw [Nat.card_eq_fintype_card]
  have : ((Fintype.card Hb * finrank K (eig ρ Hb lam) : ℕ) : K) = (finrank K V : K) := by
    push_cast
    rw [← h1, ← hn, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  exact_mod_cast this

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeight
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.CasimirHighest

theorem casimir_comm_gen {R I : Type*} [Ring R] [Fintype I] [DecidableEq I] (e : I → I → R)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j =
      (if j = k then e i l else 0) - (if l = i then e k j else 0)) (k l : I) :
    (∑ a, ∑ b, e a b * e b a) * e k l = e k l * ∑ a, ∑ b, e a b * e b a := by
  rw [← sub_eq_zero]
  have h : ∀ a b, e a b * e b a * e k l - e k l * (e a b * e b a) =
      ((if a = k then e a b * e b l else 0) - (if l = b then e a b * e k a else 0)) +
      ((if b = k then e a l * e b a else 0) - (if l = a then e k b * e b a else 0)) := by
    intro a b
    have : e a b * e b a * e k l - e k l * (e a b * e b a) =
        e a b * (e b a * e k l - e k l * e b a) + (e a b * e k l - e k l * e a b) * e b a := by
      noncomm_ring
    rw [this, he, he]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a = k then e a b * e b l else 0),
    Finset.sum_comm (f := fun a b => if l = a then e k b * e b a else 0)]
  simp

theorem casimir_on_highest_rat {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ}
    (e : Fin m → Fin m → Module.End ℂ V)
    (he : ∀ i j, e i j * e j i - e j i * e i j = e i i - e j j)
    (v : V) (κ : Fin m → ℚ) (hv : ∀ i j, i < j → e i j v = 0)
    (hκ : ∀ i, e i i v = (κ i : ℂ) • v) :
    ∑ i, ∑ j, e i j (e j i v) =
      ((∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) : ℚ) : ℂ) • v := by
  have key : ∀ i j, e i j (e j i v) =
      (((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ) : ℂ) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End ℂ V => f v) (he i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hv i j h, map_zero, sub_zero,
        hκ] at h1
      rw [h1]
      simp [h, h.ne, sub_smul]
    · subst h
      simp [hκ, mul_smul]
    · simp [hv j i h, h.ne', not_lt.mpr h.le]
  have hz : ∑ i : Fin m, ∑ j : Fin m,
      ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ)
      = ∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0), ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have a1 : ∑ j : Fin m, (if i < j then κ i else 0) = ((m : ℚ) - 1 - (i : ℕ)) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi,
        nsmul_eq_mul]
      have := i.2
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    have a2 : ∑ j : Fin m, (if j < i then κ i else 0) = ((i : ℕ) : ℚ) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio,
        nsmul_eq_mul]
    rw [a1, a2]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [key]
  rw [← hz]
  simp only [Rat.cast_sum, Finset.sum_smul]

theorem act_Eab_comm {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (i j k l : Ix p q) :
    act (Eab i j) * act (Eab k l) - act (Eab k l) * act (Eab i j) =
      (if j = k then act (Eab i l) else 0) - (if l = i then act (Eab k j) else 0) := by
  have m : ∀ i j k l : Ix p q, Eab i j * Eab k l = if j = k then Eab i l else 0 := by
    intro i j k l
    split_ifs with hh
    · subst hh; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne, hh]
  rw [← h, m, m, map_sub]
  split_ifs <;> simp

theorem casimir_central_and_highest : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  intro p q V _ _ act h
  refine ⟨fun Z => ?_, fun μ v hv => ?_⟩
  · have hZ : Z = ∑ k, ∑ l, Z k l • Eab k l := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    have hc : ∀ k l, casimir act * act (Eab k l) = act (Eab k l) * casimir act := fun k l =>
      casimir_comm_gen (fun a b => act (Eab a b)) (act_Eab_comm h) k l
    rw [hZ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hc]
  · simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
    obtain ⟨hw, hr⟩ := hv
    have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
      (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) v
      (fun i => μ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
      (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) v
      (fun i => μ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have s1 : ∀ i j, sameBlock (p := p) (q := q) (.inl i) (.inl j) := fun _ _ => trivial
    have s2 : ∀ i j, sameBlock (p := p) (q := q) (.inr i) (.inr j) := fun _ _ => trivial
    have s3 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inl i) (.inr j) := fun _ _ => id
    have s4 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inr i) (.inl j) := fun _ _ => id
    simp only [Fintype.sum_sum_type, if_pos (s1 _ _), if_pos (s2 _ _), if_neg (s3 _ _),
      if_neg (s4 _ _), Finset.sum_const_zero, add_zero, zero_add]
    rw [h1, h2, ← add_smul, ← Rat.cast_add]
    congr 2
    ring

end GlobalTheory.CasimirHighest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem preservesColimitsOfShape_spec_yoneda (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op) := by
  have h1 : PreservesColimitsOfShape J Scheme.Spec.{0}.rightOp := preservesColimitsOfShape_rightOp J _
  have h2 : PreservesColimitsOfShape J (yoneda (C := Scheme.{0})).op := preservesColimitsOfShape_op J _
  infer_instance

theorem hyp_spec_coAug_of_etFF : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  intro R _ A B g hg k
  obtain ⟨h1, h2⟩ := (etFF_basic.2.1 A B g).1 hg
  exact GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R CommRingCat.{0} (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op)
    (fun n => preservesColimitsOfShape_spec_yoneda _) A B g
    (locallySurjective_etale_section_baseChange.1 _ _ (Spec.map g) h1 h2)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIffStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryModule_standardOpens_iff : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ z : K, (∀ b ∈ rB k K x I, Algebra.trace F K (z * b) ∈ omA k x I) ↔ ∃ y ∈ omB k K (rB k K x I) d, τ y = z := by
  first | (exact @GlobalTheory.ComplStd.complementary_iff) | (exact GlobalTheory.ComplStd.complementary_iff) | (intros; apply GlobalTheory.ComplStd.complementary_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeOfRegularOfIsIntegrallyClosedInStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_atPrime_of_regular_of_isIntegrallyClosedIn : ∀ (R C : Type) [CommRing R] [IsDomain R] [CommRing C] [Algebra R C] [Module.Finite R C],
    IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) →
    ∀ (P : Ideal R) [P.IsPrime], IsRegularLocalRing (Localization.AtPrime P) →
    (∀ (P' : Ideal R) [P'.IsPrime], P' ≤ P → P'.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P') (TensorProduct R (Localization.AtPrime P') C)) →
    Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  first | (exact @GlobalTheory.PurityLoc.etale_atPrime_of_isIntegrallyClosedIn) | (exact GlobalTheory.PurityLoc.etale_atPrime_of_isIntegrallyClosedIn) | (intros; apply GlobalTheory.PurityLoc.etale_atPrime_of_isIntegrallyClosedIn  <;> assumption)
end

