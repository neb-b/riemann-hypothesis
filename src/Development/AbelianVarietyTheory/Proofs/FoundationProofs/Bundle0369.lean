module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSemisimpleGeneralisedEigenNewformGamma1Gamm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromL
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem tbA_eps_mul (c : Coef l) (n : ℕ) (s : G ℚ Ω) (u : Qn c n) :
    tbA c n (red c n ⟨eps l s, CupCob.eps_mem c s⟩ * u) =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * tbA c n u := by
  obtain ⟨x, rfl⟩ := red_surjective c n u
  have h : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  have e : (⟨eps l s, CupCob.eps_mem c s⟩ : c.O) * x = ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) • x := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_smul, Algebra.smul_def, ← h]
  rw [← map_mul, e, tbA_red, tbA_red, map_smul, smul_eq_mul, map_mul]
  rfl

theorem matQ_dual1_apply (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (hdet : dt W ^ 2 = 1) (s : G ℚ Ω) (i j : Fin 2) :
    matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s i j =
      red c n ⟨eps l s, CupCob.eps_mem c s⟩ *
        (matQ c n W hint s 0 0 * matQ c n W hint s 1 1 - matQ c n W hint s 0 1 * matQ c n W hint s 1 0) *
        matQ c n W hint s i j := by
  simp only [matQ_apply, ← map_mul, ← map_sub]
  congr 1
  apply Subtype.ext
  show mat (dual1 W) s i j = eps l s * (mat W s 0 0 * mat W s 1 1 - mat W s 0 1 * mat W s 1 0) * mat W s i j
  rw [CupCob.mat_dual1 W hdet, Matrix.smul_apply, smul_eq_mul, Matrix.det_fin_two]

theorem matQ_det_sq (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O)
    (hdet : dt W ^ 2 = 1) (s : G ℚ Ω) :
    (matQ c n W hint s 0 0 * matQ c n W hint s 1 1 - matQ c n W hint s 0 1 * matQ c n W hint s 1 0) ^ 2 = 1 := by
  simp only [matQ_apply, ← map_mul, ← map_sub, ← map_pow]
  rw [← map_one (red c n)]
  congr 1
  apply Subtype.ext
  show (mat W s 0 0 * mat W s 1 1 - mat W s 0 1 * mat W s 1 0) ^ 2 = 1
  rw [← Matrix.det_fin_two]
  exact CupCob.det_sq W hdet s

end GlobalTheory.Ord2.SelPerp

theorem GlobalTheory.Ord2.SelPerp.Phi_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (s : G ℚ Ω) (y : Mn c n), GlobalTheory.Ord2.SelPerp.Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ y) = twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) (GlobalTheory.Ord2.SelPerp.Phi c n y) := by
  intro l _ Ω _ _ c n W hint hdet S hN μ hμ s y
  apply DFunLike.ext
  intro x
  have hμs : μ (toGS Ω (S : Set Pl) s) = cycMod ℚ Ω l n s := by rw [← hμ]; rfl
  obtain ⟨p, rfl⟩ : ∃ p : Mn c n, x = matQ c n W hint s *ᵥ p :=
    ⟨matQ c n W hint s⁻¹ *ᵥ x, by
      rw [Matrix.mulVec_mulVec, ← matQ_mul, mul_inv_cancel, matQ_one, Matrix.one_mulVec]⟩
  rw [twDual_apply, ← map_inv, rhoS_toGS, Matrix.mulVec_mulVec, ← matQ_mul, inv_mul_cancel, matQ_one,
    Matrix.one_mulVec, hμs, SelPerp.Phi_apply, SelPerp.Phi_apply, ← SelPerp.tbA_eps_mul]
  congr 1
  have hd := SelPerp.matQ_det_sq c n W hint hdet s
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, SelPerp.matQ_dual1_apply c n W hint hdet]
  linear_combination (red c n ⟨eps l s, CupCob.eps_mem c s⟩ * (p 0 * y 1 - p 1 * y 0)) * hd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimplePotentialsAtNewformEigensystem
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.SSPotBr

def opZ (N l w : ℕ) : Letter → Module.End ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ)
  | Letter.T q => GlobalTheory.HeckeFamilyMatrices.TqZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w q (sgD N l q)
  | Letter.U => GlobalTheory.HeckeFamilyMatrices.UlZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w l
  | Letter.D d => GlobalTheory.HeckeFamilyMatrices.DdZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w (sgD N l d)

section
open GlobalTheory.HeckeFamilyMatrices Polynomial

theorem eichlerShimuraCoboundaries_le_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : B1 Γ w ≤ Z1 Γ w := by
  rintro z ⟨⟨p, hp⟩, rfl⟩
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · exact Submodule.sub_mem _ (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act w (mat γ) 1 p hp).1 hp
  · change GlobalTheory.HeckeFamilyMatrices.slP w (mat (γ * δ : Γ)) p - p = GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) (GlobalTheory.HeckeFamilyMatrices.slP w (mat γ) p - p) + (GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) p - p)
    have e : mat (γ * δ : Γ) = mat γ * mat δ := by
      simp only [mat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [e, (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act w (mat γ) (mat δ) p hp).2.1, map_sub]
    abel

end

theorem letter_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) :
    ∀ F ∈ Pot ℂ w (Gam N l), opL ℂ N l T F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (opL ℂ N l T F) = opZ N l w T (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro F hF
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨hsg, hTq, hU, hD⟩ := _root_.GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level N l hN hl hlN
  cases T with
  | T q =>
    obtain ⟨hq, hqN⟩ := hT
    have hcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)
    rw [hTq q, LinearMap.sum_apply]
    exact _root_.GlobalTheory.KZ.DictHk.dict_hk N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 q) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q hcop)) F hF
  | U =>
    rw [hU, LinearMap.sum_apply]
    exact _root_.GlobalTheory.KZ.DictHk.dict_hk N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 l) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU F hF
  | D d =>
    rw [hD d, LinearMap.sum_apply]
    exact _root_.GlobalTheory.KZ.DictHk.dict_hk N l w (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) _ _ hN0 hl0 (by simp) (rD _ _ (hsg d hT)) F hF

theorem lift_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) {P : FreeAlgebra ℂ Letter}
    (hP : P ∈ admissibleLettersSubalgebra ℂ N l) :
    ∀ F ∈ Pot ℂ w (Gam N l), FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (FreeAlgebra.lift ℂ (opL ℂ N l) P F) =
        FreeAlgebra.lift ℂ (opZ N l w) P (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  have hN0 : 0 < N := by omega
  obtain ⟨-, hadd, hsmul⟩ := _root_.GlobalTheory.KZ.cocP_laws w N l hN0 hl.pos
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro F hF
    simp only [FreeAlgebra.lift_ι_apply]
    exact letter_pot N l w hN hl hlN T hT F hF
  | algebraMap r =>
    intro F hF
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).smul_mem r hF, hsmul r F⟩
  | add x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hx F hF
    obtain ⟨h3, h4⟩ := hy F hF
    simp only [map_add (f := _), LinearMap.add_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).add_mem h1 h3, by rw [hadd, h2, h4]⟩
  | mul x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hy F hF
    obtain ⟨h3, h4⟩ := hx _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h3, by rw [h4, h2]⟩

end GlobalTheory.KZ.SSPotBr

namespace GlobalTheory.KZ.SSPotBr

theorem ssPotB_at_newform : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N →
    Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
    α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
    ∀ lam : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam (Letter.T q) = g.a q) → lam Letter.U = α →
    (∀ d : ℕ, Nat.Coprime d N → lam (Letter.D d) = g.χ (d : ZMod g.M)) → SSPotB N l (k - 2) lam := by
  intro k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 lam hlT hlU hlD
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hsg, -, -, -⟩ := _root_.GlobalTheory.KZ.DiamondOperatorFamilies.sgD_fams N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level N l hN5 hl hlN
  have hcopq : ∀ q, q.Prime → ¬ q ∣ N * l → Nat.Coprime q N := fun q hq hqN =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)

  obtain ⟨q0, hq0le, hq0⟩ := Nat.exists_infinite_primes (N * l + 1)
  have hq0N : ¬ q0 ∣ N * l := fun h => by
    have := Nat.le_of_dvd (Nat.mul_pos hN0 hl0) h; omega

  have hpres : ∀ t, admitted N l t →
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) := by
    intro t ht
    cases t with
    | T q =>
      obtain ⟨hq, hqN⟩ := ht
      obtain ⟨a, b, -⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q (hcopq q hq hqN)))
      exact ⟨a, b⟩
    | U =>
      obtain ⟨a, b, -⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU
      exact ⟨a, b⟩
    | D d =>
      obtain ⟨a, b, -⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _ (by simp) (rD _ _ (hsg d ht))
      exact ⟨a, b⟩

  have comm := fun (q q' d d' : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hq' : q'.Prime) (hq'N : ¬ q' ∣ N * l)
      (hd : Nat.Coprime d N) (hd' : Nat.Coprime d' N) =>
    _root_.GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt N l k hN5 hl hlN hk3 hk q q' (sgD N l q) (sgD N l q') (sgD N l d) (sgD N l d') (d : ZMod N)
      (d' : ZMod N) hq hqN hq' hq'N (hsg q (hcopq q hq hqN)) (hsg q' (hcopq q' hq' hq'N)) (hsg d hd) (hsg d' hd')
  have h1N : Nat.Coprime 1 N := Nat.coprime_one_left N
  have hcomm : ∀ t t', admitted N l t → admitted N l t' → ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2),
      opZ N l (k - 2) t (opZ N l (k - 2) t' z) - opZ N l (k - 2) t' (opZ N l (k - 2) t z) ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro t t' ht ht' z hz
    cases t with
    | T q =>
      cases t' with
      | T q' => exact (comm q q' 1 1 ht.1 ht.2 ht'.1 ht'.2 h1N h1N z hz).1
      | U => exact (comm q q 1 1 ht.1 ht.2 ht.1 ht.2 h1N h1N z hz).2.1
      | D d => exact (comm q q d 1 ht.1 ht.2 ht.1 ht.2 ht' h1N z hz).2.2.1
    | U =>
      cases t' with
      | T q' =>
        have := (comm q' q' 1 1 ht'.1 ht'.2 ht'.1 ht'.2 h1N h1N z hz).2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U => rw [sub_self]; exact Submodule.zero_mem _
      | D d => exact (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht' h1N z hz).2.2.2.1
    | D d =>
      cases t' with
      | T q' =>
        have := (comm q' q' d 1 ht'.1 ht'.2 ht'.1 ht'.2 ht h1N z hz).2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U =>
        have := (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht h1N z hz).2.2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | D d' => exact (comm q0 q0 d d' hq0 hq0N hq0 hq0N ht ht' z hz).2.2.2.2

  have key : ∀ e : (ZMod N)ˣ → ℕ, (∀ u, Nat.Coprime (e u) N) → (∀ u, ((e u : ℕ) : ZMod N) = u) →
      ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      (∀ q, q.Prime → ¬ q ∣ N * l → (opZ N l (k - 2) (Letter.T q) - lam (Letter.T q) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (opZ N l (k - 2) Letter.U - lam Letter.U • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) ∧
      ∀ u d, e u = d → (opZ N l (k - 2) (Letter.D d) - lam (Letter.D d) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro e he1 he2 z hz n hgen
    have hσD : ∀ u : (ZMod N)ˣ, GlobalTheory.HeckeFamilyMatrices.IsDiam N l (u : ZMod N) (sgD N l (e u)) := fun u => by
      have := hsg (e u) (he1 u); rwa [he2 u] at this
    have hchi : ∀ u : (ZMod N)ˣ, lam (Letter.D (e u)) = g.χ (ZMod.castHom hN (ZMod g.M) (u : ZMod N)) := fun u => by
      rw [hlD _ (he1 u), ← he2 u, map_natCast (ZMod.castHom hN (ZMod g.M))]
    obtain ⟨cT, cU, cD⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 (fun q => sgD N l q)
      (fun u => sgD N l (e u)) (fun q hq hqN => hsg q (hcopq q hq hqN)) hσD z hz n
      (fun q hq hqN => by have h := hgen (Letter.T q) ⟨hq, hqN⟩; rw [hlT q hq hqN] at h; exact h)
      (by have h := hgen Letter.U trivial; rw [hlU] at h; exact h)
      (fun u => by have h := hgen (Letter.D (e u)) (he1 u); rw [hchi u] at h; exact h)
    refine ⟨fun q hq hqN => ?_, ?_, ?_⟩
    · rw [hlT q hq hqN]; exact cT q hq hqN
    · rw [hlU]; exact cU
    · rintro u d rfl
      rw [hchi u]; exact cD u
  have hval1 : ∀ u : (ZMod N)ˣ, Nat.Coprime (u : ZMod N).val N := fun u => ZMod.val_coe_unit_coprime u
  have hval2 : ∀ u : (ZMod N)ˣ, (((u : ZMod N).val : ℕ) : ZMod N) = u := fun u => ZMod.natCast_zmod_val _
  have heig : ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      ∀ t, admitted N l t → (opZ N l (k - 2) t - lam t • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro z hz n hgen t ht
    cases t with
    | T q => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).1 q ht.1 ht.2
    | U => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).2.1
    | D d =>
      have hd : Nat.Coprime d N := ht
      refine (key (fun u => if (u : ZMod N) = (d : ZMod N) then d else (u : ZMod N).val) ?_ ?_ z hz n hgen).2.2
        (ZMod.unitOfCoprime d hd) d (if_pos (ZMod.coe_unitOfCoprime d hd))
      · intro u; split_ifs
        · exact hd
        · exact hval1 u
      · intro u; split_ifs with h
        · exact h.symm
        · exact hval2 u
  obtain ⟨P, hP, hP1, hPz⟩ := _root_.GlobalTheory.exists_genEig_idem_poly ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ) (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2))
    (GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) Letter (admitted N l) (opZ N l (k - 2)) lam (eichlerShimuraCoboundaries_le_eichlerShimuraCocycles _ _)
    (_root_.GlobalTheory.KZ.H3.lev_fd N l (k - 2) hN0 hl0) (fun t ht => (hpres t ht).1) (fun t ht => (hpres t ht).2) hcomm heig
  refine ⟨P, hP, hP1, fun F hF T hT => ?_⟩
  obtain ⟨hD1, hD2, hD3⟩ := _root_.GlobalTheory.KZ.cocP_laws (k - 2) N l hN0 hl0
  obtain ⟨hPF, hcPF⟩ := lift_pot N l (k - 2) hN5 hl hlN hP F hF
  obtain ⟨hTF, hcTF⟩ := letter_pot N l (k - 2) hN5 hl hlN T hT _ hPF
  have hG : (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) = opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) +
        (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F := by
    simp [sub_eq_add_neg, neg_smul]
  have hGpot : opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) + (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈
      Pot ℂ (k - 2) (Gam N l) :=
    (Betti.potSub ℂ (k - 2) (Gam N l)).add_mem hTF ((Betti.potSub ℂ (k - 2) (Gam N l)).smul_mem _ hPF)
  rw [hG]
  refine (hD1 _ hGpot).2.2 ?_
  rw [hD2, hD3, hcTF, hcPF]
  have := hPz (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) (hD1 F hF).1 T hT
  simpa [sub_eq_add_neg, neg_smul] using this

end GlobalTheory.KZ.SSPotBr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesEqZeroOfValsTendstoZero
section
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory

theorem KZ.norm_prime_lt_one_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem KZ.eq_zero_of_cg_all (l : ℕ) [Fact l.Prime] (x : Qbar l) (h : ∀ k : ℕ, Cg k x 0) :
    x = 0 := by
  have hlt := KZ.norm_prime_lt_one_qbar l
  have hn : 0 ≤ ‖((l : ℕ) : Qbar l)‖ := norm_nonneg _
  have ht : Filter.Tendsto (fun k : ℕ => ‖((l : ℕ) : Qbar l)‖ ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hn hlt
  have hle : ∀ k : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ k := by
    intro k
    have := h k
    unfold Cg at this
    simpa [norm_pow] using this
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' ht hle
  exact norm_le_zero_iff.mp h0

theorem KZ.series_eq_zero_of_vals_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)), (∀ n, F.coeff n ∈ c.O) → (∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) → F = 0 := by
  intro l _ c F hO hv
  ext n
  rw [map_zero]
  apply KZ.eq_zero_of_cg_all l
  intro k
  obtain ⟨m₁, hm⟩ := hv k
  exact _root_.GlobalTheory.KZ.CoefVal.coeff_cg_of_values l c F k m₁ hO hm n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromLStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameShapiroSystem_limit_unramified_away_from_l : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (Yt : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) →
  (∀ r x, χ r x ∈ c.O) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  (∀ r s a i, ‖Yt s a i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  ∃ v : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, ∀ a, Yt s a = mat W s *ᵥ v a - v a := by
  first | exact @GlobalTheory.KA.TameUnr.tame_limit_unram | exact GlobalTheory.KA.TameUnr.tame_limit_unram | (intros; apply GlobalTheory.KA.TameUnr.tame_limit_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TruncatedShiftedSeriesEqIntegralPolyCombination
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem tval_eq_sum_pow_of_integral : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  intro l _ c F N hF
  let Q : Polynomial c.O := ∑ n ∈ Finset.range N, Polynomial.C (⟨F.coeff n, hF n⟩ : c.O) * (Polynomial.X - Polynomial.C 1) ^ n
  refine ⟨fun j => ((Q.coeff j : c.O) : Qbar l), fun j => (Q.coeff j).2, fun z => ?_⟩
  have hdeg : Q.natDegree < N ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inr h
    · left
      obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
      have hn' : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_pow_le).trans ?_)
      calc n * (Polynomial.X - Polynomial.C (1 : c.O)).natDegree ≤ n * 1 :=
            Nat.mul_le_mul_left _ (Polynomial.natDegree_X_sub_C_le _)
        _ ≤ k := by omega
  rcases hdeg with hd | rfl
  · have h1 := Polynomial.aeval_eq_sum_range' (R := c.O) (x := z) hd
    have h2 : Polynomial.aeval z Q = tval F N z := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Q, tval, map_sum]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  · simp [tval]

end GlobalTheory.KZ.Cmp
end

