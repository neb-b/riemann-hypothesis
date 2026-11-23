module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695

@[expose] public section

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)

theorem b_mono {R : Ranks} (P : HCParam R) : Monotone P.b := by
  obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by have := R.two_le_m; omega⟩
  have ht : (0 : ℚ) ≤ R.t := by positivity
  intro a c hac
  induction' hc : c.1 - a.1 with d ih generalizing c
  · rw [show a = c from Fin.ext (by have : a.1 ≤ c.1 := hac; omega)]
  · let c' : Fin R.m := ⟨c.1 - 1, by omega⟩
    have h1 := ih (c := c') (show a.1 ≤ c.1 - 1 by omega) (show c.1 - 1 - a.1 = d by omega)
    have h2 := P.gap_be c'
    have h3 := P.gap_eb c' (show c.1 - 1 + 1 < R.m by omega)
    rw [show (⟨c'.1 + 1, _⟩ : Fin R.m) = c from Fin.ext (show c.1 - 1 + 1 = c.1 by omega)] at h3
    linarith

theorem u_last_le {R : Ranks} (P : HCParam R) (h : 0 < R.k) (a : Fin R.k) : P.u ⟨R.k - 1, by omega⟩ ≤ P.u a := by
  induction' hd : R.k - 1 - a.1 with d ih generalizing a
  · rw [show a = ⟨R.k - 1, by omega⟩ from Fin.ext (by have := a.2; simp only; omega)]
  · have h1 := ih ⟨a.1 + 1, by omega⟩ (show R.k - 1 - (a.1 + 1) = d by omega)
    have h2 := P.u_gt_v ⟨a.1, by omega⟩
    have h3 := P.v_gt_u ⟨a.1, by omega⟩
    exact h1.trans (h3.trans h2).le

theorem gap_rowPar {R : Ranks} (P : HCParam R) (j : Fin R.m) {y : ℚ} (hy : y ∈ rowPar P) :
    ((R.t : ℚ) + 3) / 2 ≤ y + P.e j ∨ y + P.e j ≤ -(((R.t : ℚ) + 3) / 2) := by
  have hk := R.m_add_three_le_k
  have h0 := P.gap_be j
  rcases Multiset.mem_add.1 hy with h | h
  · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 h
    have h1 := P.v_gt_u a
    have h2 := u_last_le P (by omega) ⟨a.1 + 1, by omega⟩
    have h3 := P.u_last_gt (by omega) j.pos
    have h4 := b_mono P (show (⟨0, j.pos⟩ : Fin R.m) ≤ j from Nat.zero_le _)
    left
    linarith
  · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 h
    rcases le_or_gt a j with h1 | h1
    · have := b_mono P h1
      left
      linarith
    · have h2 := P.gap_eb j (by have : j.1 < a.1 := h1; omega)
      have h3 := b_mono P (show (⟨j.1 + 1, by have : j.1 < a.1 := h1; omega⟩ : Fin R.m) ≤ a from h1)
      right
      linarith

section Twist

variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)

def twBy : D.naut.CG n := D.naut.tw π (S.e1.symm ⟨ξ, hξ⟩)

theorem rankOneCuspidal_unitaryChar_equiv_apply_symm : (S.e1 (S.e1.symm ⟨ξ, hξ⟩)).1 = ξ := by rw [S.e1.apply_symm_apply]

variable {π}

theorem twBy_unr {w : PlE D.host} (h : D.naut.unr (D.naut.locG π w)) (h' : ξ.UnrAt w) :
    D.naut.unr (D.naut.locG (twBy S π hξ) w) ∧ D.naut.frobEig (D.naut.locG (twBy S π hξ) w) =
      (D.naut.frobEig (D.naut.locG π w)).map (· * ((ξ.val w : ℂˣ) : ℂ)⁻¹) := by
  have h1 : (S.e1 (S.e1.symm ⟨ξ, hξ⟩)).1.UnrAt w := by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm]
  have h2 := (S.unr_iff _ w).2 h1
  have h3 := S.frob _ w h1
  rw [rankOneCuspidal_unitaryChar_equiv_apply_symm, Units.val_inv_eq_inv_val] at h3
  rw [twBy, D.naut.locG_tw]
  exact ⟨D.naut.unr_char _ _ (D.naut.locG_dim _ _) h h2, D.naut.frobEig_char _ _ _ h h2 (D.naut.locG_dim _ _) h3⟩

theorem twBy_mono {w : PlE D.host} (h : D.naut.mono0 (D.naut.locG π w)) : D.naut.mono0 (D.naut.locG (twBy S π hξ) w) := by
  rw [twBy, D.naut.locG_tw, D.naut.monomial_char_iff _ _ (D.naut.locG_dim _ _)]
  exact h

theorem twBy_csd (h : D.naut.csd π) (h' : IsCSD D.host ξ) : D.naut.csd (twBy S π hξ) :=
  D.naut.csd_tw _ _ ((S.csd _).2 (by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm])) h

theorem twBy_inf {a : D.R.Psi → ℚ} (h : ξ.HasInfQ (embPsi D.host) a) (τ : D.what₂.Tau) :
    D.naut.infG (twBy S π hξ) (embOver D τ false) =
      (D.naut.infG π (embOver D τ false)).map (· + (a (D.eTau τ) : ℂ)) ∧
    D.naut.infG (twBy S π hξ) (embOver D τ true) =
      (D.naut.infG π (embOver D τ true)).map (· + -(a (D.eTau τ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := S.infG (S.e1.symm ⟨ξ, hξ⟩) a (by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm]) (D.eTau τ)
  refine ⟨D.naut.infG_tw _ _ _ _ h1, D.naut.infG_tw _ _ _ _ ?_⟩
  rw [← h2]
  exact congrArg _ (RingHom.ext (embOver_true_apply D τ))

theorem twBy_regAlg (hr : D.naut.ralg π) {a : D.R.Psi → ℚ} (h : ξ.HasInfQ (embPsi D.host) a) {s : ℝ}
    (hs : ∀ g, (∃ m : ℤ, (a g : ℂ) + s = m) ∧ ∃ m : ℤ, -(a g : ℂ) + s = m) : RegAlgShift D.naut (twBy S π hξ) s := by
  intro φ
  obtain ⟨h1, h2⟩ := (D.naut.ralg_def π).1 hr φ
  obtain ⟨c, m, hc, hm⟩ : ∃ (c : ℂ) (m : ℤ),
      D.naut.infG (twBy S π hξ) φ = (D.naut.infG π φ).map (· + c) ∧ c + s = m := by
    obtain ⟨τ, b, rfl⟩ := exists_embOver D φ
    obtain ⟨⟨m, hm⟩, m', hm'⟩ := hs (D.eTau τ)
    cases b
    exacts [⟨_, m, (twBy_inf S hξ h τ).1, hm⟩, ⟨_, m', (twBy_inf S hξ h τ).2, hm'⟩]
  rw [hc]
  refine ⟨h1.map (add_left_injective c), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h2 y hy
  exact ⟨k + m, by push_cast; rw [← hm]; ring⟩

end Twist

section Chars

variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)

theorem isDelta_delAt : IsDelta (H := D.host) (if l = D.host.pde then D.host.pde' else D.host.pde) (C.delAt l) := by
  unfold CharFrame.delAt
  split_ifs
  exacts [C.isDel', C.isDel]

theorem mu_unitary : (muBase C l j)⁻¹.IsUnitary := ((C.isMu0 j).unitary.mul (isDelta_delAt C l).unitary).inv

theorem isCSD_inv {χ : HChar D.host.E} (h : IsCSD D.host χ) : IsCSD D.host χ⁻¹ :=
  ⟨fun w w' hw k => congrArg (·⁻¹) (h.1 w w' hw k), fun k => congrArg (·⁻¹) (h.2 k)⟩

theorem isCSD_mul {χ χ' : HChar D.host.E} (h : IsCSD D.host χ) (h' : IsCSD D.host χ') : IsCSD D.host (χ * χ') :=
  ⟨fun w w' hw k => (congrArg₂ (· * ·) (h.1 w w' hw k) (h'.1 w w' hw k)).trans (mul_inv _ _).symm,
    fun k => (congrArg₂ (· * ·) (h.2 k) (h'.2 k)).trans (mul_inv _ _).symm⟩

theorem mu_csd : IsCSD D.host (muBase C l j)⁻¹ :=
  isCSD_inv (isCSD_mul (GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ (C.isMu0 j).triv) (GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ (isDelta_delAt C l).triv))

theorem mu_inf : (muBase C l j)⁻¹.HasInfQ (embPsi D.host) (eExp D j) := by
  have h1 : ∀ k, (C.delAt l).inf k = 1 := fun k => Units.ext <| by
    have := GlobalTheory.GalChar.del_alg (hframe C) l k fun φ => by
      have h2 := congrArg φ (GlobalTheory.JumpDictionaryFoundation.sqrt_sq D.host)
      have h3 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
      rw [map_pow, map_neg, map_natCast] at h2
      nlinarith [sq_nonneg (φ D.host.sqrtMinusD)]
    exact this.trans (by simp)
  have h2 := GlobalTheory.HalfIntChars.hasInfQ_inv ((C.isMu0 j).inf.mul_triv h1)
  rwa [show (-fun τ => -eExp D j τ) = eExp D j from funext fun _ => neg_neg _] at h2

theorem eta_inf : C.eta⁻¹.HasInfQ (embPsi D.host) (fun _ => -(1 / 2)) :=
  GlobalTheory.HalfIntChars.hasInfQ_inv (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, C.isEta.inf⟩

theorem mu_unr {i : D.ntw.Tw} {w : PlE D.host} (hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k)) (hp : w ∉ D.ntw.pD i) :
    (muBase C (D.ntw.l i) j).UnrAt w :=
  ((C.isMu0 j).unr w hg).mul ((isDelta_delAt C _).unr w fun h => hp (by
    rw [← Finset.mem_coe, D.ntw.pD_eq]; exact h))

end Chars

theorem isSSRep_of_smul {Γ K : Type} [Group Γ] [Field K] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) K} (c : Γ → K) (hc : ∀ g, c g ≠ 0)
    (h : ∀ g, (ρ' g : Matrix (Fin n) (Fin n) K) = c g • (ρ g : Matrix (Fin n) (Fin n) K)) (hs : IsSSRep ρ) : IsSSRep ρ' := by
  have key : ∀ W, IsInv ρ' W ↔ IsInv ρ W := fun W => forall_congr' fun g => forall₂_congr fun v _ => by
    rw [h, Matrix.smul_mulVec, W.smul_mem_iff (hc g)]
  exact fun W hW => (hs W ((key W).1 hW)).imp fun W' h' => ⟨(key W').2 h'.1, h'.2⟩

section Triple

variable {D : D7} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}

theorem cpow_add_real (P : PlE D.host) (a b : ℝ) : ((normV P : ℕ) : ℂ) ^ ((a + b : ℝ) : ℂ) =
    ((normV P : ℕ) : ℂ) ^ (a : ℂ) * ((normV P : ℕ) : ℂ) ^ (b : ℂ) := by
  rw [Complex.ofReal_add, Complex.cpow_add _ _ (normV_ne_zero P)]

theorem cpow_ne_zero' (P : PlE D.host) (a : ℂ) : ((normV P : ℕ) : ℂ) ^ a ≠ 0 := by
  simp [normV_ne_zero P]

theorem rowFacts (h : IsParam σ π) (hm : ∀ v, D.naut.mono0 (D.naut.locG π v)) (j : Fin D.R.m) :
    RowFacts D.naut i (twBy S π C.isEta.unitary.inv) (twBy S π (mu_unitary C (D.ntw.l i) j)) := by
  have hinf : ∀ τ, D.naut.infG (twBy S π (mu_unitary C (D.ntw.l i) j)) (embOver D τ false) =
      (rowPar (D.hc τ)).map (fun y => ((y + (D.hc τ).e j : ℚ) : ℂ)) ∧
      D.naut.infG (twBy S π (mu_unitary C (D.ntw.l i) j)) (embOver D τ true) =
      (rowPar (D.hc τ)).map (fun y => -((y + (D.hc τ).e j : ℚ) : ℂ)) := fun τ => by
    obtain ⟨h1, h2⟩ := twBy_inf S (π := π) (mu_unitary C (D.ntw.l i) j) (mu_inf C _ j) τ
    rw [h1, h2, (h.inf τ).1, (h.inf τ).2, Multiset.map_map, Multiset.map_map, eExp, D.eTau.symm_apply_apply]
    refine ⟨Multiset.map_congr rfl fun y _ => ?_, Multiset.map_congr rfl fun y _ => ?_⟩ <;>
      simp only [Function.comp_apply] <;> push_cast <;> ring
  refine ⟨fun v hv => (twBy_unr S _ (h.unr v hv) (C.isEta.unr v).inv).1, fun v => twBy_mono S _ (hm v),
    fun v hv hp => (twBy_unr S _ (h.unr v hv) (mu_unr C j hv hp).inv).1, fun v => twBy_mono S _ (hm v),
    twBy_csd S _ h.csd (mu_csd C _ j), (regAlgShift_zero _ _).1 (twBy_regAlg S _ h.ralg (mu_inf C _ j) fun g => ?_),
    fun φ => ?_, fun φ z hz a ha => ?_⟩
  · obtain ⟨z, hz⟩ := eExp_int j g
    exact ⟨⟨z, by simp [hz]⟩, -z, by simp [hz]⟩
  · obtain ⟨τ, b, rfl⟩ := exists_embOver D φ
    have e1 : (embOver D τ false).comp (cj D) = embOver D τ true := RingHom.ext fun _ => rfl
    have e2 : (embOver D τ true).comp (cj D) = embOver D τ false := RingHom.ext fun x => by
      rw [RingHom.comp_apply, embOver_true_apply, ← RingHom.comp_apply, ← RingHom.comp_apply, RingHom.comp_assoc, e1,
        RingHom.comp_apply, embOver_true_apply, Complex.conj_conj]
    cases b
    · rw [e1, (hinf τ).1, (hinf τ).2, Multiset.map_map]
      rfl
    · rw [e2, (hinf τ).1, (hinf τ).2, Multiset.map_map]
      exact Multiset.map_congr rfl fun _ _ => (neg_neg _).symm
  · obtain ⟨τ, b, rfl⟩ := exists_embOver D φ
    obtain ⟨y, hy, hz'⟩ : ∃ y : ℚ, (((D.R.t : ℚ) + 3) / 2 ≤ y ∨ y ≤ -(((D.R.t : ℚ) + 3) / 2)) ∧ z = y := by
      cases b
      · rw [(hinf τ).1] at hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        exact ⟨_, gap_rowPar _ j hy, rfl⟩
      · rw [(hinf τ).2] at hz
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        exact ⟨-(y + (D.hc τ).e j), (gap_rowPar _ j hy).symm.imp (fun _ => by linarith) fun _ => by linarith,
          (Rat.cast_neg _).symm⟩
    have h1 : (a : ℚ) = -y + ((D.R.t : ℚ) - 1) / 2 := by
      apply Rat.cast_injective (α := ℂ)
      push_cast
      rw [ha, hz']
    refine hy.imp (fun h2 => ?_) fun h2 => ?_
    · exact_mod_cast (show (a : ℚ) < -1 by linarith)
    · exact_mod_cast (show (D.R.t : ℚ) < a by linarith)

end Triple

end GlobalTheory.TripleLocal

end
