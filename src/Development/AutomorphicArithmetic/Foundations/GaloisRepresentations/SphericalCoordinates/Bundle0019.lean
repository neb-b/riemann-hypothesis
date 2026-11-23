module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0017
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem trace_conj {F : Type} [Field F] [NumberField F] [IsCMField F] (x : F) :
    Algebra.trace ℚ F (IsCMField.complexConj F x) = Algebra.trace ℚ F x := by
  let e : F ≃ₐ[ℚ] F := AlgEquiv.ofRingEquiv (f := (IsCMField.complexConj F).toRingEquiv) (fun r => by simp)
  exact Algebra.trace_eq_of_algEquiv e x

private theorem trace_strip {F : Type} [Field F] [NumberField F] {a b : F}
    (h : ∀ x : F, Algebra.trace ℚ F (a * x) = Algebra.trace ℚ F (b * x)) : a = b := by
  have hnd := traceForm_nondegenerate ℚ F
  have : a - b = 0 := by
    apply hnd.1
    intro x
    show Algebra.trace ℚ F ((a - b) * x) = 0
    rw [sub_mul, map_sub, h, sub_self]
  exact sub_eq_zero.1 this

private theorem exists_trace_rep {F : Type} [Field F] [NumberField F] (f : F →+ ℚ) :
    ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) = f x := by
  have hnd := traceForm_nondegenerate ℚ F
  refine ⟨(LinearMap.BilinForm.toDual _ hnd).symm f.toRatLinearMap, fun x => ?_⟩
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) f.toRatLinearMap x

private theorem sum_single {F : Type} [Field F] {n : ℕ} (u : Fin n → F) :
    u = ∑ j, u j • (Pi.single j 1 : Fin n → F) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem form_ext {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) F}
    (h : ∀ u w : Fin n → F, Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (M *ᵥ u)) =
      Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (N *ᵥ u))) : M = N := by
  ext i j
  apply trace_strip
  intro x
  have := h (x • Pi.single j 1) (Pi.single i 1)
  have e : ∀ P : Matrix (Fin n) (Fin n) F,
      (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) ⬝ᵥ (P *ᵥ (x • Pi.single j 1)) = P i j * x := by
    intro P
    have e1 : (fun k => IsCMField.complexConj F ((Pi.single i 1 : Fin n → F) k)) = (Pi.single i 1 : Fin n → F) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [e1, Matrix.mulVec_smul, Matrix.mulVec_single_one, single_one_dotProduct]
    simp [mul_comm]
  rwa [e M, e N] at this

private theorem form_core {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    (B : (Fin n → F) →+ (Fin n → F) →+ ℚ)
    (hadj : ∀ (x : F) u w, B (x • u) w = B u (IsCMField.complexConj F x • w))
    (hskew : ∀ u w, B u w = - B w u)
    (hnd : ∀ u, (∀ w, B u w = 0) → u = 0) :
    ∃ A : Matrix (Fin n) (Fin n) F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj F))ᵀ = -A ∧
      ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
  have hrep : ∀ i j : Fin n, ∃ a : F, ∀ x, Algebra.trace ℚ F (a * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := fun i j =>
    exists_trace_rep (((AddMonoidHom.eval (Pi.single i 1 : Fin n → F)).comp B).comp
      (AddMonoidHom.mk' (fun x : F => x • (Pi.single j 1 : Fin n → F)) (fun a b => add_smul a b _)))
  choose A₀ hA₀ using hrep
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) F, ∀ i j x, Algebra.trace ℚ F (A i j * x) =
      B (x • (Pi.single j 1 : Fin n → F)) (Pi.single i 1) := ⟨A₀, hA₀⟩
  have hterm : ∀ (u w : Fin n → F) i j, B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
      Algebra.trace ℚ F (IsCMField.complexConj F (w i) * (A i j * u j)) := by
    intro u w i j
    have e1 : B (u j • (Pi.single j 1 : Fin n → F)) (w i • (Pi.single i 1 : Fin n → F)) =
        B (IsCMField.complexConj F (w i) • (u j • (Pi.single j 1 : Fin n → F))) (Pi.single i 1) := by
      rw [hadj (IsCMField.complexConj F (w i)) (u j • _), IsCMField.complexConj_apply_apply]
    rw [e1, smul_smul, ← hA]
    congr 1
    ring
  have hform : ∀ u w, B u w = Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (w i)) ⬝ᵥ (A *ᵥ u)) := by
    intro u w
    conv_lhs => rw [sum_single u, sum_single w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, AddMonoidHom.finsetSum_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, hterm]
  refine ⟨A, ?_, ?_, hform⟩
  · intro hdet
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    exact hv (hnd v fun w => by rw [hform, hAv]; simp)
  · ext i j
    show IsCMField.complexConj F (A j i) = - A i j
    apply trace_strip
    intro x
    have h1 : Algebra.trace ℚ F (IsCMField.complexConj F (A j i) * x) =
        Algebra.trace ℚ F (A j i * IsCMField.complexConj F x) := by
      rw [← trace_conj (A j i * IsCMField.complexConj F x), map_mul (IsCMField.complexConj F), IsCMField.complexConj_apply_apply]
    rw [h1, hA, hadj, IsCMField.complexConj_apply_apply, hskew, ← hA, neg_mul, map_neg]

private theorem bc_skew {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La) (halt : ∀ x, E x x = 0)
    (u w : ℚ ⊗[ℤ] La) : E.baseChange ℚ u w = - E.baseChange ℚ w u := by
  have hs : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb, neg_add]
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd, neg_add]
    | tmul b y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [hs x y]
      simp [mul_comm]

private theorem exists_pure {La : Type} [AddCommGroup La] (v : ℚ ⊗[ℤ] La) :
    ∃ (N : ℕ) (x : La), N ≠ 0 ∧ N • v = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add a b ha hb =>
    obtain ⟨N, x, hN, hx⟩ := ha
    obtain ⟨M, y, hM, hy⟩ := hb
    refine ⟨N * M, M • x + N • y, mul_ne_zero hN hM, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, mul_comm N M, mul_smul, hx, mul_comm M N, mul_smul, hy,
      TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  | tmul a x =>
    refine ⟨a.den, a.num • x, a.den_ne_zero, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul, zsmul_eq_mul, _root_.mul_one, Rat.den_mul_eq_num]

private theorem bc_nondeg {La : Type} [AddCommGroup La] (E : LinearMap.BilinForm ℤ La)
    (hE : Function.Injective E) (v : ℚ ⊗[ℤ] La) (h : ∀ w, E.baseChange ℚ v w = 0) : v = 0 := by
  obtain ⟨N, x, hN, hx⟩ := exists_pure v
  have hx0 : x = 0 := by
    apply hE
    ext y
    have h1 := h ((1 : ℚ) ⊗ₜ[ℤ] y)
    have h2 : E.baseChange ℚ (N • v) ((1 : ℚ) ⊗ₜ[ℤ] y) = 0 := by simp [h1]
    rw [hx, LinearMap.BilinForm.baseChange_tmul] at h2
    simpa using h2
  rw [hx0, TensorProduct.tmul_zero] at hx
  have : (N : ℚ) • v = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hx
  exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hN)

theorem UpperTheory.Gal.W2.fForm_of :
    UpperTheory.Gal.W2.FForm := by
  intro p _ D G L kp σ hF
  let E := D.EF.baseChange ℚ
  let B : (Fin G.n → G.F) →+ (Fin G.n → G.F) →+ ℚ :=
    AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun w => E (kp.symm u) (kp.symm w)) (by intro a b; simp))
      (by intro a b; ext w; simp)
  have hB : ∀ u w, B u w = E (kp.symm u) (kp.symm w) := fun _ _ => rfl
  have hsc : ∀ (x : G.F) (u : Fin G.n → G.F),
      kp.symm (x • u) = L.rep (algebraMap G.F G.C x) (kp.symm u) := by
    intro x u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply, AlgEquiv.commutes]
    ext i
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
  have hsm : ∀ (c : G.C) (u : Fin G.n → G.F), kp.symm (σ c *ᵥ u) = L.rep c (kp.symm u) := by
    intro c u
    apply kp.injective
    rw [AddEquiv.apply_symm_apply, hF, AddEquiv.apply_symm_apply]
  obtain ⟨A, hdet, hskew, hform⟩ := form_core B
    (by
      intro x u w
      rw [hB, hB, hsc, hsc, L.adj]
      show E _ (L.rep ((G.star _).unop) _) = _
      rw [G.star_F])
    (by intro u w; exact bc_skew D.EF D.alt _ _)
    (by
      intro u hu
      have h0 : kp.symm u = 0 := bc_nondeg D.EF D.nondeg _ fun w => by
        have := hu (kp w)
        rwa [hB, AddEquiv.symm_apply_apply] at this
      simpa using congrArg kp h0)
  have hform' : ∀ u w, E u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u)) := by
    intro u w
    have := hform (kp u) (kp w)
    rwa [hB, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at this
  refine ⟨A, hdet, hskew, hform', fun c => ?_⟩
  apply form_ext
  intro u w
  have hcj : (fun i => IsCMField.complexConj G.F (w i)) ⬝ᵥ
        (((σ c).map (IsCMField.complexConj G.F))ᵀ * A) *ᵥ u =
      (fun i => IsCMField.complexConj G.F ((σ c *ᵥ w) i)) ⬝ᵥ (A *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    congr 1
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hcj, ← Matrix.mulVec_mulVec]
  have h1 := hform (σ (sh G c) *ᵥ u) w
  have h2 := hform u (σ c *ᵥ w)
  rw [← h1, ← h2, hB, hB, hsm, hsm]
  have h3 : sh G (sh G c) = c := G.star_star c
  have h4 := L.adj (sh G c) (kp.symm u) (kp.symm w)
  rw [h3] at h4
  exact h4
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixFwd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem coordA_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (hc : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  refine ⟨hc.1, fun a => ?_⟩
  obtain ⟨w, hw, hw'⟩ := hc.2 a
  obtain ⟨k, rfl⟩ := hd
  refine ⟨k • w, AddSubgroup.nsmul_mem _ hw k, ?_⟩
  rw [hw', smul_smul]

private theorem eq_of_nsmul_eq_of_ne_zero {g m : ℕ} (hm : m ≠ 0) {a b : Fin g → ℂ} (h : m • a = m • b) : a = b := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [← Nat.cast_smul_eq_nsmul ℂ m a, ← Nat.cast_smul_eq_nsmul ℂ m b] at h
  exact smul_right_injective _ hm' h

private theorem fix_line_ext {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D' : PLat D.O D.inv} {j : D'.La →+ VQ D}
    (hdiv : ∀ w, ∃ (m : ℕ) (u : D'.La), m ≠ 0 ∧ m • w = j u)
    (Q : VQ D →+ (Fin D.g → ℂ)) (hh : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ))
    (hl : ∀ u, Q (actY L y (j u)) = hh (Q (j u))) :
    ∃ H : Matrix (Fin D.g) (Fin D.g) ℂ, ∀ w, Q (actY L y w) = H *ᵥ Q w := by
  refine ⟨LinearMap.toMatrix' (hh : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)), fun w => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  show Q (actY L y w) = hh (Q w)
  obtain ⟨m, u, hm, hmu⟩ := hdiv w
  apply eq_of_nsmul_eq_of_ne_zero hm
  have e1 : m • Q (actY L y w) = Q (actY L y (j u)) := by
    rw [← hmu, map_nsmul, map_nsmul]
  have e2 : m • hh (Q w) = hh (Q (j u)) := by
    rw [← hmu, map_nsmul, map_nsmul]
  rw [e1, e2, hl]

theorem UpperTheory.Gal.W2.fixFwd_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.FixFwd := by
  intro hHecke hOne hForm hIso hFix _hAct p _ D G L gb N N' h hLev X X' c₁ c₂ hX hL hX' hL' ρ hFine v t₀ B PD RD D' t hCls' P j a hC x e hU hx
  have hN : 0 < N := by
    have := hLev.1
    omega
  obtain ⟨hPl, hCA', hLoc, Q, hPerQ, hQP, hrel⟩ := hC
  obtain ⟨e₁, hU₁, -⟩ := hOne p D G L gb N N' h hLev X X' c₁ hX hL hX' hL' ρ hFine B PD D' t hCls' j a.1 hPl hCA' hLoc P x e hU
  obtain ⟨D'', t'', P'', e'', inc, j'', hCls'', hU'', hPinc, -, hdivinc, hjinc, hPl'', hCA'', hLoc''⟩ :=
    hHecke p D G L gb N N' h hLev X X' c₂ hX hL hX' hL' ρ hFine D' t P x e hU B j a.1.1 (PD.lat a.1.2) hPl hCA' hLoc
  have hx' : (x ≫ c₁.q : Sp ℂ ⟶ (gfam X.univ hX hL).X) = x ≫ c₂.q := hx
  revert e₁
  rw [hx']
  intro e₁ hU₁
  obtain ⟨w, hh, hmk, hPw, -⟩ := _root_.GlobalTheory.PELU.unifAt_cmp D.O D.inv D.g ρ _ _ _ _ N D' D'' t t'' P P'' _ _ _ hN hU₁ hU''
  obtain ⟨y, s, hs, hys, hyj⟩ := hForm p D G L B.β B.β D'' D' j'' j hPl'' hPl
    (w : D'.La →ₗ[D.O] D''.La) 1 one_pos (fun u u' => by
      rw [_root_.one_mul]
      exact hmk.1 u u')
  let Y : GlobalTheory.LKCx.grp G B.β := ⟨(y, s), hys, hs⟩
  have hQ'' : ∀ u'', Q (j'' u'') = P'' u'' := by
    intro u''
    obtain ⟨d, u, hd0, hdu⟩ := hdivinc u''
    have e1 : d • Q (j'' u'') = Q (j u) := by
      rw [← map_nsmul, ← map_nsmul, ← hdu, hjinc]
    have e2 : d • P'' u'' = P u := by
      rw [← map_nsmul, ← hdu, hPinc]
    apply eq_of_nsmul_eq_of_ne_zero hd0
    rw [e1, e2, hQP]
  have hl : ∀ u, Q (actY L Y (j u)) = hh (Q (j u)) := by
    intro u
    rw [hQP, ← hPw, ← hQ'']
    congr 1
    exact (hyj u).symm
  obtain ⟨H, hH⟩ := fix_line_ext L Y hPl.2.2.1 Q hh hl
  have hfixL := ((hFix p D G L v t₀ ρ B.β RD Q a.2 hPerQ hrel Y).1).2 ⟨H, hH⟩
  have hmem := (hIso p D G L B PD N hN hLev.2.1 D'' t'' D' t j'' j (a.1.1 * h⁻¹, a.1.2) a.1 N N' t'' t
    hCls'' hCls' hPl'' hPl hCA'' (coordA_of_dvd L hLev.2.2.2.2.1 hCA') hLoc'' hLoc Y).2 ⟨w, hmk, fun u => hyj u⟩
  refine ⟨Y, hfixL, ?_, by simpa using hmem.2⟩
  have h1 := hmem.1
  simp only [Set.mem_setOf_eq]
  simpa [mul_inv_rev, _root_.mul_assoc] using h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

abbrev Loc (G : HTGroup p) : Type := (w : Fin G.m) → Fin G.n → G.Fw w

def IntL (z : Loc G) : Prop := ∀ w i, ‖(z w i : PadicAlgCl p)‖ ≤ 1

def pairL (a b : Loc G) : ℚ_[p] := ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (a w ⬝ᵥ b w)

structure PFrame (β : G.Cˣ) where
  T : VQ D →+ Loc G
  T' : VQ D →+ Loc G
  act : ∀ (c : G.C) x w, T (L.rep c x) w = G.rho w c *ᵥ T x w
  act' : ∀ (c : G.C) x w, T' (L.rep c x) w = (G.rho w ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ T' x w
  form : ∀ u x, ((formB L β u x : ℚ) : ℚ_[p]) = pairL (T' x) (T u) - pairL (T' u) (T x)
  dense : ∀ (a b : Loc G) (k : ℕ), ∃ x a' b', IntL a' ∧ IntL b' ∧ T x = a + p ^ k • a' ∧ T' x = b + p ^ k • b'
  bound : ∃ (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ ∧
    ∀ x, IntL (T x) → IntL (T' x) → ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))

variable {L}

def PFrame.Mem {β : G.Cˣ} (A : PFrame L β) (g : Gp G) (x : VQ D) : Prop :=
  IntL (fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w) ∧
    ∀ z : Loc G, IntL z → ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w)‖ ≤ 1

def IntPt (g : Gp G) : Prop :=
  ‖(g.1 : ℚ_[p])‖ = 1 ∧ ∀ w i j, ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1 ∧
    ‖((((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHeckeCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.heckeCoord_of :
    UpperTheory.Gal.W2.IsogAt → UpperTheory.Gal.W2.IsogCoord → UpperTheory.Gal.W2.HeckeCoord := by
  intro hA hC p _ D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU B j h₁ M hpl hco hloc
  obtain ⟨D'', t'', P'', e'', inc, d, hcls, hU'', hP, he, hd, hinc, f, nu, f'', nu'', hw, hw'', hf, hf'', hiff⟩ :=
    hA p D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU
  obtain ⟨h3, hNp, h3', hNp', -, hK⟩ := hlev
  obtain ⟨j'', hj, hpl'', hco'', hloc''⟩ :=
    hC p D G L B N N' (by omega) hNp (by omega) hNp' h hK ρ D' t D'' t'' P P'' inc d hU.2.1 hU''.2.1 hP hd hinc
      f nu f'' nu'' hw hw'' hf hf'' hiff j h₁ M hpl hco hloc
  refine ⟨D'', t'', P'', e'', inc, j'', hcls, hU'', hP, he, ?_, hj, hpl'', hco'', hloc''⟩
  intro u''
  obtain ⟨u, hu⟩ := hinc u''
  refine ⟨d, u, ?_, hu⟩
  rintro rfl
  have hp : p = 1 := by simpa using hd
  exact (Fact.out : p.Prime).one_lt.ne' hp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHermOfJ
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.hermOfJ_of :
    UpperTheory.Gal.W2.HermOfJ := by
  intro g E halt hI hpos
  have hskew : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
    linarith
  have hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x := by
    intro x
    rw [smul_smul, Complex.I_mul_I]
    simp
  have hcomm : ∀ x y : Fin g → ℂ, E (Complex.I • x) y = E (Complex.I • y) x := by
    intro x y
    have h := hI (Complex.I • x) y
    rw [hII, map_neg, LinearMap.neg_apply] at h
    rw [← h, hskew x]
    ring
  let H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y => ⟨E (Complex.I • x) y, E x y⟩
  have hsym : ∀ x y, H y x = star (H x y) := by
    intro x y
    apply Complex.ext
    · simpa [H] using hcomm y x
    · simpa [H] using hskew y x
  have hadd : ∀ a b y, H (a + b) y = H a y + H b y := by
    intro a b y
    apply Complex.ext <;> simp [H, smul_add]
  have hsmulI : ∀ x y, H (Complex.I • x) y = Complex.I * H x y := by
    intro x y
    apply Complex.ext
    · simp [H, hII]
    · simp [H]
  have hsmulR : ∀ (r : ℝ) x y, H (r • x) y = (r : ℂ) * H x y := by
    intro r x y
    apply Complex.ext
    · simp [H, smul_comm Complex.I r x]
    · simp [H]
  have hsmul : ∀ (c : ℂ) x y, H (c • x) y = c * H x y := by
    intro c x y
    have hc : c • x = c.re • x + c.im • (Complex.I • x) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hc, hadd, hsmulR, hsmulR, hsmulI]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let e : Fin g → Fin g → ℂ := fun i j => if i = j then 1 else 0
  have hexp : ∀ x y, H x y = ∑ i, x i * H (e i) y := by
    intro x y
    let f : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun x => H x y
        map_add' := fun a b => hadd a b y
        map_smul' := fun c a => by simpa using hsmul c a y }
    simpa [f, e] using LinearMap.pi_apply_eq_sum_univ f x
  have hform : ∀ x y, hermForm (Matrix.of fun i j => H (e i) (e j)) x y = H x y := by
    intro x y
    rw [hexp x y]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hsym y (e i), hexp y (e i), star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', ← hsym (e j) (e i), mul_comm]
  refine ⟨Matrix.of fun i j => H (e i) (e j), ?_, ?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.of_apply]
    rw [← hsym]
  · intro z hz
    rw [hform]
    exact hpos z hz
  · intro x y
    rw [hform]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowCorr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powCorr_of :
    UpperTheory.Gal.W2.PwOver → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PowCorr := by
  intro hPw hPt p _ D G L gb N N' h X X' c₁ c₂ ρ D' S hact ga hcomp k α
  have w₁ := hPw p D G L gb N N' 1 X X' c₁ k
  have w₂ := hPw p D G L gb N N' h X X' c₂ k
  refine ⟨?_, ?_⟩
  · intro P P'' hP hP'' hga z
    obtain ⟨hu, hex⟩ := hcomp P P'' hP hP'' hga
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    have f'' := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P'' hP''
    apply KS.PowPB.pow_left_hom_ext
    · simp only [Category.assoc, (w₂.2.2.2 α).1, w₁.1]
      simp only [← Category.assoc, f.1, f''.1]
      exact hu
    · intro i
      simp only [Category.assoc, (w₂.2.2.2 α).2 i, w₁.2.1 i]
      simp only [← Category.assoc, f.2.1, f''.2.1]
      rw [hex, Category.assoc, ← w₁.2.2.1, ← Category.assoc, ← hact P'' hP'']
      rfl
  · intro P hP hinj z z' heq
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    refine (f.2.2.2.1 z z').2 (fun j => hinj (z j) (z' j) ?_)
    have e := congrArg (· ≫ Over.Hom.left (KS.pr X.univ.A j)) heq
    simp only [Category.assoc, w₁.2.1 j] at e
    simpa only [← Category.assoc, f.2.1] using e
end

