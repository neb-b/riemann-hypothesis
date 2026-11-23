module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.FockMonomialRight

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Monomial
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def varE (p : ℕ) (x : D.ML × Fin D.r) : D.EA :=
  Sum.elim (fun b => Finsupp.single (Sum.inl b, x.2) 1)
    (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) 1)
      (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) (D.P p t))
        (fun t => Finsupp.single (Sum.inr t, x.2) 1))) x.1

theorem ph_X (p : ℕ) (x : D.ML × Fin D.r) :
    D.ph p (X x : MvPolynomial (D.ML × Fin D.r) K) = monomial (D.varE p x) 1 := by
  obtain ⟨i, a⟩ := x
  unfold ph
  rw [aeval_X]
  rcases i with b | t | t | t <;> simp [varE, X, monomial_pow]

theorem phE_apply_inl (p : ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.phE p ζ (Sum.inl b, a) = ζ (D.mb b, a) := by
  simp [phE, collapseExponent, tpE]

theorem phE_apply_inr (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.phE p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) + ζ (D.mtp t, a) := by
  simp [phE, collapseExponent, tpE]

theorem phE_eq_sum (p : ℕ) (ζ : D.EM) : D.phE p ζ = ζ.sum fun x k => k • D.varE p x := by
  classical
  ext ⟨i, a⟩
  rw [Finsupp.sum_fintype _ _ (by intro x; simp), Finsupp.finsetSum_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rcases i with b | t
  · rw [phE_apply_inl]
    simp [varE, Finsupp.single_apply, mb, ite_and]
  · rw [phE_apply_inr]
    simp only [varE, Sum.elim_inl, Sum.elim_inr, Finsupp.smul_apply, Finsupp.single_apply, Prod.mk.injEq,
      Sum.inr.injEq, reduceCtorEq, false_and, if_false, Finset.sum_const_zero, zero_add,
      ite_and, smul_eq_mul, mul_ite, mul_one, mul_zero, mlab, mw, mtp]
    have key : ∀ f : D.Tau → Fin D.r → ℕ,
        (∑ x, ∑ y, if x = t then (if y = a then f x y else 0) else 0) = f t a := by
      intro f
      rw [Finset.sum_eq_single t (by intro x _ hx; simp [hx]) (by simp)]
      simp
    rw [key, key, key]
    ring

theorem ph_monomial (p : ℕ) (ζ : D.EM) (c : K) :
    D.ph p (monomial ζ c) = monomial (D.phE p ζ) c := by
  classical
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, phE_eq_sum]
  simp only [map_pow, ph_X, monomial_pow, one_pow]
  rw [show D.ph p (C c) = C c from (D.ph p).commutes c]
  rw [Finsupp.sum, ← monomial_sum_one, C_mul_monomial, mul_one]

theorem ldeg_phE (p : ℕ) (ζ : D.EM) (h : D.GoodE p ζ) (i : D.OL) : ldeg (D.phE p ζ) i = D.dO i := by
  obtain ⟨-, -, h3, h4, -⟩ := h
  rcases i with b | t
  · simp only [ldeg, phE_apply_inl, dO, Sum.elim_inl]
    exact h3 b
  · simp only [ldeg, phE_apply_inr, dO, Sum.elim_inr, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact h4 t

theorem Good.add {p : ℕ} {Z W : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (hW : D.Good p W) :
    D.Good p (Z + W) := by
  classical
  intro ζ hζ
  rcases Finset.mem_union.mp (support_add hζ) with h | h
  · exact hZ ζ h
  · exact hW ζ h

theorem Good.smul {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (a : K) :
    D.Good p (a • Z) := fun ζ hζ => hZ ζ (support_smul hζ)

theorem Good.zero (p : ℕ) : D.Good p (0 : MvPolynomial (D.ML × Fin D.r) K) := by
  intro ζ hζ; simp at hζ

theorem Good.sum {p : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (D.ML × Fin D.r) K)
    (h : ∀ i ∈ s, D.Good p (f i)) : D.Good p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.zero D p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Good.add D (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Good.monomial {p : ℕ} {ζ : D.EM} (h : D.GoodE p ζ) (c : K) : D.Good p (monomial ζ c) := by
  classical
  intro ζ' hζ'
  have := support_monomial_subset hζ'
  rw [Finset.mem_singleton] at this
  rw [this]; exact h

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.PrimedEmbeddingInjective
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def embU (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (x : D.OL × Fin D.r) (ζ : D.EM) : ℕ :=
  Sum.elim (fun b => ζ (D.mb b, x.2)) (fun t => ρ t x.2 + D.P p t * ζ (D.mw t, x.2)) x.1

def embE (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => D.embU p ρ x ζ

theorem substituted_exponent_eq_embedded (p : ℕ) (ζ : D.EM) : D.collapseExponent p ζ = D.embE p (D.labF ζ) ζ := rfl

def gaR (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ρ : D.Tau → Fin D.r → ℕ) (ε : ℤ)
    (ζ : D.EM) : K :=
  D.ga (D.embE p ρ ζ) ^ ε * ∏ t, gam t (ρ t) (D.wF ζ t) ^ ε

theorem gaR_one (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) 1 ζ = D.gaP p gam ζ := by
  simp only [gaR, gaP, zpow_one, substituted_exponent_eq_embedded]

theorem gaR_neg_one (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) (-1) ζ = (D.gaP p gam ζ)⁻¹ := by
  simp only [gaR, gaP, zpow_neg_one, substituted_exponent_eq_embedded, Finset.prod_inv_distrib, mul_inv]

end TwistData

section

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

abbrev CostM (D : TwistData K) : ℕ → (D.EM → K) → Prop := CostV (K := K) (r := D.r) D.msg Set.univ

theorem costM_ok (D : TwistData K) : CostOK (CostM D) :=
  costV_ok _ _ (fun _ _ _ _ _ h1 h2 => vala_add h1 h2) (fun _ _ _ a _ h => vala_smul a h)

theorem costM_choose (hV2 : V2 K) (D : TwistData K) (hr : 0 < D.r) (x : D.ML × Fin D.r) (k : ℕ) :
    CostM D k (fun α => ((α x).choose k : K)) := by
  haveI : NeZero D.r := ⟨hr.ne'⟩
  intro S _ θ F h
  exact vala_dg_choose hV2 x k h

theorem exists_approx_gaR (hV2 : V2 K) (D : TwistData K) (hV : D.Valid v p)
    (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K)
    (hDig : D.DigOK v p cst gam) (ρ : D.Tau → Fin D.r → ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ g : D.EM → K, (∀ ζ, 0 ≤ v (g ζ)) ∧ CostM D (12 * D.c) g ∧
      ((∀ t a, ρ t a < D.P p t) → ∀ ζ, ((D.c : ℕ) : WithTop ℚ) ≤ v (D.gaR p gam ρ ε ζ - g ζ)) := by
  have hC := costM_ok D
  have hch := costM_choose hV2 D hV.1
  by_cases hρ : ∀ t a, ρ t a < D.P p t
  · obtain ⟨hga0, hga⟩ := hV.2.2.2.2.2.2
    obtain ⟨T, lam, hlam, hcong⟩ := hga ε hε
    obtain ⟨g1, a1, a2, a3⟩ := approx_of_trunc_gen (v := v) hC (D.embU p ρ) (by
        rintro ⟨i, a⟩ k
        rcases i with b | t
        · exact hch (D.mb b, a) k
        · exact cost_choose_affine hC (fun ζ => ζ (D.mw t, a)) (hch (D.mw t, a)) (ρ t a) (D.P p t) k)
      T lam hlam (fun ζ => D.ga (D.embE p ρ ζ) ^ ε) (fun ζ => hcong (D.embE p ρ ζ))
    obtain ⟨T', lam', hlam', hcong'⟩ := hDig.2 ρ hρ ε hε
    obtain ⟨g2, b1, b2, b3⟩ := approx_of_trunc_gen (v := v) hC
      (fun (x : D.Tau × Fin D.r) (ζ : D.EM) => ζ (D.mw x.1, x.2)) (fun x k => hch (D.mw x.1, x.2) k)
      T' lam' hlam' (fun ζ => (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε)
      (fun ζ => hcong' (fun x => ζ (D.mw x.1, x.2)))
    have u2 : ∀ ζ : D.EM, v ((∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε) = 0 := fun ζ =>
      v_unit_zpow v (Finset.prod_induction _ (fun x => v x = 0) (fun a b ha hb => v_unit_mul v ha hb)
        v.map_one fun t _ => ((hDig.1 t (ρ t) (hρ t)).2 _).1) ε
    refine ⟨fun ζ => g1 ζ * g2 ζ, fun ζ => v_mul_nonneg (a1 ζ) (b1 ζ), ?_, fun _ ζ => ?_⟩
    · have := hC.mul _ _ _ _ a3 b3
      have e : 6 * D.c + 6 * D.c = 12 * D.c := by ring
      rwa [e] at this
    · have e : D.gaR p gam ρ ε ζ - g1 ζ * g2 ζ =
          (D.ga (D.embE p ρ ζ) ^ ε - g1 ζ) * (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε +
            g1 ζ * ((∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε - g2 ζ) := by
        have e2 : ∏ t, gam t (ρ t) (D.wF ζ t) ^ ε = (∏ t, gam t (ρ t) (D.wF ζ t)) ^ ε :=
          Finset.prod_zpow _ _ _
        simp only [TwistData.gaR]
        rw [e2]; ring
      rw [e]
      exact v_add_ge (v_mul_ge_left (a2 ζ) (u2 ζ).ge) (v_mul_ge_right (a1 ζ) (b2 ζ))
  · refine ⟨fun _ => 1, fun _ => by simp, ?_, fun h => absurd h hρ⟩
    exact hC.mono 0 _ _ (Nat.zero_le _) hC.one

theorem eOut_of_mem_image {L : Type} [DecidableEq L] {r : ℕ} (out : L → Prop) [DecidablePred out]
    (F : MvPolynomial (L × Fin r) K) {μ : L × Fin r →₀ ℕ} (hμ : μ ∈ F.support.image (eOut out)) :
    eOut out μ = μ := by
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hμ
  exact eOut_eOut out α

theorem vala_dg_labels (D : TwistData K) (gg : (D.Tau → Fin D.r → ℕ) → D.EM → K) (n : ℕ)
    (hgg : ∀ ρ, CostM D n (gg ρ)) (S : Finset D.ML) (hS : ∀ t, D.mlab t ∉ S) (θ : ℝ)
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : vala D.msg S θ Z) :
    vala D.msg S (θ - n) (dg (fun ζ => gg (D.labF ζ) ζ) Z) := by
  set out : D.ML → Prop := fun i => ∃ t, i = D.mlab t with hout
  letI : DecidablePred out := Classical.decPred _
  have hoS : ∀ i ∈ S, ¬ out i := by
    rintro i hi ⟨t, rfl⟩; exact hS t hi
  set_option synthInstance.maxHeartbeats 100000 in
    conv => rw [sum_coefOut out Z, map_sum]
  refine vala_sum _ _ fun μ hμ => ?_
  have e : dg (fun ζ => gg (D.labF ζ) ζ) (monomial μ 1 * coefOut out μ Z) =
      dg (gg (D.labF μ)) (monomial μ 1 * coefOut out μ Z) := by
    refine dg_congr fun α hα => ?_
    have hlab : D.labF α = D.labF μ := by
      rw [mem_support_iff, coeff_monomial_mul'] at hα
      by_cases hle : μ ≤ α
      · rw [if_pos hle, one_mul] at hα
        have h0 := eOut_eq_zero_of_mem_support_coefOut out (mem_support_iff.mpr hα)
        funext t a
        have h1 : (α - μ) (D.mlab t, a) = 0 := by
          have := DFunLike.congr_fun h0 (D.mlab t, a)
          rw [eOut_apply, if_pos ⟨t, rfl⟩] at this
          simpa using this
        have h2 : μ (D.mlab t, a) ≤ α (D.mlab t, a) := hle _
        rw [Finsupp.tsub_apply] at h1
        simp only [TwistData.labF]
        omega
      · rw [if_neg hle] at hα; exact absurd rfl hα
    rw [hlab]
  rw [e]
  refine hgg _ S (Set.mem_univ _) θ _ ?_
  refine vala_mul_left_nonneg (valS_monomial_nonneg_of_free _ _ ?_) (vala_coefOut out hoS _ hZ)
  intro i hi a
  rw [← eOut_of_mem_image out Z hμ, eOut_apply, if_neg (hoS i hi)]

theorem stepG_of (hV2 : V2 K) : StepG K v p := by
  intro _hD D hV cst gam hDig
  have Hp := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ 1 (Or.inl rfl)
  have Hm := fun ρ => exists_approx_gaR hV2 D hV cst gam hDig ρ (-1) (Or.inr rfl)
  choose gp hp1 hp2 hp3 using Hp
  choose gm hm1 hm2 hm3 using Hm
  refine ⟨fun ζ => gp (D.labF ζ) ζ, fun ζ => gm (D.labF ζ) ζ, fun ζ => hp1 _ ζ, fun ζ => hm1 _ ζ, ?_, ?_⟩
  · intro ζ hζ
    constructor
    · have := hp3 (D.labF ζ) hζ ζ
      rw [D.gaR_one, AddValuation.map_sub_swap] at this
      exact this
    · have := hm3 (D.labF ζ) hζ ζ
      rw [D.gaR_neg_one, AddValuation.map_sub_swap] at this
      exact this
  · intro S hS θ Z hZ
    have e : θ - 12 * (D.c : ℝ) = θ - ((12 * D.c : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    exact ⟨vala_dg_labels D gp _ hp2 S hS θ Z hZ, vala_dg_labels D gm _ hm2 S hS θ Z hZ⟩

end

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ProjKeepsLetter
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

section Generic

variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)

theorem fock_proj_right {W : Set (MvPolynomial (L × Fin r) K)}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d W π) {A G : MvPolynomial (L × Fin r) K}
    (hA : A ∈ PolK K r d) (hAW : A ∈ W) (hG : G ∈ PolK K r d) : fock A (π G) = fock A G := by
  have h := (hπ G hG).2.2.2 A hA hAW
  rw [fock_sub_left] at h
  rw [fock_comm A (π G), fock_comm A G]
  exact (sub_eq_zero.mp h).symm

theorem proj_preserves (hP : PROJ K v p C0) (hD : DVRHyp v p) {S S'' : Finset L} {th th'' : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π)
    (hS : S ⊆ S'' ∨ S'' ⊆ S ∨ Disjoint S S'') {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) (hFW : F ∈ Aset sg S'' th'') : π F ∈ Aset sg S'' th'' := by
  obtain ⟨⟨π'', hπ''⟩, -⟩ := hP hD L sg r d S'' th''
  have hfix : π'' F = F := (hπ'' F hF).2.2.1 hFW
  have hcomm : π (π'' F) = π'' (π F) := by
    rcases hS with h | h | h
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inl h) th'' π'' hπ'' F hF
    · exact (((hP hD L sg r d S'' th'').2 π'' hπ'').2.1 S (Or.inl h) th π hπ F hF).symm
    · exact ((hP hD L sg r d S th).2 π hπ).2.1 S'' (Or.inr h) th'' π'' hπ'' F hF
  have hE : π F = π'' (π F) := by rw [← hcomm, hfix]
  rw [hE]
  exact (hπ'' (π F) (hπ F hF).1).2.1

theorem bge_proj (hP : PROJ K v p C0) (hD : DVRHyp v p) {S : Finset L} {th : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π) {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) {a : ℝ} (ha : bge v a F) :
    bge v (a - (r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i)) (π F) := by
  rw [bge_iff] at ha ⊢
  have hb := ((hP hD L sg r d S th).2 π hπ).2.2 F hF
  have h2 := ha.trans hb
  generalize vBB v (π F) = x at h2 ⊢
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe]
    linarith

theorem prodProj (hP : PROJ K v p C0) (hD : DVRHyp v p) {ι : Type} (s : Finset ι)
    (S : ι → Finset L) (th : ι → ℤ)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, S x ⊆ S y ∨ S y ⊆ S x ∨ Disjoint (S x) (S y)) :
    ∃ Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K,
      (∀ F ∈ PolK K r d, Pr F ∈ PolK K r d) ∧
      (∀ F ∈ PolK K r d, ∀ x ∈ s, Pr F ∈ Aset sg (S x) (th x)) ∧
      (∀ A ∈ PolK K r d, (∀ x ∈ s, A ∈ Aset sg (S x) (th x)) →
        ∀ G ∈ PolK K r d, fock A (Pr G) = fock A G) ∧
      (∀ F ∈ PolK K r d, ∀ a : ℝ, bge v a F →
        bge v (a - s.card * ((r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i))) (Pr F)) ∧
      (∀ (S'' : Finset L) (th'' : ℤ), (∀ x ∈ s, S x ⊆ S'' ∨ Disjoint (S x) S'') →
        ∀ F ∈ PolK K r d, F ∈ Aset sg S'' th'' → Pr F ∈ Aset sg S'' th'') ∧
      (∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨LinearMap.id, fun F hF => hF, fun F _ x hx => by simp at hx, fun A _ _ G _ => rfl, ?_,
      fun S'' th'' _ F _ hFW => hFW, fun i _ _ a F _ => rfl⟩
    intro F _ a ha
    simpa using ha
  | @insert x s hx ih =>
    have hpair' : ∀ y ∈ s, ∀ z ∈ s, S y ⊆ S z ∨ S z ⊆ S y ∨ Disjoint (S y) (S z) :=
      fun y hy z hz => hpair y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz)
    obtain ⟨Pr, h1, h2, h3, h4, h5, h6⟩ := ih hpair'
    obtain ⟨⟨πx, hπx⟩, -⟩ := hP hD L sg r d (S x) (th x)
    have hPx := (hP hD L sg r d (S x) (th x)).2 πx hπx
    refine ⟨πx ∘ₗ Pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro F hF
      exact (hπx _ (h1 F hF)).1
    · intro F hF y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hπx _ (h1 F hF)).2.1
      · exact proj_preserves sg d hP hD hπx
          (hpair _ (Finset.mem_insert_self _ s) y (Finset.mem_insert_of_mem hy)) (h1 F hF) (h2 F hF y hy)
    · intro A hA hAW G hG
      rw [LinearMap.comp_apply,
        fock_proj_right d hπx hA (hAW x (Finset.mem_insert_self x s)) (h1 G hG)]
      exact h3 A hA (fun y hy => hAW y (Finset.mem_insert_of_mem hy)) G hG
    · intro F hF a ha
      have hb := bge_proj sg d hP hD hπx (h1 F hF) (h4 F hF a ha)
      rw [LinearMap.comp_apply]
      refine bge_mono v ?_ hb
      rw [Finset.card_insert_eq_ite, if_neg hx]
      apply le_of_eq
      push_cast
      ring
    · intro S'' th'' hS F hF hFW
      have hPr := h5 S'' th'' (fun y hy => hS y (Finset.mem_insert_of_mem hy)) F hF hFW
      rw [LinearMap.comp_apply]
      rcases hS x (Finset.mem_insert_self x s) with h | h
      · exact proj_preserves sg d hP hD hπx (Or.inl h) (h1 F hF) hPr
      · exact proj_preserves sg d hP hD hπx (Or.inr (Or.inr h)) (h1 F hF) hPr
    · intro i hi hout a F hF
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        h6 i hi (fun y hy => hout y (Finset.mem_insert_of_mem hy)) a F hF]
      exact hPx.1 i hi (hout x (Finset.mem_insert_self x s)) a (Pr F) (h1 F hF)

end Generic

section Torus

variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}

theorem euler_eq_dg {σ : Type} (x : σ) (G : MvPolynomial σ K) :
    X x * pderiv x G = dg (fun ξ => (ξ x : K)) G := by
  refine MvPolynomial.induction_on' G (fun α c => ?_) (fun P Q hP hQ => ?_)
  · rw [MvPolynomial.X_mul_pderiv_monomial, dg_monomial, MvPolynomial.smul_monomial, nsmul_eq_mul]
  · rw [map_add (f := _), mul_add, hP, hQ, map_add (f := _)]

private theorem coeff_dg_eq_mul_coeff {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K)
    (α : σ →₀ ℕ) : (dg f F).coeff α = f α * F.coeff α := by
  classical
  rw [dg_eq_sum_f, MvPolynomial.coeff_sum]
  by_cases h : α ∈ F.support
  · rw [Finset.sum_eq_single α (fun β _ hβ => by rw [MvPolynomial.coeff_monomial, if_neg hβ])
      (fun h' => absurd h h'), MvPolynomial.coeff_monomial, if_pos rfl]
  · have h0 : F.coeff α = 0 := by simpa using h
    rw [h0, mul_zero]
    exact Finset.sum_eq_zero (fun β hβ => by
      rw [MvPolynomial.coeff_monomial, if_neg (fun (e : β = α) => h (e ▸ hβ))])

theorem proj_keeps_letter (d : L → ℕ)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) (i : L)
    (hcomm : ∀ (a : Fin r), ∀ F ∈ PolK K r d,
      Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) (a : Fin r) : ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d := by
    rw [mem_PolK_iff]
    intro α hα k
    have hαζ : α = ζ := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hα
      exact hα rfl
    rw [hαζ]
    exact hζ k
  have h := hcomm a _ hmono
  rw [euler_eq_dg, euler_eq_dg] at h
  simp only [dg_monomial, mul_one] at h
  have h' := congrArg (fun G => AddMonoidAlgebra.coeff G ζ') h
  simp only [coeff_dg_eq_mul_coeff] at h'
  have hsm : (monomial ζ ((ζ (i, a) : ℕ) : K) : MvPolynomial (L × Fin r) K) =
      ((ζ (i, a) : ℕ) : K) • monomial ζ (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h'
  have hne : (Pr (monomial ζ 1)).coeff ζ' ≠ 0 := by simpa using hζ'
  have hc := mul_right_cancel₀ hne h'
  exact_mod_cast hc.symm

end Torus

theorem prodProj_entries {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r]
    (d : L → ℕ) {ι : Type} (s : Finset ι) (S : ι → Finset L)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K)
    (h1 : ∀ F ∈ PolK K r d, Pr F ∈ PolK K r d)
    (h6 : ∀ i : L, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) :
    (∀ k, ldeg ζ' k = d k) ∧
      ∀ i, sg i = true → (∀ x ∈ s, i ∉ S x) → ∀ a, ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d := by
    rw [mem_PolK_iff]
    intro α hα k
    have hαζ : α = ζ := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hα
      exact hα rfl
    rw [hαζ]
    exact hζ k
  exact ⟨fun k => (mem_PolK_iff d _).mp (h1 _ hmono) ζ' hζ' k,
    fun i hi hout a => proj_keeps_letter d Pr i (h6 i hi hout) ζ hζ ζ' hζ' a⟩

end Formalism.MainNotions.PlaneGram
end
end

