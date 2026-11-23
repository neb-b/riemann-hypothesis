module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CongruenceIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CongruenceIndex.mul_mulVec (γ δ : GL (Fin r) E) (v : Fin r → E) :
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]


open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.isUStab_one : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ 1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab
  exact ⟨fun x y => by simp, fun x => by simp⟩

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.isUStab_mul {γ δ : GL (Fin r) E} (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ) (hδ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ δ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ (γ * δ) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec, _root_.GlobalTheory.CongruenceIndex.mul_mulVec, hγ.1, hδ.1]
  · rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec]
    exact (hδ.2 x).trans (hγ.2 _)

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.isUStab_inv {γ : GL (Fin r) E} (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ⁻¹ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h := hγ.1 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
    rw [_root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec, _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec] at h
    exact h.symm
  · have h := hγ.2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
    rw [_root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec] at h
    exact h.symm

def congruenceSubgroup (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (M : ℕ) : Subgroup (GL (Fin r) E) where
  carrier := {γ | FD.IsUStab Gm Λ γ ∧
    (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)}
  one_mem' := ⟨isUStab_one, fun v _ => ⟨0, Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro γ δ ⟨hγ, hγ'⟩ ⟨hδ, hδ'⟩
    refine ⟨isUStab_mul hγ hδ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hδ' v hv
    obtain ⟨w', hw', e'⟩ := hγ' _ ((hδ.2 v).1 hv)
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [mul_mulVec, e', e, smul_add, add_assoc]
  inv_mem' := by
    rintro γ ⟨hγ, hγ'⟩
    refine ⟨isUStab_inv hγ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hγ' _ (((isUStab_inv hγ).2 v).1 hv)
    rw [mulVec_inv_mulVec] at e
    refine ⟨-w, Λ.neg_mem hw, ?_⟩
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact e.symm

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
private theorem inv_mul_mem_congruenceSubgroup_of_agree_mod {T : Finset (Fin r → E)}
    (hT : Submodule.span (𝓞 E) (T : Set (Fin r → E)) = Λ) {M : ℕ} {s γ : GL (Fin r) E}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ s) (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ)
    (h : ∀ t ∈ T, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t =
      (s : Matrix (Fin r) (Fin r) E) *ᵥ t + M • w) :
    s⁻¹ * γ ∈ _root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M := by
  have hsi := _root_.GlobalTheory.CongruenceIndex.isUStab_inv hs
  refine ⟨_root_.GlobalTheory.CongruenceIndex.isUStab_mul hsi hγ, fun v hv => ?_⟩
  rw [← hT] at hv
  induction hv using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨w, hw, e⟩ := h t ht
    refine ⟨((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w, (hsi.2 w).1 hw, ?_⟩
    have hst := _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec s⁻¹ t
    rw [inv_inv] at hst
    rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec, e, Matrix.mulVec_add, hst, Matrix.mulVec_smul]
  | zero => exact ⟨0, Λ.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, ex⟩ := hx
    obtain ⟨w', hw', ey⟩ := hy
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [Matrix.mulVec_add, ex, ey, smul_add]
    abel
  | smul a x _ hx =>
    obtain ⟨w, hw, ex⟩ := hx
    refine ⟨a • w, Λ.smul_mem a hw, ?_⟩
    rw [Matrix.mulVec_smul, ex, smul_add, smul_comm a M w]

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.exists_finset_cosets (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ →
      ∃ s ∈ S, s⁻¹ * γ ∈ _root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M := by
  classical
  obtain ⟨T, hT⟩ := id hΛ
  set I : Ideal (𝓞 E) := Ideal.span {(M : 𝓞 E)} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  haveI : Subsingleton (Λ ⧸ (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  haveI : Finite (Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  let St := {γ : GL (Fin r) E // _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ}
  let Φ : St → (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := fun γ t =>
    Submodule.Quotient.mk ⟨(γ.1 : Matrix (Fin r) (Fin r) E) *ᵥ t.1,
      (γ.2.2 t.1).1 (hT ▸ Submodule.subset_span t.2)⟩
  haveI : Fintype (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) := Fintype.ofFinite _
  let rep : (T → Λ ⧸ I • (⊤ : Submodule (𝓞 E) Λ)) → GL (Fin r) E := fun x =>
    if h : ∃ γ : St, Φ γ = x then h.choose.1 else 1
  refine ⟨Finset.univ.image rep, fun γ hγ =>
    ⟨rep (Φ ⟨γ, hγ⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
  have hex : ∃ δ : St, Φ δ = Φ ⟨γ, hγ⟩ := ⟨_, rfl⟩
  have hrep : rep (Φ ⟨γ, hγ⟩) = hex.choose.1 := dif_pos hex
  rw [hrep]
  refine inv_mul_mem_congruenceSubgroup_of_agree_mod hT hex.choose.2 hγ (fun t ht => ?_)
  have hq := congrFun hex.choose_spec ⟨t, ht⟩
  have hmem := (Submodule.Quotient.eq _).1 hq.symm
  have hdiv : ∀ x : Λ, x ∈ I • (⊤ : Submodule (𝓞 E) Λ) → ∃ b : Λ, (M : 𝓞 E) • b = x := by
    intro x hx
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hdiv _ hmem
  refine ⟨b.1, b.2, ?_⟩
  have hb' := congrArg Subtype.val hb
  simp only [Submodule.coe_smul, Submodule.coe_sub] at hb'
  rw [Nat.cast_smul_eq_nsmul] at hb'
  rw [hb']
  abel


open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.congruence_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → 0 < M → ∃ Γ : Subgroup (GL (Fin r) E), (∀ γ, γ ∈ Γ ↔ _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ := by
  intro E _ _ _ r M Gm Λ hΛ hM
  exact ⟨_root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M, fun γ => Iff.rfl,
    _root_.GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM⟩

end GlobalTheory.CongruenceIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqIffConjNe
section
namespace GlobalTheory.ConjugateMembership

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_neg_of_sq {x : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) x = -x := by
  have hre : x.re * x.re - x.im * x.im = -d := by
    have := congrArg Complex.re hx
    simpa [sq] using this
  have him : x.re * x.im + x.im * x.re = 0 := by
    have := congrArg Complex.im hx
    simpa [sq] using this
  have h0 : x.re = 0 := by
    by_contra h
    have hi : x.im = 0 := by
      have h2 : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left h
    rw [hi] at hre
    nlinarith [mul_self_nonneg x.re]
  apply Complex.ext <;> simp [h0]

theorem eq_iff_conj_ne {x r : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) (hr : r ^ 2 = -(d : ℂ)) :
    x = r ↔ ¬ (starRingEnd ℂ) x = r := by
  rw [conj_eq_neg_of_sq hd hx]
  constructor
  · rintro rfl h
    have h0 : x = 0 := by linear_combination (-1 / 2 : ℂ) * h
    rw [h0] at hx
    have : (d : ℂ) = 0 := by linear_combination hx
    exact hd.ne' (by exact_mod_cast this)
  · intro h
    have : (x - r) * (-x - r) = 0 := by linear_combination hr - hx
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd (sub_eq_zero.1 h1) h

theorem mem_iff_conjugate_notMem {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hx : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [← map_pow, hE]; simp
  have hr : H.rt0 ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [H.sqrt_neg_disc_sq]; simp
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  exact eq_iff_conj_ne hd hx hr

end GlobalTheory.ConjugateMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LevelHalf


open NumberField Matrix in
open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
      (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        ∃ e, gam a = a + l.M • e) → ∀ a, ∃ e, gam a = a + l.M • e := by
  intro E _ _ _ H D l gam hiso hhalf x
  cases D with
  | mk La _ _ EF _ hbij hbar _ _ _ _ => ?_
  obtain ⟨M, _, _, Mb, _, _, hsup, _, _⟩ := l
  dsimp only at *
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp
    (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ Mb ⊔ Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  set y := gam x - x with hy
  obtain ⟨e₁, he₁⟩ := hhalf (j • x) (Submodule.smul_mem_smul hj Submodule.mem_top)
  have hjy : j • y = M • e₁ := by
    rw [hy, smul_sub, ← LinearEquiv.map_smul, he₁]
    abel
  have hdiv : ∀ z, (M : ℤ) ∣ EF (i • y) z := by
    intro z
    rw [hbar]
    have hmem : H.bar i ∈ Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hi
    obtain ⟨e₂, he₂⟩ := hhalf (H.bar i • z) (Submodule.smul_mem_smul hmem Submodule.mem_top)
    refine ⟨-EF (gam x) e₂, ?_⟩
    rw [hy, map_sub, LinearMap.sub_apply, ← hiso x (H.bar i • z), he₂, map_add (f := _), map_nsmul,
      nsmul_eq_mul]
    ring
  let ψ : La →ₗ[ℤ] ℤ :=
    { toFun := fun z => EF (i • y) z / M
      map_add' := fun a b => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hdiv a)
      map_smul' := fun c a => by
        simp only [map_zsmul, smul_eq_mul, eq_intCast, Int.cast_id]
        exact Int.mul_ediv_assoc _ (hdiv a) }
  obtain ⟨w, hw⟩ := hbij.2 ψ
  have hiy : i • y = M • w := by
    apply hbij.1
    ext z
    rw [map_nsmul, LinearMap.smul_apply, hw]
    simp [ψ, nsmul_eq_mul, Int.mul_ediv_cancel' (hdiv z)]
  refine ⟨e₁ + w, ?_⟩
  calc gam x = x + y := by rw [hy]; abel
    _ = x + M • (e₁ + w) := by
      rw [smul_add, ← hjy, ← hiy, add_comm (j • y), ← add_smul, hij, one_smul]

end GlobalTheory.LevelHalf
end

