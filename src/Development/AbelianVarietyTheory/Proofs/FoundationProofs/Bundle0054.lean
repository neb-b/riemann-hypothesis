module

public import Mathlib
public import GroundTheory.PAdicHodge.AxLemma
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineFunctionalEqPeriodMul
section
open TensorProduct GroundTheory.PAdicHodge UniformSpace

namespace GlobalTheory

theorem line_functional_eq_period_mul : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
  (g : S → Module.End ℤ_[l] M) (ρ : S → Matrix (Fin 2) (Fin 2) (PadicAlgCl l))
  (L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l]) (F : Finset (PadicAlgCl l)),
  (∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ a ∈ F, a ∈ K) → ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l,
    ∃ s, ∀ b ∈ B, L (1 ⊗ₜ[ℤ_[l]] g s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b)) →
  ∀ (m : ℕ) (σ : Fin m → (Fin 2 → PadicAlgCl l) →ₗ[PadicAlgCl l] TensorProduct ℤ_[l] (PadicAlgCl l) M),
  (∀ i v, σ i v ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype)) →
  (∀ i s v, LinearMap.baseChange (PadicAlgCl l) (g s) (σ i v) = σ i (Matrix.mulVec (ρ s) v)) →
  (∀ i, L (σ i ![1, 0]) = 0) →
  ∃ (κ : Fin m → PadicAlgCl l) (per : ℂ_[l]), ‖per‖ = 1 ∧ ∀ i v, L (σ i v) = per * ((κ i * v 1 : PadicAlgCl l) : ℂ_[l]) := by
  intro l _ M S _ _ B g ρ L F hgal m σ hσB hσeq hσ0
  classical

  have hsm : ∀ (a : PadicAlgCl l) (z : ℂ_[l]), a • z = (a : ℂ_[l]) * z := fun a z => by
    rw [Algebra.smul_def]; rfl
  set y : Fin m → ℂ_[l] := fun i => L (σ i ![0, 1]) with hy
  have hLv : ∀ i v, L (σ i v) = (v 1 : ℂ_[l]) * y i := by
    intro i v
    have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
      ext j; fin_cases j <;> simp
    calc L (σ i v) = L (σ i (v 0 • ![1, 0] + v 1 • ![0, 1])) := by rw [← hv]
      _ = _ := by rw [map_add (f := _), map_smul, map_smul, map_add (f := _), map_smul, map_smul, hσ0, smul_zero,
          zero_add, hsm]
  by_cases hall : ∀ i, y i = 0
  · refine ⟨0, 1, norm_one, fun i v => ?_⟩
    rw [hLv, hall i]; simp
  push_neg at hall
  obtain ⟨i₀, hy0⟩ := hall

  have hex : ∀ i, ∃ Sf : Finset (PadicAlgCl l × B),
      σ i ![0, 1] = ∑ q ∈ Sf, q.1 ⊗ₜ[ℤ_[l]] (q.2 : M) := by
    intro i
    obtain ⟨t, ht⟩ := hσB i ![0, 1]
    obtain ⟨Sf, rfl⟩ := TensorProduct.exists_finset t
    refine ⟨Sf, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← ht, map_sum]
    simp [LinearMap.baseChange_tmul]
  choose Sf hSf using hex
  set T : Finset (PadicAlgCl l) := F ∪ Finset.univ.biUnion (fun i => (Sf i).image Prod.fst) with hT
  set K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
    with hK
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTK : ∀ a ∈ T, a ∈ K := fun a ha => IntermediateField.subset_adjoin _ _ (by simpa using ha)
  have hFK : ∀ a ∈ F, a ∈ K := fun a ha => hTK a (Finset.mem_union_left _ ha)
  have hSK : ∀ i, ∀ q ∈ Sf i, q.1 ∈ K := fun i q hq =>
    hTK _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hq⟩))

  have hmul : ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, ∃ c : PadicAlgCl l,
      ∀ i, τ • y i = (c : ℂ_[l]) * y i := by
    intro τ
    obtain ⟨s, hs⟩ := hgal K hFK τ
    refine ⟨ρ s 1 1, fun i => ?_⟩
    have h1 : L (LinearMap.baseChange (PadicAlgCl l) (g s) (σ i ![0, 1])) = τ • y i := by
      rw [hy]
      simp only
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hSf i, map_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [LinearMap.baseChange_tmul]
      have e1 : ∀ x : M, q.1 ⊗ₜ[ℤ_[l]] x = q.1 • ((1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] x) := fun x => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e1 (q.2 : M), map_smul, map_smul, hsm, hsm, hs _ q.2.2, smul_mul',
        gal_smul_coe, show τ q.1 = q.1 from τ.commutes ⟨q.1, hSK i q hq⟩]
    rw [← h1, hσeq, hLv]
    congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hfix : ∀ i, ∃ k : K, ((k : PadicAlgCl l) : ℂ_[l]) = y i / y i₀ := by
    intro i
    refine exists_eq_coe_of_forall_smul_eq fun τ => ?_
    obtain ⟨c, hc⟩ := hmul τ
    have hne : τ • y i₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_smul_gal, norm_ne_zero_iff]; exact hy0
    have hc0 : (c : ℂ_[l]) ≠ 0 := by
      intro h0; apply hne; rw [hc, h0, zero_mul]
    rw [smul_div₀', hc, hc]
    field_simp
  choose k hk using hfix

  obtain ⟨a, ha⟩ := (Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt (y i₀)
    (norm_pos_iff.2 hy0)
  rw [dist_eq_norm] at ha
  have hna : ‖(a : ℂ_[l])‖ = ‖y i₀‖ := by
    have e : (a : ℂ_[l]) = -(y i₀ - (a : ℂ_[l])) + y i₀ := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact ha.ne),
      norm_neg, max_eq_right ha.le]
  have ha0 : (a : ℂ_[l]) ≠ 0 := by
    rw [← norm_ne_zero_iff, hna, norm_ne_zero_iff]; exact hy0
  refine ⟨fun i => (k i : PadicAlgCl l) * a, y i₀ / (a : ℂ_[l]), ?_, fun i v => ?_⟩
  · rw [norm_div, hna, div_self (norm_ne_zero_iff.2 hy0)]
  · rw [hLv, Completion.coe_mul, Completion.coe_mul, hk i]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinIntegralClosureIff
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory

theorem towerAlg_mem_iff (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (s : (integralClosure (O0 p) Ω)) :
    s ∈ towerAlg T ↔ (s : Ω) ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  have himg : ((integralClosure (O0 p) Ω).val : integralClosure (O0 p) Ω → Ω) ''
      (Set.range (zS T) ∪ Set.range (qS T)) = Set.range T.ζ ∪ Set.range T.qq := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hmap : (towerAlg T).map (integralClosure (O0 p) Ω).val =
      Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
    rw [towerAlg, AlgHom.map_adjoin, himg]
  rw [← hmap, Subalgebra.mem_map]
  constructor
  · intro h; exact ⟨s, h, rfl⟩
  · rintro ⟨t, ht, hts⟩
    have : t = s := Subtype.ext hts
    exact this ▸ ht

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndT
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem act_one_gen (x : Fin 2 → ℚ) : act x 1 = x := by
  funext i
  fin_cases i <;> simp [act, Fin.sum_univ_two]

theorem act_mul_gen (x : Fin 2 → ℚ) (γ δ : SL(2, ℤ)) : act x (γ * δ) = act (act x γ) δ := by
  funext i
  simp only [act, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem modular_law_of_generators (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ)
    (hP : ∀ x γ, P x → P (act x γ))
    (hS : ∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ)
    (hT : ∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) :
    ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {γ | ∀ x τ, P x → f x (γ • τ) = f (act x γ) τ}
      one_mem' := by
        intro x τ _
        simp [act_one_gen]
      mul_mem' := by
        intro γ δ hγ hδ x τ hx
        rw [mul_smul, hγ x _ hx, hδ _ τ (hP x γ hx), act_mul_gen]
      inv_mem' := by
        intro γ hγ x τ hx
        have h := hγ (act x γ⁻¹) (γ⁻¹ • τ) (hP x _ hx)
        rw [smul_inv_smul, ← act_mul_gen, inv_mul_cancel, act_one_gen] at h
        exact h.symm }
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H := by
    rw [Subgroup.closure_le]
    intro γ hγ
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  intro γ
  have : γ ∈ H := hle (by rw [_root_.SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ)
  exact this

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrder
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_top_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 →
    (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ hv σ hσF l hl hσl ⟨y, hy⟩ r hr
  obtain ⟨d, hdF, _hd0, hrx, hx1⟩ :=
    _root_.GlobalTheory.AlmostEt.klc_scale L v p hp F hF hp0 hp1 r hr (σ • y - y) (sub_ne_zero.mpr hy)
  set x := (σ • y - y) * d ^ p with hxdef
  refine ⟨x, Subfield.mem_top x, hx1, ?_⟩
  by_contra hle
  push_neg at hle
  have hfix : ∀ j : ℕ, (σ ^ j) • d = d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hσF d hdF, ih]
  have hterm : ∀ j : ℕ, (σ ^ j) • x = ((σ ^ (j + 1)) • y - (σ ^ j) • y) * d ^ p := by
    intro j
    rw [hxdef, smul_mul', smul_pow', hfix, smul_sub, pow_succ, mul_smul]
  have hsum : ∑ j ∈ Finset.range l, (σ ^ j) • x = 0 := by
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_range_sub (fun j => (σ ^ j) • y), hσl, one_smul, pow_zero,
      one_smul, sub_self, zero_mul]
  have hstep : ∀ j : ℕ, v ((σ ^ j) • x - x) ≤ r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (σ ^ (j + 1)) • x - x = σ • ((σ ^ j) • x - x) + (σ • x - x) := by
        rw [smul_sub, pow_succ', mul_smul]; ring
      rw [e]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hle)
      rw [hv]; exact ih
  have hlx : (l : L) * x = ∑ j ∈ Finset.range l, (x - (σ ^ j) • x) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : v ((l : L) * x) ≤ r := by
    rw [hlx]
    apply Valuation.map_sum_le
    intro j _
    rw [← Valuation.map_neg, neg_sub]
    exact hstep j
  rw [map_mul, _root_.GlobalTheory.AlmostEt.natCast_eq_one_of_coprime L v p l hp1 hl, one_mul] at h1
  exact absurd (lt_of_lt_of_le hrx h1) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusOldformTraceToGammaZero
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.TrOld

def rep (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : Option (Fin l) → SL(2, ℤ)
  | none => 1
  | some j => gaOld N l a b h j

def sig (l : ℕ) [NeZero l] (x : SL(2, ℤ)) : Option (Fin l) :=
  if (l : ℤ) ∣ mat x 1 0 then none
  else some ⟨(((mat x 1 1 : ℤ) : ZMod l) * ((mat x 1 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩

lemma mul_11 (x y : SL(2, ℤ)) : mat (x * y) 1 1 = mat x 1 0 * mat y 0 1 + mat x 1 1 * mat y 1 1 := by
  simp only [mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma mulInv_10 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 0 = mat x 1 0 * mat y 1 1 - mat x 1 1 * mat y 1 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ring

lemma mulInv_11 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 1 = -(mat x 1 0 * mat y 0 1) + mat x 1 1 * mat y 0 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

lemma mem_iff (M : ℕ) (x : SL(2, ℤ)) : x ∈ Gamma0 M ↔ (M : ℤ) ∣ mat x 1 0 := by
  rw [Gamma0_mem]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

section
variable {N l : ℕ} {a b : ℤ} {h : (l : ℤ) * b - N * a = 1}

lemma rep_none_10 : mat (rep N l a b h none) 1 0 = 0 := rfl
lemma rep_none_11 : mat (rep N l a b h none) 1 1 = 1 := rfl
lemma rep_some_10 (j : Fin l) : mat (rep N l a b h (some j)) 1 0 = N := rfl
lemma rep_some_11 (j : Fin l) : mat (rep N l a b h (some j)) 1 1 = (N : ℤ) * (j : ℕ) + l * b := rfl

lemma rep_00 (o : Option (Fin l)) : mat (rep N l a b h o) 0 0 = 1 := by
  cases o <;> simp [rep, gaOld, mat]

lemma rep_10 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 0 : ℤ) : ZMod N) = 0 := by
  cases o with
  | none => rw [rep_none_10]; simp
  | some j => rw [rep_some_10]; simp

lemma rep_11 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 1 : ℤ) : ZMod N) = 1 := by
  cases o with
  | none => rw [rep_none_11]; simp
  | some j =>
    have hc := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at hc
    rw [ZMod.natCast_self, zero_mul, sub_zero] at hc
    rw [rep_some_11]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add, hc]

include h in
lemma cop : IsCoprime (N : ℤ) (l : ℤ) := ⟨-a, b, by linear_combination h⟩

lemma sig_mem [NeZero l] (hl : l.Prime) (x : SL(2, ℤ)) (hx : x ∈ Gamma0 N) :
    x * (rep N l a b h (sig l x))⁻¹ ∈ Gamma0 (N * l) := by
  have := Fact.mk hl
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hδ : ∀ o, (N : ℤ) ∣ mat (rep N l a b h o) 1 0 := fun o =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (rep_10 o)
  rw [mem_iff] at hx
  rw [mem_iff, mulInv_10]
  push_cast
  apply hc.mul_dvd
  · exact dvd_sub (Dvd.dvd.mul_right hx _) (Dvd.dvd.mul_left (hδ _) _)
  · unfold sig
    split_ifs with hd
    · rw [rep_none_10, rep_none_11]
      simpa using hd
    · rw [rep_some_10, rep_some_11, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hc0 : ((mat x 1 0 : ℤ) : ZMod l) ≠ 0 := by
        rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hu := mul_inv_cancel₀ hc0
      have hl0 : ((l : ℕ) : ZMod l) = 0 := ZMod.natCast_self l
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination ((N : ZMod l) * ((mat x 1 1 : ℤ) : ZMod l)) * hu +
        (((mat x 1 0 : ℤ) : ZMod l) * (b : ZMod l)) * hl0

lemma not_dvd (hN : 0 < N) (hl : l.Prime) : ¬ ((N : ℤ) * l ∣ N) := by
  intro hd
  have h1 := Int.le_of_dvd (by exact_mod_cast hN) hd
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h3 : (0 : ℤ) < N := by exact_mod_cast hN
  nlinarith

lemma rep_inj (hN : 0 < N) (hl : l.Prime) (o₁ o₂ : Option (Fin l))
    (hm : rep N l a b h o₁ * (rep N l a b h o₂)⁻¹ ∈ Gamma0 (N * l)) : o₁ = o₂ := by
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [mem_iff, mulInv_10] at hm
  push_cast at hm
  rcases o₁ with _ | i <;> rcases o₂ with _ | j
  · rfl
  · exfalso
    rw [rep_none_10, rep_none_11, rep_some_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · exfalso
    rw [rep_some_10, rep_none_11, rep_none_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · rw [rep_some_10, rep_some_11, rep_some_10, rep_some_11] at hm
    have e : (N : ℤ) * (N * (j : ℕ) + l * b) - (N * (i : ℕ) + l * b) * N =
        N * (N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) := by ring
    rw [e] at hm
    have h1 : (l : ℤ) ∣ N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := (mul_dvd_mul_iff_left hN'.ne').1 hm
    have h2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := hc.symm.dvd_of_dvd_mul_left h1
    have h3 : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h2
      have := i.isLt
      have := j.isLt
      rw [abs_lt]
      constructor <;> omega
    congr 1
    ext
    omega

end

end GlobalTheory.HeckeFamilyMatrices.TrOld


open GlobalTheory.HeckeFamilyMatrices.TrOld in
theorem GlobalTheory.HeckeFamilyMatrices.chiInv_trOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1)
    (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → l.Prime → ChiInv k N (N * l) χ G →
    ChiInv k N N χ (trOld k N l a b h G) := by
  intro N l k a b h χ G hN hl hG γ hγ
  have : NeZero l := ⟨hl.ne_zero⟩
  have rep_mem : ∀ o, rep N l a b h o ∈ Gamma0 N := fun o => Gamma0_mem.2 (rep_10 o)
  have hsum : trOld k N l a b h G = ∑ o : Option (Fin l), G ∣[k] rep N l a b h o := by
    rw [Fintype.sum_option]
    simp only [rep, SlashAction.slash_one]
    unfold trOld
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun j => G ∣[k] gaOld N l a b h j) l).symm
  have hterm : ∀ o, (G ∣[k] rep N l a b h o) ∣[k] γ =
      χ ((mat γ 1 1 : ℤ) : ZMod N) • (G ∣[k] rep N l a b h (sig l (rep N l a b h o * γ))) := by
    intro o
    have hA : rep N l a b h o * γ ∈ Gamma0 N := mul_mem (rep_mem o) hγ
    have hη := sig_mem (h := h) hl _ hA
    have hA0 : ((mat (rep N l a b h o * γ) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hA
    have hchar : ((mat (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹) 1 1 : ℤ)
        : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
      rw [mulInv_11, rep_00]
      push_cast
      rw [hA0, mul_11]
      push_cast
      rw [rep_10, rep_11]
      ring
    have e : G ∣[k] (rep N l a b h o * γ) =
        (G ∣[k] (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹)) ∣[k]
          rep N l a b h (sig l (rep N l a b h o * γ)) := by
      rw [← SlashAction.slash_mul, inv_mul_cancel_right]
    rw [← SlashAction.slash_mul, e, hG _ hη, ModularForm.SL_smul_slash, hchar]
  have hinj : Function.Injective (fun o => sig l (rep N l a b h o * γ)) := by
    intro o₁ o₂ he
    apply rep_inj (h := h) hN hl
    have h1 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₁) hγ)
    have h2 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₂) hγ)
    simp only at he
    rw [he] at h1
    have h3 := mul_mem h1 (inv_mem h2)
    convert h3 using 1
    group
  rw [hsum, SlashAction.sum_slash, Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.smul_sum]
  congr 1
  exact (Finite.injective_iff_bijective.mp hinj).sum_comp (fun o => G ∣[k] rep N l a b h o)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaise
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem chiInv_slash_dg (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ) (hl : 0 < l)
    (hB : ChiInv k N N χ B) : ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  intro γ hγ
  rw [Gamma0_mem] at hγ
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (mat γ 1 0) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  obtain ⟨t, ht⟩ := hdvd
  have hdet : (mat γ).det = 1 := by simp [mat]
  rw [Matrix.det_fin_two] at hdet
  let γ' : SL(2, ℤ) := ⟨!![mat γ 0 0, (l : ℤ) * mat γ 0 1; (N : ℤ) * t, mat γ 1 1], by
    rw [Matrix.det_fin_two_of]; push_cast at ht; rw [ht] at hdet; linear_combination hdet⟩
  have hE : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [γ']
  have hD : (dg l 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of]; omega
  have hDpos : 0 < (dg l 1).det := by simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl
  have hγd : (mat γ).det ≠ 0 := by simp [mat]
  have hEd : (mat γ').det ≠ 0 := by simp [mat]
  have hmul : dg l 1 * mat γ = mat γ' * dg l 1 := by
    push_cast at ht
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [dg, γ', mat, Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring
  have hs : mat γ' 1 1 = mat γ 1 1 := rfl
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hγd, hmul, toGL_mul _ _ hEd hD,
    SlashAction.slash_mul, ← slash_SL_eq, hB γ' hE, smul_slash_toGL k _ hDpos, hs]

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionMatrixMul
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SlashAction

theorem polySlash_matrix_mul : ∀ (w : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) →
    slP w (A * B) p = slP w B (slP w A p) :=
  fun w A B p hp => (GlobalTheory.HeckeFamilyMatrices.HkC.polySlash_comp w A B p (GlobalTheory.HeckeFamilyMatrices.HkC.mem_degLT_iff.1 hp)).symm

end GlobalTheory.HeckeFamilyMatrices.SlashAction
end

