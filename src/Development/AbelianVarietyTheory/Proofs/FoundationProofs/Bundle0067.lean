module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspForm
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem map_mapGL_rat (σ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ σ) =
      Matrix.SpecialLinearGroup.mapGL ℝ σ := by
  ext i j
  simp

theorem isZeroAt_sum {c : OnePoint ℝ} {k : ℤ} {ι : Type} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  refine Finset.sum_induction F (fun G => c.IsZeroAt G k) (fun a b ha hb => ha.add hb) ?_ h
  intro g _
  show IsZeroAtImInfty ((0 : ℍ → ℂ) ∣[k] g)
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

theorem heckeT_cuspForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k,
    ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  intro N l q k σ hN hq hql hσ f
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hql
    · exact h
  have hq0 : 0 < q := hq.pos
  have hinv := _root_.GlobalTheory.HkInv.heckeT_slash_invariant N l q k σ (⇑f) hN hq hql hσ
    (fun γ hγ => by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩)
  have hhol := (_root_.GlobalTheory.Hk.hecke_mdiff q k σ (⇑f) hq0 (CuspFormClass.holo f)).2.2
  refine ⟨{ toFun := GlobalTheory.Hk.heckeT k q σ ⇑f
            slash_action_eq' := ?_
            holo' := hhol
            zero_at_cusps' := ?_ }, rfl⟩
  · rintro A ⟨γ, hγ, rfl⟩
    exact hinv γ hγ
  · intro c hc
    show c.IsZeroAt (GlobalTheory.Hk.heckeT k q σ ⇑f) k
    rw [GlobalTheory.Hk.heckeT, _root_.GlobalTheory.Hk.uOp_eq_sum_slash q k (⇑f) hq0, _root_.GlobalTheory.Hk.smul_vOp_eq_slash q k _ hq0, ModularForm.SL_slash,
      ← SlashAction.slash_mul]
    refine OnePoint.IsZeroAt.add (isZeroAt_sum _ _ fun j _ => ?_) ?_
    · exact _root_.GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
    · have h := _root_.GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt N l k (Matrix.SpecialLinearGroup.mapGL ℚ σ *
        Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
          (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne')) hN hl
        (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
      rw [map_mul, map_mapGL_rat] at h
      exact h

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularForm
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma isBoundedAt_finsetSum_heckeT {c : OnePoint ℝ} {k : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    simp only [Finset.sum_empty]
    rw [SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem heckeT_modularForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  intro N l q k σ hN hq hql hσ f
  have hq0 : 0 < q := hq.pos
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hql
    · exact h
  have hinv : ∀ γ ∈ lev N l, (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := fun γ hγ =>
    f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  refine ⟨{ toFun := heckeT k q σ ⇑f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ lev N l), rfl⟩
    exact _root_.GlobalTheory.HkInv.heckeT_slash_invariant N l q k σ ⇑f hN hq hql hσ hinv A hA
  · exact (_root_.GlobalTheory.Hk.hecke_mdiff q k σ ⇑f hq0 f.holo').2.2
  · intro c hc
    have hsum := _root_.GlobalTheory.Hk.uOp_eq_sum_slash q k (⇑f) hq0
    have hv := _root_.GlobalTheory.Hk.smul_vOp_eq_slash q k ((⇑f) ∣[k] σ) hq0
    show c.IsBoundedAt (heckeT k q σ ⇑f) k
    unfold heckeT
    rw [hsum, hv]
    refine OnePoint.IsBoundedAt.add (isBoundedAt_finsetSum_heckeT _ _ fun j _ => ?_) ?_
    · exact _root_.GlobalTheory.Hk.slash_rat_isBoundedAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
    · set D := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
          (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne') with hD
      have e : ((⇑f ∣[k] σ) ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) D)
          = ⇑f ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)
              (Matrix.SpecialLinearGroup.mapGL ℚ σ * D) := by
        rw [map_mul, SlashAction.slash_mul, SL_slash]
        congr 2
        ext i j
        simp [Matrix.SpecialLinearGroup.mapGL]
      rw [e]
      refine _root_.GlobalTheory.Hk.slash_rat_isBoundedAt N l k _ hN hl ?_ f c hc
      simp [hD, Matrix.det_fin_two_of]
      exact_mod_cast hq0
end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEq
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private lemma submodule_toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ (A B C : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → _root_.GlobalTheory.FinWeil.SelfDual γ C → _root_.GlobalTheory.FinWeil.Adj A B → _root_.GlobalTheory.FinWeil.idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W B C (_root_.GlobalTheory.FinWeil.sumOp W A B v) = lam (_root_.GlobalTheory.FinWeil.idx A B) • _root_.GlobalTheory.FinWeil.sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W hW lam hlam A B C hA hB hC hAdj hAC hinf v hv
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hC' : ∀ y, y ∈ C ↔ ∀ c ∈ C, γ y c = 1 := hC
  have hv' : ∀ a ∈ A, W a v = v := hv
  have hlam' : (∀ n : ℕ, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
      lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧ ((∀ r ∈ P, σ r ∈ P) →
        lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P) := hlam
  obtain ⟨x, hx, P, hP, hfin, hxP, hBle⟩ : ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧
      (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x} := hAdj
  obtain ⟨hAB, -, hrep, -, -⟩ :=
    _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple hW A B hA hB x hx P hP hfin hxP hBle
  haveI := Fintype.ofFinite (R ⧸ P)
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hu : _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ q : R ⧸ P, W (Quotient.out q • x) v :=
    (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB v hv (R ⧸ P) (fun q => Quotient.out q • x)
      (fun q => B.smul_mem _ hx) hrep).1
  have huB : _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A B hB).2.1 (hAB ▸ hN)).2.1 v hv
  obtain ⟨n, f, hfC, hfrep⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A C hAC
  have hfrepB : ∀ c ∈ C, ∃! i, c - f i ∈ B := by
    intro c hc
    have key : ∀ i, c - f i ∈ A ↔ c - f i ∈ B := fun i => by
      have hm : c - f i ∈ C := C.sub_mem hc (hfC i)
      constructor
      · intro h
        have h' : c - f i ∈ A ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [hinf] at h'
        exact (Submodule.mem_inf.1 h').1
      · intro h
        have h' : c - f i ∈ B ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [← hinf] at h'
        exact (Submodule.mem_inf.1 h').1
    simpa only [key] using hfrep c hc
  have hBC := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW B C hC _ huB (Fin n) f hfC hfrepB).1
  have hACsum := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A C hC v hv (Fin n) f hfC hfrep).1
  have hSfix : ∀ c ∈ C, W c (_root_.GlobalTheory.FinWeil.sumOp W A C v) = _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A C hC).2.1 hAC).2.1 v hv

  have hmemE : ∀ y, y ∈ (A ⊓ C).toAddSubgroup ↔ y ∈ A ∧ y ∈ C := fun y => by
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf]
  have hEC : (A ⊓ C).toAddSubgroup.relIndex C.toAddSubgroup ≠ 0 := by
    rw [submodule_toAddSubgroup_inf, AddSubgroup.inf_relIndex_right]
    exact hAC
  have hEA := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (fun a ha => by
      simp only [Submodule.mem_toAddSubgroup] at ha
      rw [hmemE, hC' a]
      exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hA' t]
      exact ⟨fun h a ha => hW.swap_eq_one (h.1 a ha),
        fun h => ⟨fun a ha => hW.swap_eq_one (h a ha), ht⟩⟩)
    hEC).1
  have hdual := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (fun c hc => by
      simp only [Submodule.mem_toAddSubgroup] at hc
      rw [hmemE, hA' c]
      exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hC' t]
      exact ⟨fun h c hc => hW.swap_eq_one (h.2 c hc),
        fun h => ⟨ht, fun c hc => hW.swap_eq_one (h c hc)⟩⟩)
    (hEA ▸ hEC)).2.1

  obtain ⟨a, ha, hxa⟩ := hdual x (fun c _ hcE => by
    have hcBC : c ∈ B ⊓ C := by
      rw [← hinf]
      exact Submodule.mem_inf.2 ((hmemE c).1 hcE)
    exact hW.iso hB (Submodule.mem_inf.1 hcBC).1 hx)
  simp only [Submodule.mem_toAddSubgroup] at ha
  have hc₀ : x - a ∈ C := by
    rw [hC']
    intro c hc
    apply hW.swap_eq_one
    rw [sub_eq_add_neg, hW.add_right, hW.neg_right, hxa c hc,
      mul_inv_cancel₀ (hW.ne_zero c a)]
  obtain ⟨c₀, hc₀C, hxac⟩ : ∃ c₀ ∈ C, x = a + c₀ := ⟨x - a, hc₀, by abel⟩

  obtain ⟨χ, hχ⟩ : ∃ χ : R → ℂ, ∀ t, χ t = γ a (t • c₀) := ⟨fun t => γ a (t • c₀), fun _ => rfl⟩
  have hχne : ∀ t, χ t ≠ 0 := fun t => by rw [hχ]; exact hW.ne_zero _ _
  have hχadd : ∀ s t, χ (s + t) = χ s * χ t := fun s t => by
    rw [hχ, hχ, hχ, add_smul, hW.add_right]
  have hχ0 : χ 0 = 1 := by rw [hχ, zero_smul]; exact hW.zero_right a
  have hχx : ∀ t, χ t = γ a (t • x) := fun t => by
    rw [hχ, hxac, smul_add, hW.add_right,
      hW.iso hA ha (A.smul_mem t ha), one_mul]
  have hχP : ∀ r ∈ P, χ r = 1 := fun r hr => by
    rw [hχx]
    exact hW.iso hA ha ((hxP r).2 hr)
  have hχσ : ∀ t, χ (σ t) = χ t := fun t => by
    have h1 : γ (t • a) c₀ * γ (t • c₀) a = 1 := by
      have h0 := hW.iso hB (B.smul_mem t hx) hx
      rw [hxac, smul_add, hW.add_left, hW.add_right,
        hW.add_right,
        hW.iso hA (A.smul_mem t ha) ha,
        hW.iso hC (C.smul_mem t hc₀C) hc₀C] at h0
      simpa only [one_mul, mul_one] using h0
    rw [hW.swap a (t • c₀), ← hχ] at h1
    rw [hχ, ← hW.adj t a c₀]
    exact (mul_inv_eq_one₀ (hχne t)).1 h1
  have hχnt : ∃ t, χ t ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have haB : a ∈ B := by
      rw [hB']
      intro b hb
      obtain ⟨d, hd, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [hW.add_right,
        hW.iso hA ha (Submodule.mem_inf.1 hd).1, ← hχx,
        hcon, one_mul]
    have hc₀A : c₀ ∈ A := by
      have h1 : c₀ ∈ B ⊓ C := by
        refine Submodule.mem_inf.2 ⟨?_, hc₀C⟩
        have h2 := B.sub_mem hx haB
        rwa [hxac, add_sub_cancel_left] at h2
      rw [← hinf] at h1
      exact (Submodule.mem_inf.1 h1).1
    have h3 : (1 : R) • x ∈ A := by
      rw [one_smul, hxac]
      exact A.add_mem ha hc₀A
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 ((hxP 1).1 h3))
  have hσP : ∀ r ∈ P, σ r ∈ P := by
    intro r hr
    by_contra hσr
    obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hσr
    obtain ⟨t, ht⟩ := hχnt
    apply ht
    have h1 : t = t * i + σ (r * σ (t * s)) := by
      rw [map_mul, hW.sg_sg]
      linear_combination (-t) * hsi
    rw [h1, hχadd, hχP _ (P.mul_mem_left t hi), hχσ, hχP _ (P.mul_mem_right _ hr), one_mul]

  have hterm : ∀ s : R, W (s • x) v = χ (w * s * σ s) • W (s • c₀) v := fun s => by
    have hcomp := hW.comp (s • c₀) (s • a) v
    rw [hv' _ (A.smul_mem s ha), ← smul_add, add_comm c₀ a, ← hxac] at hcomp
    have e : γ (w • s • c₀) (s • a) = (χ (w * s * σ s))⁻¹ := by
      rw [hW.swap (s • a) (w • s • c₀), hW.adj s a,
        smul_smul, smul_smul, hχ, show σ s * w * s = w * s * σ s by ring]
    rw [hcomp, e, smul_smul, mul_inv_cancel₀ (hχne _), one_smul]

  have hshift : ∀ c ∈ C, ∑ i, W (f i) (W c v) = _root_.GlobalTheory.FinWeil.sumOp W A C v := by
    intro c hc
    have h1 : ∀ i, W (f i) (W c v) = W c (W (f i) v) := fun i => by
      rw [hW.comm,
        hW.iso hC (hfC i) hc, one_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun i _ => h1 i), ← map_sum, ← hACsum]
    exact hSfix c hc
  have hstep : ∀ i, W (f i) (∑ q : R ⧸ P, W (Quotient.out q • x) v) =
      ∑ q : R ⧸ P, χ (w * Quotient.out q * σ (Quotient.out q)) •
        W (f i) (W (Quotient.out q • c₀) v) := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hterm, map_smul]
  have hstep' : ∀ q : R ⧸ P, ∑ i, χ (w * Quotient.out q * σ (Quotient.out q)) •
      W (f i) (W (Quotient.out q • c₀) v) =
        χ (w * Quotient.out q * σ (Quotient.out q)) • _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    fun q => by rw [← Finset.smul_sum, hshift _ (C.smul_mem _ hc₀C)]
  rw [hBC, hu, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm,
    Finset.sum_congr rfl (fun q _ => hstep' q), ← Finset.sum_smul]
  congr 1
  rw [← finsum_eq_sum_of_fintype,
    _root_.GlobalTheory.NormFormGauss.gauss_quotient σ w hW.sg_sg hW.w_add P hP hfin hσP
      ((hlam'.2 P hP hfin).2 hσP).2 χ hχadd hχ0 hχP hχσ hχnt,
    hAB, ((hlam'.2 P hP hfin).2 hσP).1]

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesAdjoinKummerRootsAndValuesEqStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_adjoin_kummer_roots_and_values_eq : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ θ₀ : Ω, θ ≠ 0 → θ₀ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} → θ₀ ^ N ∈ Set.range (algebraMap K Ω) →
      ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      ∀ g : Ω ≃ₐ[K] Ω, GlobalTheory.NeedB.Inert B g → ∀ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 →
        B.valuation (θ ^ N / (θ₀ ^ N * c ^ N)) = 1 →
        g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup ∧ GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum ζ θ₀ g := by
  first | exact @GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | exact GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq | (intros; apply GlobalTheory.InertKummer.inert_fixes_adjoin_and_kum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfJKMem
section
open scoped MatrixGroups

open Polynomial

namespace GlobalTheory.K4.LevNormal

open GlobalTheory.KZ

theorem normal_of_fixed (F L : Type) [Field F] [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]
    (h : ∀ x : L, (∀ σ : L ≃ₐ[F] L, σ x = x) → x ∈ Set.range (algebraMap F L)) : Normal F L := by
  classical
  rw [normal_iff]
  intro x
  have hx : IsIntegral F x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨hx, ?_⟩
  have hfin : (Set.range fun σ : L ≃ₐ[F] L => σ x).Finite := by
    refine ((minpoly F x).rootSet_finite L).subset ?_
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    show aeval (σ x) (minpoly F x) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  set O := hfin.toFinset with hO
  set P : L[X] := ∏ g ∈ O, (X - C g) with hP
  have hmap : ∀ σ : L ≃ₐ[F] L, P.map (σ : L →+* L) = P := by
    intro σ
    rw [hP, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    refine Finset.prod_bijective σ σ.bijective ?_ (fun _ _ => rfl)
    intro g
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨σ * τ, rfl⟩
    · rintro ⟨τ, hτ⟩
      refine ⟨σ⁻¹ * τ, ?_⟩
      show σ.symm (τ x) = g
      rw [hτ, σ.symm_apply_apply]
  have hl : P ∈ lifts (algebraMap F L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply h
    intro σ
    have := congrArg (fun Q => Q.coeff n) (hmap σ)
    simpa [coeff_map] using this
  have hmon : P.Monic := monic_prod_of_monic _ _ fun g _ => monic_X_sub_C g
  obtain ⟨Q, hQ⟩ := (mem_lifts P).1 hl
  have h0 : aeval x Q = 0 := by
    rw [aeval_def, ← eval_map, hQ, hP, eval_prod]
    refine Finset.prod_eq_zero (i := x) ?_ (by simp)
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, rfl⟩
  have hd : (minpoly F x).map (algebraMap F L) ∣ P := by
    rw [← hQ]
    exact Polynomial.map_dvd _ (minpoly.dvd F x h0)
  have hs : P.Splits := Splits.prod fun g _ => Splits.X_sub_C g
  exact hs.of_dvd hmon.ne_zero hd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem isAlgebraic_of_jK_mem [Algebra.IsAlgebraic ℚ Ω] (X : Tower Ω ε) (F : Subfield X.K) (hj : X.jK ∈ F) (f : X.K) :
    IsAlgebraic F f := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  let A : IntermediateField F X.K := algebraicClosure F X.K
  have hc : ∀ c : Ω, algebraMap Ω X.K c ∈ A := by
    intro c
    rw [mem_algebraicClosure_iff]
    have h1 : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic c)
    have h2 : IsAlgebraic ℤ (algebraMap Ω X.K c) := h1.algHom (algebraMap Ω X.K).toIntAlgHom
    exact h2.extendScalars (R := ℤ) (S := F) (RingHom.injective_int _)
  let B : IntermediateField Ω X.K := A.toSubfield.toIntermediateField hc
  have hle : IntermediateField.adjoin Ω {X.jK} ≤ B := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact A.algebraMap_mem ⟨X.jK, hj⟩
  have h3 : IsAlgebraic A f := by
    obtain ⟨p, hp, h0⟩ := X.alg_j f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* A :=
      (IntermediateField.adjoin Ω {X.jK}).toSubfield.subtype.codRestrict A fun y => hle y.2
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).2 hp, ?_⟩
    rw [aeval_def, eval₂_map]
    exact h0
  exact h3.restrictScalars F

theorem gal_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω) (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    (hΓ : CongruenceSubgroup.Gamma m ≤ Γ') (s : Ω ≃ₐ[ℚ] Ω) (hs : s ζ = ζ) (f : X.K) (hf : f ∈ lev X Γ') :
    X.gal s f ∈ lev X Γ' := by
  rw [mem_lev_iff] at hf ⊢
  intro γ hγ
  have := X.recip m f hm (fun δ hδ => hf δ (hΓ hδ)) ζ hζ s 1 (by simpa using hs) γ γ (by simp)
  rw [← this, hf γ hγ]

theorem normal : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω), 0 < m → IsPrimitiveRoot ζ m → CongruenceSubgroup.Gamma m ≤ Γ' → letI := GlobalTheory.K4.algMdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup; Normal (GlobalTheory.K4.mdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ ε X Γ' m ζ hm hζ hΓ
  set S := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup with hS
  letI := algMdl X Γ' S
  haveI := isScalarTower_mdl X Γ' S
  haveI : Algebra.IsAlgebraic (mdl X Γ' S) (lev X Γ') := ⟨fun f =>
    (isAlgebraic_algebraMap_iff (A := X.K) (lev X Γ').subtype.injective).1
      (isAlgebraic_of_jK_mem X _ (jK_mem_mdl X Γ' S) (f : X.K))⟩
  apply normal_of_fixed
  intro x hx
  refine ⟨⟨x, (mem_mdl_iff X Γ' S _).2 ⟨x.2, fun s hs => ?_⟩⟩, rfl⟩
  have hsζ : s ζ = ζ := hs ⟨ζ, IntermediateField.subset_adjoin ℚ {ζ} rfl⟩
  let φ : lev X Γ' →ₐ[mdl X Γ' S] lev X Γ' :=
    { ((X.gal s).toRingHom.comp (lev X Γ').subtype).codRestrict (lev X Γ')
        (fun f => gal_mem_lev X Γ' m ζ hm hζ hΓ s hsζ f f.2) with
      commutes' := fun y => Subtype.ext (((mem_mdl_iff X Γ' S _).1 y.2).2 s hs) }
  exact congrArg Subtype.val (hx (AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)))

end GlobalTheory.K4.LevNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
section
namespace GlobalTheory.IwahoriEigenObj

theorem iwahoriEigenvalues : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues :=
  GlobalTheory.IwahoriEigen.iwahoriEigenvalues

end GlobalTheory.IwahoriEigenObj
end

