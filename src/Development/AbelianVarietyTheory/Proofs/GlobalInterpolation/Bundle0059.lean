module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions

theorem eN_eq_single {F : Type} [Field F] {N i : ℕ} (h : i < N) :
    Loc.eN F N i = Pi.single (⟨i, h⟩ : Fin N) 1 := by
  funext l
  simp only [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_eq_zero {F : Type} [Field F] {N i : ℕ} (h : ¬ i < N) : Loc.eN F N i = 0 := by
  funext l
  have hl : l.1 ≠ i := fun e => h (e ▸ l.2)
  simp only [Loc.eN, hl, if_false, Pi.zero_apply]

theorem inX_single {F : Type} [Field F] {n c : ℕ} (s : Fin (n + c)) (hs : s.1 < n) :
    Loc.inX F n c (Pi.single ⟨s.1, hs⟩ 1) = Pi.single s 1 := by
  funext l
  rw [inX_apply]
  by_cases hl : l.1 < n
  · simp only [hl, dif_pos, Pi.single_apply, Fin.ext_iff]
  · have hne : l ≠ s := fun e => hl (e ▸ hs)
    simp only [hl, dif_neg, not_false_eq_true, Pi.single_apply, hne, if_false]

theorem unfoldingAffineSpace_mem_iff_intrinsic : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) := by
  intro F _ n' c' n c hc hc' xj x
  subst hc'
  have hy : ∀ {a b : ℕ} (y : (Fin a → F) →ₗ[F] (Fin b → F)) (s : Fin a) (l : Fin b),
      y (Pi.single s 1) l = LinearMap.toMatrix' y l s := by
    intro a b y s l
    rw [LinearMap.toMatrix'_apply]
  have hM : ∀ (t : Loc.FC n' (c + 1) n c → F) (l : Fin (n + c)) (s : Fin (n' + (c + 1))),
      LinearMap.toMatrix' (Loc.xx1 xj t) l s =
        if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
        else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
        else if l.1 = n + (s.1 - n') then 1 else 0 := by
    intro t l s
    simp only [Loc.xx1, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨fun v => ?_, ?_, ?_⟩
    · have hcomp : (Loc.xx1 xj t).comp (Loc.inX F n' (c + 1)) = (Loc.inX F n c).comp xj := by
        refine (Pi.basisFun F (Fin n')).ext fun a => ?_
        rw [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.comp_apply]
        have hi := inX_single (F := F) (n := n') (c := c + 1) (Fin.castAdd (c + 1) a) a.2
        simp only [Fin.val_castAdd, Fin.eta] at hi
        rw [hi]
        funext l
        rw [hy, hM, inX_apply]
        have hnf : ¬ Loc.IsFree n' n c l.1 (Fin.castAdd (c + 1) a).1 := by
          simp only [Loc.IsFree, Fin.val_castAdd]
          omega
        rw [dif_neg hnf, dif_pos (by simp only [Fin.val_castAdd]; exact a.2)]
        by_cases hl : l.1 < n
        · rw [dif_pos hl, dif_pos hl, hy]
          rfl
        · rw [dif_neg hl, dif_neg hl]
      exact LinearMap.congr_fun hcomp v
    · rw [eN_eq_single (show n' < n' + (c + 1) by omega)]
      funext l
      rw [hy, hM]
      have hnf : ¬ Loc.IsFree n' n c l.1 n' := by
        simp only [Loc.IsFree]
        omega
      rw [dif_neg hnf, dif_neg (lt_irrefl n'), Nat.sub_self, Nat.add_zero]
      simp only [Loc.eN]
    · intro s
      rw [mem_Ufl]
      intro l hl
      rw [Pi.sub_apply]
      by_cases hs : n' + s < n' + (c + 1)
      · rw [eN_eq_single hs, hy, hM]
        have hnf : ¬ Loc.IsFree n' n c l.1 (n' + s) := by
          have := l.2
          simp only [Loc.IsFree]
          omega
        rw [dif_neg hnf, dif_neg (Nat.not_lt.2 (Nat.le_add_right n' s))]
        change (if l.1 = n + (n' + s - n') then (1 : F) else 0) - _ = 0
        rw [Nat.add_sub_cancel_left]
        simp only [Loc.eN, sub_self]
      · rw [eN_eq_zero hs, map_zero]
        have hne : l.1 ≠ n + s := by
          have := l.2
          omega
        simp only [Loc.eN, hne, if_false, Pi.zero_apply, sub_zero]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun p => x (Pi.single p.1.2 1) p.1.1, ?_⟩
    refine (Pi.basisFun F (Fin (n' + (c + 1)))).ext fun s => ?_
    rw [Pi.basisFun_apply]
    funext l
    rw [hy (Loc.xx1 xj _), hM]
    by_cases hf : Loc.IsFree n' n c l.1 s.1
    · rw [dif_pos hf]
    rw [dif_neg hf]
    by_cases hs : s.1 < n'
    · rw [dif_pos hs, ← inX_single s hs, h1, inX_apply]
      by_cases hl : l.1 < n
      · rw [dif_pos hl, dif_pos hl, hy]
      · rw [dif_neg hl, dif_neg hl]
    rw [dif_neg hs]
    have hsj : s.1 = n' + (s.1 - n') := by omega
    have hsingle : (Pi.single s 1 : Fin (n' + (c + 1)) → F) = Loc.eN F (n' + (c + 1)) (n' + (s.1 - n')) := by
      rw [eN_eq_single (show n' + (s.1 - n') < n' + (c + 1) by omega)]
      congr 1
      exact Fin.ext hsj
    rw [hsingle]
    by_cases h0 : s.1 - n' = 0
    · rw [h0]
      change x (Loc.eN F (n' + (c + 1)) n') l = if l.1 = n then 1 else 0
      rw [h2]
      simp only [Loc.eN]
    · have hmem := (mem_Ufl).1 (h3 (s.1 - n')) l (by
        simp only [Loc.IsFree] at hf
        omega)
      rw [Pi.sub_apply, sub_eq_zero] at hmem
      rw [hmem]
      simp only [Loc.eN]

end GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingCharacterArgumentCompUnipotentRadicals
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals

variable {F : Type} [Field F] {n' c' n c : ℕ}

private theorem mem_Ufl_iff_forall_not_lt_eq_zero {N C i : ℕ} {v : Fin (N + C) → F} :
    v ∈ Loc.Ufl F N C i ↔ ∀ l : Fin (N + C), ¬ l.1 < N + i → v l = 0 := Iff.rfl

private theorem atN_add' {N : ℕ} (v w : Fin N → F) (i : ℕ) :
    Loc.atN (v + w) i = Loc.atN v i + Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

private theorem atN_smul' {N : ℕ} (a : F) (v : Fin N → F) (i : ℕ) :
    Loc.atN (a • v) i = a * Loc.atN v i := by
  unfold Loc.atN
  split_ifs <;> simp

private theorem atN_sub' {N : ℕ} (v w : Fin N → F) (i : ℕ) :
    Loc.atN (v - w) i = Loc.atN v i - Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

private theorem atN_eq_zero_of_mem_Ufl {N C i : ℕ} {v : Fin (N + C) → F} (hv : v ∈ Loc.Ufl F N C i) :
    Loc.atN v (N + i) = 0 := by
  unfold Loc.atN
  split_ifs with h
  · exact mem_Ufl_iff_forall_not_lt_eq_zero.1 hv ⟨N + i, h⟩ (lt_irrefl _)
  · rfl

private theorem atN_eN_self {N j : ℕ} (h : j < N) : Loc.atN (Loc.eN F N j) j = 1 := by
  simp [Loc.atN, Loc.eN, h]

theorem sub_atN_mem {i : ℕ} {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c (i + 1)) :
    v - Loc.atN v (n + i) • Loc.eN F (n + c) (n + i) ∈ Loc.Ufl F n c i := by
  rw [mem_Ufl_iff_forall_not_lt_eq_zero] at hv ⊢
  intro l hl
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Loc.eN]
  by_cases he : l.1 = n + i
  · rw [if_pos he]
    have hlt : n + i < n + c := by
      rw [← he]
      exact l.2
    have ha : Loc.atN v (n + i) = v l := by
      unfold Loc.atN
      rw [dite_eq_left hlt]
      congr 1
      exact Fin.ext he.symm
    rw [ha]
    ring
  · rw [if_neg he, hv l (by omega)]
    ring

private theorem Ufl_mem_succ_of_mem {N C i : ℕ} {v : Fin (N + C) → F} (hv : v ∈ Loc.Ufl F N C i) :
    v ∈ Loc.Ufl F N C (i + 1) :=
  mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => mem_Ufl_iff_forall_not_lt_eq_zero.1 hv l (fun h => hl (by omega))

private theorem eN_mem_Ufl_succ {N C i : ℕ} : Loc.eN F (N + C) (N + i) ∈ Loc.Ufl F N C (i + 1) :=
  mem_Ufl_iff_forall_not_lt_eq_zero.2 fun l hl => by
    simp only [Loc.eN]
    rw [if_neg]
    omega

theorem map_mem_Ufl {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) (s : ℕ) :
    ∀ v ∈ Loc.Ufl F n' c' s, x v ∈ Loc.Ufl F n c s := by
  induction s with
  | zero =>
    intro v hv
    have hv' := mem_Ufl_iff_forall_not_lt_eq_zero.1 hv
    have e : v = Loc.inX F n' c' (fun j => v (Fin.castAdd c' j)) := by
      funext l
      simp only [Loc.inX, LinearMap.pi_apply]
      split_ifs with h
      · rfl
      · simp only [LinearMap.zero_apply]
        exact hv' l (by omega)
    rw [e, h1]
    apply mem_Ufl_iff_forall_not_lt_eq_zero.2
    intro l hl
    simp only [Loc.inX, LinearMap.pi_apply]
    rw [dite_eq_right (by omega)]
    rfl
  | succ s ih =>
    intro v hv
    have hd := sub_atN_mem hv
    have e : v = (v - Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s)) +
        Loc.atN v (n' + s) • Loc.eN F (n' + c') (n' + s) := by abel
    rw [e, map_add (f := _), map_smul]
    refine Submodule.add_mem _ (Ufl_mem_succ_of_mem (ih _ hd)) (Submodule.smul_mem _ _ ?_)
    have e2 : x (Loc.eN F (n' + c') (n' + s)) = Loc.eN F (n + c) (n + s) +
        (x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s)) := by abel
    rw [e2]
    exact Submodule.add_mem _ eN_mem_Ufl_succ (Ufl_mem_succ_of_mem (h3 s))

private theorem atN_apply_eq_atN_of_mem_Ufl_succ {N' C' N C : ℕ} (y : (Fin (N' + C') → F) →ₗ[F] (Fin (N + C) → F))
    (hU : ∀ s, ∀ v ∈ Loc.Ufl F N' C' s, y v ∈ Loc.Ufl F N C s)
    (h3 : ∀ s : ℕ, y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s) ∈ Loc.Ufl F N C s)
    {s : ℕ} (hs : s < C) {v : Fin (N' + C') → F} (hv : v ∈ Loc.Ufl F N' C' (s + 1)) :
    Loc.atN (y v) (N + s) = Loc.atN v (N' + s) := by
  have hd := sub_atN_mem hv
  have hsm : Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) +
      (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s))) =
      y (Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s)) := by
    rw [map_smul]
    congr 1
    abel
  have hy : y v = y (v - Loc.atN v (N' + s) • Loc.eN F (N' + C') (N' + s)) +
      Loc.atN v (N' + s) • (Loc.eN F (N + C) (N + s) +
        (y (Loc.eN F (N' + C') (N' + s)) - Loc.eN F (N + C) (N + s))) := by
    rw [hsm, ← map_add (f := _), sub_add_cancel]
  rw [hy, atN_add', atN_smul', atN_add', atN_eq_zero_of_mem_Ufl (hU s _ hd),
    atN_eN_self (by omega), atN_eq_zero_of_mem_Ufl (h3 s)]
  ring

theorem atN_map {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) {s : ℕ} (hs : s < c)
    {v : Fin (n' + c') → F} (hv : v ∈ Loc.Ufl F n' c' (s + 1)) : Loc.atN (x v) (n + s) = Loc.atN v (n' + s) := atN_apply_eq_atN_of_mem_Ufl_succ x (map_mem_Ufl h1 h3) h3 hs hv

theorem atN_eN_succ (N m : ℕ) : Loc.atN (Loc.eN F N (m + 1)) m = 0 := by
  simp [Loc.atN, Loc.eN]

private theorem atN_r_x_r'_eq_atN_x_add_atN_r'_add_atN_r (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F))
    (hU : ∀ s, ∀ v ∈ Loc.Ufl F n' c' s, x v ∈ Loc.Ufl F n c s)
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)
    (r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)) (hr : Loc.R1cond F n c r)
    (r' : (Fin (n' + c') → F) ≃ₗ[F] (Fin (n' + c') → F)) {i : ℕ} (hi : i < c)
    (e' : Fin (n' + c') → F) (E : Fin (n + c) → F)
    (he' : Loc.atN e' (n' + i) = 0) (hE : Loc.atN E (n + i) = 0)
    (hu' : r' e' - e' ∈ Loc.Ufl F n' c' (i + 1)) (hxe : x e' - E ∈ Loc.Ufl F n c (i + 1)) :
    Loc.atN (r (x (r' e'))) (n + i) =
      Loc.atN (x e') (n + i) + (Loc.atN (r' e') (n' + i) + Loc.atN (r E) (n + i)) := by
  have hz : x (r' e') - E ∈ Loc.Ufl F n c (i + 1) := by
    have e : x (r' e') - E = (x e' - E) + x (r' e' - e') := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ hxe (hU _ _ hu')
  have hrz : Loc.atN (r.toLinearMap (x (r' e') - E)) (n + i) = Loc.atN (x (r' e') - E) (n + i) :=
    atN_apply_eq_atN_of_mem_Ufl_succ r.toLinearMap hr.1 hr.2.2 hi hz
  have hxu : Loc.atN (x (r' e' - e')) (n + i) = Loc.atN (r' e' - e') (n' + i) :=
    atN_apply_eq_atN_of_mem_Ufl_succ x hU h3 hi hu'
  simp only [LinearEquiv.coe_coe] at hrz
  rw [map_sub, atN_sub', atN_sub', hE] at hrz
  rw [map_sub, atN_sub', atN_sub', he'] at hxu
  linear_combination hrz + hxu

theorem chArg_comp :
    (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∃ d : F, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + d := by
  intro H F _ n' c' n c hc hc' r hr r' hr'
  refine ⟨∑ i ∈ Finset.range c, (Loc.atN (r' (Loc.eN F (n' + c') (n' + i + 1))) (n' + i) +
    Loc.atN (r (Loc.eN F (n + c) (n + i + 1))) (n + i)), ?_⟩
  intro xj t
  obtain ⟨hx1, -, hx3⟩ := (H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  obtain ⟨hrc, -⟩ := hr
  obtain ⟨hr'c, -⟩ := hr'
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < c := Finset.mem_range.1 hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact atN_r_x_r'_eq_atN_x_add_atN_r'_add_atN_r _ (map_mem_Ufl hx1 hx3) hx3 r hrc r' hi' _ _ (atN_eN_succ _ _) (atN_eN_succ _ _)
    (by
      have h := hr'c.2.2 (i + 1)
      simp only [← add_assoc] at h
      exact h)
    (by
      have h := hx3 (i + 1)
      simp only [← add_assoc] at h
      exact h)

end GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces

variable {F : Type} [Field F] {n' c' n c : ℕ}

theorem hom_ext {a b : ℕ} {x y : (Fin a → F) →ₗ[F] (Fin b → F)}
    (h : ∀ s l, x (Pi.single s 1) l = y (Pi.single s 1) l) : x = y := by
  ext s l
  simpa using h s l

noncomputable def linPart (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) :
    (Loc.FC n' c' n c → F) →ₗ[F] ((Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) where
  toFun t := Loc.xx1 xj t - Loc.xx1 xj 0
  map_add' t u := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply, Pi.add_apply, linearMap_unfolding_apply_single]
    split_ifs <;> simp
  map_smul' a t := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, linearMap_unfolding_apply_single, RingHom.id_apply]
    split_ifs <;> simp

theorem unfoldingAffineLinearMap_apply_freeEntry (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (p : Loc.FC n' c' n c) :
    Loc.xx1 xj t (Pi.single p.1.2 1) p.1.1 = t p := by
  rw [linearMap_unfolding_apply_single, dite_eq_left p.2]

theorem map_Ufl {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)
    (s : ℕ) {v : Fin (n' + c') → F} (hv : v ∈ Loc.Ufl F n' c' s) : x v ∈ Loc.Ufl F n c s := by
  have key : ∀ l : Fin (n' + c'), l.1 < n' + s → x (Pi.single l 1) ∈ Loc.Ufl F n c s := by
    intro l hl
    by_cases hln : l.1 < n'
    · have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) =
          Loc.inX F n' c' (Pi.single (⟨l.1, hln⟩ : Fin n') 1) := by
        funext m
        rw [inX_apply]
        split_ifs with hm
        · by_cases hml : m = l
          · subst hml
            simp
          · have hne : (⟨m.1, hm⟩ : Fin n') ≠ ⟨l.1, hln⟩ := fun he => hml (Fin.ext (by simpa using he))
            simp [hml, hne]
        · have hml : m ≠ l := fun he => hm (he ▸ hln)
          simp [hml]
      rw [hsingle, h1]
      exact inX_mem_Ufl s _
    · have hle : n' ≤ l.1 := not_lt.1 hln
      have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) = Loc.eN F (n' + c') (n' + (l.1 - n')) := by
        funext m
        rw [Nat.add_sub_cancel' hle]
        by_cases hml : m = l
        · subst hml
          simp [Loc.eN]
        · have hv : m.1 ≠ l.1 := fun he => hml (Fin.ext he)
          simp [Loc.eN, hml, hv]
      rw [hsingle, ← sub_add_cancel (x (Loc.eN F (n' + c') (n' + (l.1 - n'))))
        (Loc.eN F (n + c) (n + (l.1 - n')))]
      exact Submodule.add_mem _ (Ufl_mono (by omega) (h3 (l.1 - n'))) (eN_mem_Ufl (by omega))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hl : l.1 < n' + s
  · have hsm : (Pi.single l (v l) : Fin (n' + c') → F) = v l • Pi.single l 1 := by
      funext m
      by_cases hml : m = l
      · subst hml
        simp
      · simp [hml]
    rw [hsm, map_smul]
    exact Submodule.smul_mem _ _ (key l hl)
  · have hz : v l = 0 := (mem_Ufl.1 hv) l hl
    rw [hz, Pi.single_zero, map_zero]
    exact Submodule.zero_mem _

theorem affine_action : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  intro H F _ n' c' n c hc hc' r hr r' hr' xj'
  have hR : Loc.R1cond F n c r := hr.1
  have hR' : Loc.R1cond F n' c' r' := hr'.1
  obtain ⟨γ, hγ⟩ := exists_res hr
  obtain ⟨γ', hγ'⟩ := exists_res hr'
  obtain ⟨xj, hxj⟩ : ∃ xj : (Fin n' → F) →ₗ[F] (Fin n → F),
      xj = γ.symm.toLinearMap ∘ₗ xj' ∘ₗ γ'.symm.toLinearMap := ⟨_, rfl⟩
  have hy : ∀ t, ∃ t', r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' t' := by
    intro t
    obtain ⟨c1, c2, c3⟩ := (H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
    refine (H F n' c' n c hc hc' xj' _).2 ⟨?_, ?_, ?_⟩
    · intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hγ', c1, hγ, hxj]
      simp
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hR'.2.1, c2, hR.2.1]
    · intro s
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hsplit : r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)))) - Loc.eN F (n + c) (n + s) =
          r (Loc.xx1 xj t (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s)) +
            (r (Loc.eN F (n + c) (n + s)) - Loc.eN F (n + c) (n + s)) +
            r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n' + c') (n' + s))) := by
        simp only [map_sub]
        abel
      rw [hsplit]
      exact Submodule.add_mem _ (Submodule.add_mem _ (hR.1 s _ (c3 s)) (hR.2.2 s))
        (hR.1 s _ (map_Ufl c1 c3 s (hR'.2.2 s)))
  obtain ⟨f, hf⟩ : ∃ f : (Loc.FC n' c' n c → F) → (Loc.FC n' c' n c → F), ∀ t p,
      f t p = (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨_, fun _ _ => rfl⟩
  have hyf : ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (f t) := by
    intro t
    obtain ⟨t', ht'⟩ := hy t
    have hft : f t = t' := by
      funext p
      rw [hf, ht', unfoldingAffineLinearMap_apply_freeEntry]
    rw [hft, ht']
  obtain ⟨L, hL⟩ : ∃ L : (Loc.FC n' c' n c → F) →ₗ[F] (Loc.FC n' c' n c → F), ∀ t p,
      L t p = (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨{ toFun := fun t p => (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1
       map_add' := fun t u => by
         funext p
         simp only [map_add (f := _), LinearMap.add_comp, LinearMap.comp_add, LinearMap.add_apply, Pi.add_apply]
       map_smul' := fun a t => by
         funext p
         simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_apply, Pi.smul_apply,
           RingHom.id_apply] }, fun _ _ => rfl⟩
  have hxx : ∀ t : Loc.FC n' c' n c → F, Loc.xx1 xj t = linPart xj t + Loc.xx1 xj 0 := by
    intro t
    simp only [linPart, LinearMap.coe_mk, AddHom.coe_mk, sub_add_cancel]
  have hLf : ∀ t, L t + f 0 = f t := by
    intro t
    funext p
    rw [Pi.add_apply, hL, hf, hf, hxx t]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply, Pi.add_apply]
  have hinj : Function.Injective L := by
    intro t u htu
    have hfe : f t = f u := by rw [← hLf t, ← hLf u, htu]
    have hyy : r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap =
        r.toLinearMap ∘ₗ Loc.xx1 xj u ∘ₗ r'.toLinearMap := by rw [hyf t, hyf u, hfe]
    have hx : Loc.xx1 xj t = Loc.xx1 xj u := by
      refine LinearMap.ext fun v => ?_
      have hv := congrArg (fun g => r.symm (g (r'.symm v))) hyy
      simpa using hv
    funext p
    rw [← unfoldingAffineLinearMap_apply_freeEntry xj t p, ← unfoldingAffineLinearMap_apply_freeEntry xj u p, hx]
  refine ⟨xj, LinearEquiv.ofInjectiveEndo L hinj, f 0, fun t => ?_⟩
  rw [hyf t]
  congr 1
  exact (hLf t).symm

end GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces
end

