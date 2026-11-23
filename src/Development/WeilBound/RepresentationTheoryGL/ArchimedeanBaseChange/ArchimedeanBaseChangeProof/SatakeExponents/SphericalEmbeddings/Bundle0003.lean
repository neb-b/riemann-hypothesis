module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2Intertwining
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.GL2Intertwining

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem exists_scalar_fixed_indSp_unrChar (α : Fin n → ℂˣ) (g : GL (Fin n) k) :
    ∃ c : ℂ, ∀ v : IndSp (points (Fin n))
      ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom),
      v ∈ fixed (iP (k := k) α) (KO k (Fin n)) → v.1.1 g = c * v.1.1 1 := by
  obtain ⟨p, hp, x, hx, rfl⟩ :=
    (GlobalTheory.SmGL.LeviInt.levi_integral_facts k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n))).2.2.2.2.2.2.2.2 g
  refine ⟨((twist ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)
      (deltaHalf k (fun _ : Fin n => Unit))).comp (leviProj k (points (Fin n))) ⟨p, hp⟩) 1, fun v hv => ?_⟩
  have h1 : v.1.1 (p * x) = v.1.1 p := by
    have h := congrArg (fun u : IndSp (points (Fin n))
      ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom) => u.1.1 p)
      (hv ⟨x, hx⟩)
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
    exact h
  have h2 := v.1.2 ⟨p, hp⟩ 1
  rw [mul_one] at h2
  rw [h1, h2]
  conv_lhs => rw [show v.1.1 1 = v.1.1 1 • (1 : ℂ) by simp]
  rw [map_smul, smul_eq_mul, mul_comm]

theorem kline (α : Fin n → ℂˣ) {v w : IndSp (points (Fin n))
    ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)}
    (hv : v ∈ fixed (iP (k := k) α) (KO k (Fin n))) (hw : w ∈ fixed (iP (k := k) α) (KO k (Fin n))) :
    w.1.1 1 • v = v.1.1 1 • w := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨c, hc⟩ := exists_scalar_fixed_indSp_unrChar α g
  show w.1.1 1 • v.1.1 g = v.1.1 1 • w.1.1 g
  rw [hc v hv, hc w hw, smul_eq_mul, smul_eq_mul]
  ring

theorem one_ne_zero_of_fixed (α : Fin n → ℂˣ) {w : IndSp (points (Fin n))
    ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)}
    (hw : w ∈ fixed (iP (k := k) α) (KO k (Fin n))) (h0 : w ≠ 0) : w.1.1 1 ≠ 0 := by
  intro h1
  apply h0
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨c, hc⟩ := exists_scalar_fixed_indSp_unrChar α g
  rw [hc w hw, h1, mul_zero]
  rfl

end PositivityTheory.Rg.BcB.N3.GL2Intertwining
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseAsm
section
namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3 GlobalTheory.SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sphEmb_of (hG : GL2SphericalSwap k) (hS : StageLift k) (hE : ExpSph k) (hP : SatPerm k) (hB : Bubble k) : SphEmb k := by
  intro n ξ hm V _ _ π hs hi hsph hq
  obtain ⟨η, f, hf⟩ := hE n V π hs hi hsph
  obtain ⟨σ, rfl⟩ := hP n ξ η V π hs hi hsph hq ⟨f, hf⟩
  exact hB hS hG n ξ hm σ V π hi hsph ⟨f, PositivityTheory.Rg.BcB.N3.PseSat.injective_of_ne_zero hi f hf⟩

end PositivityTheory.Rg.BcB.N3.Pse
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseBub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseBub

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse PositivityTheory.Rg.BcB.N3.PseSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comp_injective {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {π : Representation ℂ (GL (Fin n) k) V} {ρ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) U} (hi : π.IsIrreducible) (hsph : IsSpherical π)
    (f : π.IntertwiningMap ρ) (hf : Function.Injective f) (T : ρ.IntertwiningMap τ) (hT : KInj k T) :
    Function.Injective (T.comp f) := by
  classical
  set g := T.comp f with hg
  have hg' : ∀ v, g v = T (f v) := fun v => Representation.IntertwiningMap.comp_apply _ _ _ T f v
  rcases hi.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with h | h
  · intro x y hxy
    have hx : x - y ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [Representation.IntertwiningMap.mem_ker, map_sub, hxy, sub_self]
    rw [h] at hx
    have hx' : x - y ∈ (⊥ : Submodule ℂ V) := hx
    exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hx')
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hfv : f v ∈ fixed ρ (KO k (Fin n)) := by
      intro h'
      have := hv h'
      rw [← Representation.IntertwiningMap.isIntertwining, this]
      simp
    have hker : v ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [h]
      exact (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ V))
    rw [Representation.IntertwiningMap.mem_ker, hg'] at hker
    have := hT (f v) hfv hker
    exact hv0 (hf (by rw [this, map_zero]))

def wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := ∑ i : Fin n, (i : ℕ) * (σ i : ℕ)

theorem wt_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : wt σ ≤ n * (n * n) := by
  unfold wt
  calc ∑ i : Fin n, (i : ℕ) * (σ i : ℕ) ≤ ∑ _i : Fin n, n * n :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul i.2.le (σ i).2.le
    _ = n * (n * n) := by simp

theorem wt_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1) (hd : σ j < σ i) :
    wt σ < wt (σ * Equiv.swap i j) := by
  classical
  have hne : i ≠ j := by
    intro h
    subst h
    omega
  unfold wt
  have key : ∀ τ : Equiv.Perm (Fin n), ∑ k : Fin n, (k : ℕ) * (τ k : ℕ) =
      (i : ℕ) * (τ i : ℕ) + ((j : ℕ) * (τ j : ℕ) +
        ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (τ k : ℕ)) := by
    intro τ
    rw [Finset.add_sum_erase (Finset.univ.erase i) (fun k : Fin n => (k : ℕ) * (τ k : ℕ))
      (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩)]
    rw [Finset.add_sum_erase Finset.univ (fun k : Fin n => (k : ℕ) * (τ k : ℕ)) (Finset.mem_univ i)]
  rw [key σ, key (σ * Equiv.swap i j)]
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * ((σ * Equiv.swap i j) k : ℕ) =
      ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (σ k : ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hd' : (σ j : ℕ) < σ i := hd
  rw [hij]
  nlinarith

theorem exists_descent {n : ℕ} (σ : Equiv.Perm (Fin n)) (h1 : σ ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ σ j < σ i := by
  by_contra hne
  push_neg at hne
  apply h1
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hs : StrictMono (σ : Fin (m + 1) → Fin (m + 1)) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hle := hne i.castSucc i.succ (by simp)
      exact lt_of_le_of_ne hle (fun h => (Fin.castSucc_lt_succ (i := i)).ne (σ.injective h))
    ext x
    have hx := congrFun hs.eq_id x
    simp [hx]

theorem bubble : Bubble k := by
  intro hSL hG2 n ξ hξ σ₀ V _ _ π hi hsph hf₀
  have key : ∀ m : ℕ, ∀ σ : Equiv.Perm (Fin n), n * (n * n) - wt σ = m →
      (∃ f : π.IntertwiningMap (iP (ξ ∘ ⇑σ)), Function.Injective ⇑f) →
        ∃ f : π.IntertwiningMap (iP ξ), Function.Injective ⇑f := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro σ hm hσ
      by_cases h1 : σ = 1
      · subst h1
        exact hσ
      · obtain ⟨i, j, hij, hd⟩ := exists_descent σ h1
        obtain ⟨f, hf⟩ := hσ
        have hle : ‖(((ξ ∘ ⇑σ) i : ℂˣ) : ℂ)‖ ≤ ‖(((ξ ∘ ⇑σ) j : ℂˣ) : ℂ)‖ := hξ _ _ hd.le
        obtain ⟨T0, hT0⟩ := hG2 _ _ hle
        obtain ⟨T, hT⟩ := hSL n (ξ ∘ ⇑σ) i j hij ⟨T0, hT0⟩
        have hinj := comp_injective hi hsph f hf T hT
        have hw := wt_swap σ i j hij hd
        have hwle := wt_le (σ * Equiv.swap i j)
        have hlt : n * (n * n) - wt (σ * Equiv.swap i j) < m := by
          generalize n * (n * n) = N at *
          omega
        exact ih _ hlt (σ * Equiv.swap i j) rfl ⟨T.comp f, hinj⟩
  exact key _ σ₀ rfl hf₀

end PositivityTheory.Rg.BcB.N3.PseBub
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStage
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 2000000 in
theorem main {r t : ℕ} (A : Fin r → ℂˣ) (a b : ℂˣ) (B : Fin t → ℂˣ)
    (T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a])) (hT : KInj k T) :
    ∃ T' : (iP (k := k) (Fin.append A (Fin.append ![a, b] B))).IntertwiningMap
      (iP (k := k) (Fin.append A (Fin.append ![b, a] B))), KInj k T' := by
  obtain ⟨Ei⟩ := iP_append (k := k) 2 t ![a, b] B
  obtain ⟨Ei'⟩ := iP_append (k := k) 2 t ![b, a] B
  obtain ⟨Eo⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![a, b] B)
  obtain ⟨Eo'⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![b, a] B)
  exact mainGen _ _ Ei Ei' Eo Eo' T hT

set_option maxHeartbeats 2000000 in
variable (k) in
theorem stageLift : StageLift k := by
  intro n η i j hij ⟨T, hT⟩
  obtain ⟨r, hr⟩ : ∃ r, i.val = r := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, n = r + (2 + t) := ⟨n - (r + 2), by have := j.isLt; omega⟩
  subst ht
  obtain ⟨A, hA⟩ : ∃ A : Fin r → ℂˣ, ∀ l, A l = η (Fin.castAdd (2 + t) l) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin t → ℂˣ, ∀ l, B l = η (Fin.natAdd r (Fin.natAdd 2 l)) := ⟨_, fun _ => rfl⟩
  have ei : ∀ h : 0 < 2, Fin.natAdd r (Fin.castAdd t (⟨0, h⟩ : Fin 2)) = i := fun h => Fin.ext (by simp [hr])
  have ej : ∀ h : 1 < 2, Fin.natAdd r (Fin.castAdd t (⟨1, h⟩ : Fin 2)) = j := fun h => Fin.ext (by simp [hr, hij])
  have h1 : η = Fin.append A (Fin.append ![η i, η j] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · rw [Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [ei h]; rfl
        | ⟨1, h⟩ => rw [ej h]; rfl
      · rw [Fin.append_right, hB]
  have h2 : η ∘ Equiv.swap i j = Fin.append A (Fin.append ![η j, η i] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · have e1 : Fin.castAdd (2 + t) l ≠ i := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      have e2 : Fin.castAdd (2 + t) l ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2, Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [Function.comp_apply, ei h, Equiv.swap_apply_left]; rfl
        | ⟨1, h⟩ => rw [Function.comp_apply, ej h, Equiv.swap_apply_right]; rfl
      · have e1 : Fin.natAdd r (Fin.natAdd 2 m) ≠ i := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        have e2 : Fin.natAdd r (Fin.natAdd 2 m) ≠ j := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        rw [Fin.append_right, hB, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2]
  have := main (k := k) A (η i) (η j) B T hT
  rw [← h1, ← h2] at this
  exact this

end PositivityTheory.Rg.BcB.N3.PseStage

end
end

