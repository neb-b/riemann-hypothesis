module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfSteps
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem move_left (hM : MidP k) (hR : RefineP k) (hS : SwapP k) (hJ : JuxtP k) (hL : LinkP k) (x ρ : IrrGL (k := k)) :
    ∀ (A : List (IrrGL (k := k))), (∀ a ∈ A, a.IsCusp ∧ ρ ≠ a.nu 1) → ∀ (Δ : Segment k) (b : IrrGL (k := k)) (B : List (IrrGL (k := k))), Δ.first = ρ →
      IsLSeg Δ b.rep → EmbL x (A ++ [b] ++ B) → ∃ (Γ : Segment k) (c y : IrrGL (k := k)), Γ.first = ρ ∧ IsLSeg Γ c.rep ∧ EmbL x [c, y] := by
  intro A
  induction A using List.reverseRecOn with
  | nil =>
    intro _ Δ b B hΔ hb hx
    obtain ⟨σ, -, hσ⟩ := hM x [b] B [] (by simpa using hx)
    exact ⟨Δ, b, σ, hΔ, hb, by simpa using hσ⟩
  | append_singleton A' a ih =>
    intro hA Δ b B hΔ hb hx
    have hA' : ∀ a ∈ A', a.IsCusp ∧ ρ ≠ a.nu 1 := fun a' ha' => hA a' (List.mem_append_left _ ha')
    have ha := hA a (by simp)
    have hx' : EmbL x (A' ++ [a, b] ++ B) := by simpa using hx
    by_cases hlk : (Segment.single a ha.1).Linked Δ
    · rcases hL a ha.1 Δ hlk with h | h
      · exact (ha.2 (hΔ.symm.trans h)).elim
      · obtain ⟨σ, hσ, hxσ⟩ := hM x A' [a, b] B hx'
        rw [h] at hσ
        rcases hJ σ b Δ hb hσ with h2 | h2
        · have hup : (up Δ).first = ρ := by
            unfold up
            rw [Segment.first_ofFirst]
            exact hΔ
          exact ih hA' (up Δ) σ B hup h2 hxσ
        · have h3 := hR x σ A' [b, Δ.first.nu Δ.len] B h2 hxσ
          rw [← h] at h3
          exact ih hA' Δ b ([a] ++ B) hΔ hb (by simpa using h3)
    · have h3 := hS x a b A' B _ Δ (single_spec ha.1).2.1 hb hlk hx'
      exact ih hA' Δ b ([a] ++ B) hΔ hb (by simpa using h3)

theorem exhaustion_of_steps
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      MidP k ∧ RefineP k ∧ SwapP k ∧ CuspEmbP k ∧ SuppP k ∧ JuxtP k ∧ LinkP k ∧ MinP k ∧ PeelGoodP k) :
    GlobalTheory.Published.LanglandsExhaustionGL := by
  intro k _ _ _ _ _ x
  obtain ⟨hM, hR, hS, hC, hP, hJ, hL, hm, hG⟩ := H k
  suffices H : ∀ n : ℕ, ∀ x : IrrGL (k := k), x.1 = n → ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep from H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact GlobalTheory.LocGL.exh_le_one x (by omega)
    obtain ⟨l, hl, hx⟩ := hC x
    have hne : l ≠ [] := by
      rintro rfl
      obtain ⟨hd, -⟩ := hx
      simp at hd
      omega
    obtain ⟨ρ, hρ, hmin⟩ := hm l hne hl
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hρ
    obtain ⟨Γ, c, y, e, hc, hy⟩ := move_left hM hR hS hJ hL x ρ A
      (fun a ha => ⟨hl a (List.mem_append_left _ ha), by simpa using hmin a (List.mem_append_left _ ha) 1 one_pos⟩)
      (Segment.single ρ (hl ρ hρ)) ρ B rfl (single_spec (hl ρ hρ)).2.1 (by simpa using hx)
    obtain ⟨hd, f, hf⟩ := id hy
    have hdeg : Γ.deg = c.1 := hc.deg_eq
    have hpos' : 0 < Γ.deg := Nat.mul_pos Γ.len_pos Γ.d_pos
    have hd2 : c.1 + y.1 = x.1 := (Fin.sum_univ_two fun a => ([c, y].get a).1).symm.trans hd
    obtain ⟨𝔫, h𝔫⟩ := ih y.1 (by omega) y rfl
    refine ⟨_, hG x [c, y].get hd Γ 𝔫 hc h𝔫 ⟨f, hf⟩ fun Δ' hΔ' hp => ?_⟩
    obtain ⟨j, hj, ej⟩ := hp.2
    exact hmin _ (hP x c y _ 𝔫 hl hx hy h𝔫 Δ' hΔ') j hj (e.symm.trans ej)

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev nxt (Δ : Segment k) : IrrGL (k := k) := Δ.first.nu ((Δ.len : ℕ) : ℂ)

variable (k)

def ShlP : Prop :=
  ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k), (∀ i, IsLSeg (Δ i) (x i).rep) →
    ∀ w : List (IrrGL (k := k)), (∀ c ∈ w, c.IsCusp) → Wd (prodIrr x hd) w → InShW (Finset.univ.val.map Δ) w

def DecLP : Prop := ∀ (Γ : Segment k) (σ : IrrGL (k := k)), EmbL σ (decW Γ) → IsLSeg Γ σ.rep

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidDefs
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

section Tensor

variable {G H V V' W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W]

def extL {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (f : ρ.IntertwiningMap ρ')
    (σ : Representation ℂ H W) : (extTensor ρ σ).IntertwiningMap (extTensor ρ' σ) where
  toLinearMap := f.toLinearMap.rTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

def extR (σ : Representation ℂ H W) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') : (extTensor σ ρ).IntertwiningMap (extTensor σ ρ') where
  toLinearMap := f.toLinearMap.lTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Ind

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def ind₂Map (e : a ⊕ b ≃ n) {ρ : Representation ℂ (GL a k × GL b k) V}
    {ρ' : Representation ℂ (GL a k × GL b k) V'} (f : ρ.IntertwiningMap ρ') :
    (ind₂ e ρ).IntertwiningMap (ind₂ e ρ') :=
  parIndMap (two e) (compMap f _)

end Ind

variable {nA nB m m' N : ℕ} {VA VB V V' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB] [Module ℂ VB]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def T3 (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) (τ : Representation ℂ (GL (Fin m) k) V) :=
  ind₂ (stdSum h1) (extTensor PA (ind₂ (stdSum h2) (extTensor τ PB)))

def tripleProductMap (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) {τ : Representation ℂ (GL (Fin m) k) V}
    {τ' : Representation ℂ (GL (Fin m) k) V'} (f : τ.IntertwiningMap τ') :
    (T3 h2 h1 PA PB τ).IntertwiningMap (T3 h2 h1 PA PB τ') :=
  ind₂Map _ (extR PA (ind₂Map _ (extL f PB)))

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.NotAboveTransGenSelf
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linkP : LinkP k := by
  intro ρ hρ Δ hl
  obtain ⟨σ, hσ, c, d, c', d', h1, h2, e1, e2⟩ := hl.exists_eq_icc
  have hlen : (Segment.single ρ hρ).len = 1 := rfl
  have hfst : (Segment.single ρ hρ).first = ρ := Segment.first_ofFirst _ _ _ _
  rw [e1, e2, Segment.linked_icc] at hl
  rw [e1] at hlen hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst] at hlen hfst
  have hdc : d = c := by omega
  subst hdc e2 hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst, IrrGL.nu_nu]
  rcases hl with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · left
    obtain rfl : c' = d + 1 := by omega
    congr 1
    push_cast
    ring
  · right
    obtain rfl : d = d' + 1 := by omega
    rw [show (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    congr 1
    push_cast
    ring

private theorem eq_zero_of_nu_eq_of_isCusp {ρ : IrrGL (k := k)} (hρ : ρ.IsCusp) (n : ℤ) (h : ρ.nu (n : ℂ) = ρ) : n = 0 := by
  have hsub : (Segment.icc ρ hρ n n le_rfl).carrier ⊆ (Segment.icc ρ hρ 0 0 le_rfl).carrier := by
    intro x hx
    rw [Segment.mem_icc] at hx ⊢
    obtain ⟨a, ha1, ha2, rfl⟩ := hx
    obtain rfl : a = n := le_antisymm ha2 ha1
    refine ⟨0, le_rfl, le_rfl, ?_⟩
    rw [h]
    simp [IrrGL.nu_zero]
  have := Segment.icc_subset_icc.mp hsub
  omega

theorem minP : MinP k := by
  classical
  intro l hl hc
  obtain ⟨ρ₀, h₀⟩ := List.exists_mem_of_ne_nil l hl
  set f : ℕ → IrrGL (k := k) := fun m => ρ₀.nu (-(m : ℂ)) with hf
  have hinj : Function.Injective f := by
    intro m m' hmm
    have h1 : (f m).nu (m : ℂ) = (f m').nu (m : ℂ) := by rw [hmm]
    simp only [hf, IrrGL.nu_nu, neg_add_cancel, IrrGL.nu_zero] at h1
    have h2 : ρ₀.nu (((m : ℤ) - m' : ℤ) : ℂ) = ρ₀ := by
      conv_rhs => rw [h1]
      congr 1
      push_cast
      ring
    have := eq_zero_of_nu_eq_of_isCusp (hc ρ₀ h₀) _ h2
    omega
  have hfin : {m : ℕ | f m ∈ l}.Finite := by
    refine ((l.toFinset.finite_toSet).preimage hinj.injOn).subset ?_
    intro m hm
    simpa using hm
  have h0 : (0 : ℕ) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f 0 ∈ l
    simpa [hf, IrrGL.nu_zero] using h₀
  set M := hfin.toFinset.max' ⟨0, h0⟩ with hMdef
  have hM : f M ∈ l := by
    have hm := hfin.toFinset.max'_mem ⟨0, h0⟩
    rw [Set.Finite.mem_toFinset] at hm
    exact hm
  refine ⟨f M, hM, fun ρ' hρ' j hj heq => ?_⟩
  have hρ'eq : ρ' = f (M + j) := by
    have h3 : (f M).nu (-(j : ℂ)) = ρ' := by
      rw [heq, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]
    rw [← h3]
    simp only [hf, IrrGL.nu_nu]
    congr 1
    push_cast
    ring
  have hmem : M + j ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f (M + j) ∈ l
    rw [← hρ'eq]
    exact hρ'
  have := hfin.toFinset.le_max' _ hmem
  omega

end PositivityTheory.Exh

end
end

