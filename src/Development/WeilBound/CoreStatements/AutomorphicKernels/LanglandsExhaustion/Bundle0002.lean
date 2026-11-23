module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDec
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def FineUniqP : Prop :=
  ∀ (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Zc.Seg.dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → τ.IsIrreducible →
    ∀ f : τ.IntertwiningMap (prodIrr (Zc.Seg.dec Δ) hd), Function.Injective f → IsLSeg Δ τ

theorem exists_emb_of_cast {h h' N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (e : h = h') (x : Fin h → IrrGL (k := k)) (y : Fin h' → IrrGL (k := k))
    (hxy : ∀ i, x i = y (Fin.cast e i)) (hd : ∑ a, (x a).1 = N) (f : τ.IntertwiningMap (prodIrr x hd))
    (hf : Function.Injective f) :
    ∃ hd' : ∑ a, (y a).1 = N, ∃ g : τ.IntertwiningMap (prodIrr y hd'), Function.Injective g := by
  subst e
  obtain rfl : x = y := funext fun i => by simpa using hxy i
  exact ⟨hd, f, hf⟩

theorem decW_get_eq (Γ : Segment k) (e : (decW Γ).length = Γ.len) (i : Fin (decW Γ).length) :
    (decW Γ).get i = Zc.Seg.dec Γ (Fin.cast e i) := by
  exact List.get_ofFn (fun a : Fin Γ.len => Γ.term (Fin.rev a)) i

theorem decLP (hF : FineUniqP k) : DecLP k := by
  intro Γ σ h
  obtain ⟨hd, f, hf⟩ := h
  have e : (decW Γ).length = Γ.len := List.length_ofFn
  obtain ⟨hd', g, hg⟩ := exists_emb_of_cast σ.rep e (decW Γ).get (Zc.Seg.dec Γ) (decW_get_eq Γ e) hd f hf
  exact hF Γ hd' σ.rep σ.2.rep.smooth σ.2.rep.irr g hg

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtSwap
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nu_nu_nat (x : IrrGL (k := k)) (a b : ℕ) : (x.nu (a : ℂ)).nu (b : ℂ) = x.nu ((a + b : ℕ) : ℂ) := by
  rw [IrrGL.nu_nu, Nat.cast_add]

theorem not_linked_single (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (n j : ℕ)
    (hj : j + 2 ≤ n) :
    ¬ (Segment.single (ρ.nu (n : ℂ)) (hρ.nu _)).Linked (Segment.single (ρ.nu (j : ℂ)) (hρ.nu _)) := by
  rintro ⟨⟨Γ, hΓ⟩, -, -⟩
  simp only [Segment.carrier_single] at hΓ
  have inj : ∀ a b : ℕ, ρ.nu (a : ℂ) = ρ.nu (b : ℂ) → a = b := fun a b h => GlobalTheory.T.cuspidal_twist_injective hA ρ hρ a b h
  have ha : ρ.nu (n : ℂ) ∈ Γ.carrier := by rw [hΓ]; exact Or.inl rfl
  have hb : ρ.nu (j : ℂ) ∈ Γ.carrier := by rw [hΓ]; exact Or.inr rfl
  obtain ⟨i, hi, ei⟩ := Segment.mem_carrier.1 ha
  obtain ⟨i', hi', ei'⟩ := Segment.mem_carrier.1 hb
  have key : ∀ s : ℕ, Γ.first.nu ((i' + s : ℕ) : ℂ) = ρ.nu ((j + s : ℕ) : ℂ) := by
    intro s; rw [← nu_nu_nat, ei', nu_nu_nat]
  have key2 : ∀ s : ℕ, Γ.first.nu ((i + s : ℕ) : ℂ) = ρ.nu ((n + s : ℕ) : ℂ) := by
    intro s; rw [← nu_nu_nat, ei, nu_nu_nat]
  rcases lt_or_ge i' i with h | h
  · have e1 := key (i - i')
    rw [show i' + (i - i') = i by omega, ei] at e1
    have h2 := inj _ _ e1
    have hc : Γ.first.nu ((i' + 1 : ℕ) : ℂ) ∈ Γ.carrier := Segment.mem_carrier.2 ⟨i' + 1, by omega, rfl⟩
    rw [hΓ, key 1] at hc
    rcases hc with hc | hc
    · have := inj _ _ (Set.mem_singleton_iff.1 hc); omega
    · have := inj _ _ (Set.mem_singleton_iff.1 hc); omega
  · have e1 := key2 (i' - i)
    rw [show i + (i' - i) = i' by omega, ei'] at e1
    have := inj _ _ e1
    omega

theorem mem_tail_decW (Δ : Segment k) (x : IrrGL (k := k)) (hx : x ∈ (decW Δ).tail) :
    ∃ j : ℕ, j + 2 ≤ Δ.len ∧ x = Δ.first.nu (j : ℂ) := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
  have hm' : m + 1 < Δ.len := by
    have := hm
    simp [decW] at this
    omega
  refine ⟨Δ.len - (m + 2), by omega, ?_⟩
  simp only [List.getElem_tail, decW, List.getElem_ofFn, Segment.term, Fin.val_rev]

theorem move_past (hS : SwapP k) (σ ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) :
    ∀ (Q P : List (IrrGL (k := k))), (∀ q ∈ Q, ∃ hq : q.IsCusp, ¬ (Segment.single ρ hρ).Linked (Segment.single q hq)) →
      EmbL σ (P ++ ρ :: Q) → EmbL σ (P ++ Q ++ [ρ]) := by
  intro Q
  induction Q with
  | nil => intro P _ h; simpa using h
  | cons q Q ih =>
    intro P hQ h
    obtain ⟨hq, hl⟩ := hQ q (by simp)
    have h2 : EmbL σ (P ++ [ρ, q] ++ Q) := by simpa using h
    have h3 := hS σ ρ q P Q _ _ (single_spec hρ).2.1 (single_spec hq).2.1 hl h2
    have h4 := ih (P ++ [q]) (fun q' hq' => hQ q' (by simp [hq'])) (by simpa using h3)
    simpa using h4

theorem emb_move_end (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hS : SwapP k) (σ : IrrGL (k := k)) (Δ : Segment k)
    (P Q : List (IrrGL (k := k))) (h1 : decW Δ = P ++ Q) (hP : P ≠ []) (he : EmbL σ (P ++ nxt Δ :: Q)) :
    EmbL σ (decW Δ ++ [nxt Δ]) := by
  obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP
  rw [h1]
  refine move_past hS σ (nxt Δ) (Δ.isCusp_first.nu _) Q (p :: P') ?_ he
  intro q hq
  have hq' : q ∈ (decW Δ).tail := by rw [h1]; simp [hq]
  obtain ⟨j, hj, rfl⟩ := mem_tail_decW Δ q hq'
  exact ⟨Δ.isCusp_first.nu _, not_linked_single hA Δ.first Δ.isCusp_first Δ.len j (by omega)⟩

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtUniq
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isLSeg (Δ : Segment k) (x y : IrrGL (k := k)) (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) : x = y := by
  obtain ⟨n, cx⟩ := x
  obtain ⟨m, cy⟩ := y
  obtain ⟨hx1, hxc⟩ := hx
  obtain ⟨hy1, hyc⟩ := hy
  have hnm : n = m := hx1.symm.trans hy1
  subst hnm
  obtain ⟨e⟩ := IsCosocle.unique hxc hyc
  have hc : cx = cy := by
    rw [← Quotient.out_eq cx, ← Quotient.out_eq cy]
    exact Quotient.sound ⟨e.symm⟩
  rw [hc]

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtWords
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_up (Δ : Segment k) : decW (up Δ) = nxt Δ :: decW Δ := by
  show List.ofFn (fun i : Fin (Δ.len + 1) => (up Δ).term (Fin.rev i)) = _
  rw [List.ofFn_succ]
  congr 1
  simp only [decW]
  congr 1
  funext i
  show Δ.first.nu (((Fin.rev i.succ : Fin (Δ.len + 1)) : ℕ) : ℂ) = Δ.first.nu (((Fin.rev i : Fin Δ.len) : ℕ) : ℂ)
  have h : ((Fin.rev i.succ : Fin (Δ.len + 1)) : ℕ) = ((Fin.rev i : Fin Δ.len) : ℕ) := by
    simp only [Fin.val_rev, Fin.val_succ]
    omega
  rw [h]

theorem nxt_not_mem (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : nxt Δ ∉ decW Δ := by
  intro h
  rw [decW, List.mem_ofFn] at h
  obtain ⟨i, hi⟩ := h
  have h2 := GlobalTheory.T.cuspidal_twist_injective hA Δ.first Δ.isCusp_first _ _ hi
  have h3 := (Fin.rev i).isLt
  omega

theorem eq_decW_of_append (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (u P Q : List (IrrGL (k := k)))
    (h1 : decW Δ = P ++ Q) (h2 : u ++ [nxt Δ] = P ++ nxt Δ :: Q) : u = decW Δ := by
  rcases Q.eq_nil_or_concat' with rfl | ⟨Q', q, rfl⟩
  · rw [h1, List.append_nil]
    exact (List.append_inj' h2 rfl).1
  · exfalso
    have h3 : u ++ [nxt Δ] = (P ++ nxt Δ :: Q') ++ [q] := by simpa using h2
    have h4 := (List.append_inj' h3 rfl).2
    have hq : q = nxt Δ := by simpa using h4.symm
    apply nxt_not_mem hA Δ
    rw [h1, ← hq]
    simp

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidExact
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

section TensorExact

variable {G H V₁ V₂ V₃ W : Type} [Group G] [Group H] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
  [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup W] [Module ℂ W]
  {τ₁ : Representation ℂ G V₁} {τ₂ : Representation ℂ G V₂} {τ₃ : Representation ℂ G V₃}

theorem extL_exact (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃) (σ : Representation ℂ H W)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (extL f σ) ∧ Function.Exact (extL f σ) (extL g σ) :=
  ⟨Module.Flat.rTensor_preserves_injective_linearMap (M := W) f.toLinearMap hf,
    Module.Flat.rTensor_exact W (f := f.toLinearMap) (g := g.toLinearMap) hfg⟩

theorem extR_exact (σ : Representation ℂ H W) (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (extR σ f) ∧ Function.Exact (extR σ f) (extR σ g) :=
  ⟨Module.Flat.lTensor_preserves_injective_linearMap (M := W) f.toLinearMap hf,
    Module.Flat.lTensor_exact W (f := f.toLinearMap) (g := g.toLinearMap) hfg⟩

end TensorExact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section IndExact

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
  {ρ₁ : Representation ℂ (GL a k × GL b k) V₁} {ρ₂ : Representation ℂ (GL a k × GL b k) V₂}
  {ρ₃ : Representation ℂ (GL a k × GL b k) V₃}

theorem ind₂Map_exact (e : a ⊕ b ≃ n) (f : ρ₁.IntertwiningMap ρ₂) (g : ρ₂.IntertwiningMap ρ₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (ind₂Map (k := k) e f) ∧ Function.Exact (ind₂Map (k := k) e f) (ind₂Map (k := k) e g) := by
  refine ⟨GlobalTheory.ParIndExact.parIndMap_injective _ _ hf, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · exact GlobalTheory.ParIndExact.parIndMap_exact _ (compMap f _) (compMap g _) hf
      (fun v hv => by obtain ⟨u, hu⟩ := (hfg v).1 hv; exact ⟨u, hu⟩) y hy
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hfg.apply_apply_eq_zero (u.1.1 x)

end IndExact

variable {nA nB m m' N : ℕ} {VA VB V₁ V₂ V₃ : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB] [Module ℂ VB]
  [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]


set_option maxHeartbeats 1000000 in
theorem tripleProductMap_injective (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) {τ₁ : Representation ℂ (GL (Fin m) k) V₁}
    {τ₂ : Representation ℂ (GL (Fin m) k) V₂} {τ₃ : Representation ℂ (GL (Fin m) k) V₃}
    (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) :
    Function.Injective (tripleProductMap h2 h1 PA PB f) ∧ Function.Exact (tripleProductMap h2 h1 PA PB f) (tripleProductMap h2 h1 PA PB g) := by
  have s1 := extL_exact (G := GL (Fin m) k) (H := GL (Fin nB) k) f g PB hf hfg
  have s2 := ind₂Map_exact (k := k) (stdSum h2) (extL f PB) (extL g PB) s1.1 s1.2
  have s3 := extR_exact (G := GL (Fin m') k) (H := GL (Fin nA) k) PA (ind₂Map (k := k) (stdSum h2) (extL f PB))
    (ind₂Map (k := k) (stdSum h2) (extL g PB)) s2.1 s2.2
  exact ind₂Map_exact (k := k) (stdSum h1) (extR PA (ind₂Map (k := k) (stdSum h2) (extL f PB)))
    (extR PA (ind₂Map (k := k) (stdSum h2) (extL g PB))) s3.1 s3.2

end PositivityTheory.Exh

end
end

