module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

set_option synthInstance.maxHeartbeats 400000

section

open GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.CompanionTheory.Hypotheses₂.TD

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem cellone_offdiag (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (x : Fin 2 → IrrGL (k := k))
    (H : ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = (x 1).1), 0 < (q 0).1 → jm q hq (x 1).rep ≠ 0 →
      ∀ (p : IrrGL (k := k)) (hc : ∑ a, (![p, q 0] a).1 = (x 0).1), jhMult (x 0).rep (prodIrr ![p, q 0] hc) = 0)
    {b : Fin 2 → Fin 2 → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (x j).1)
    (h0 : jhMult (piTensor fun i => (x i).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    b 1 0 = 0 := by
  have hτ : (piTensor fun i => (x i).rep).IsIrreducible := _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun i => (x i).2.rep
  have hτs : IsSmooth (piTensor fun i => (x i).rep) := isSmooth_piTensor fun i => (x i).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  by_contra hb
  let c : Fin 2 → Fin 2 → IrrGL (k := k) := fun i j => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr
  have hq : ∑ j, b 1 j = (x 1).1 := by simpa using Fintype.card_congr (f 1)
  have hd : ∑ i, b i 0 = (x 0).1 := by simpa using Fintype.card_congr (g 0)
  have hjm : jm (c 1) hq (x 1).rep ≠ 0 := by
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (f 1) (stdBlocks (fun j => b 1 j) hq) _).2
      (x 1).rep
    let θ := (piTensorEquiv fun j => IrrGL.equivOf (s 1 j).ρ (s 1 j).smooth (s 1 j).irr).symm
    exact jhMult_ne_zero_iff.2 ((IsSubquotient.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective).trans
      ((hrow 1).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)))
  have hsub : IsSubquotient (x 0).rep (prodIrr (fun i => c i 0) hd) := by
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) 0 (x 0).2.rep.irr
      ((isSubquotient_comp_mulSingle (fun i => (x i).rep) (fun i => (x i).2.rep.irr) 0).trans
        (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g 0) (stdBlocks (fun i => b i 0) hd) _).1
      (piTensor fun i => (s i 0).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i 0).ρ) (fun i => (s i 0).smooth) fun i => (s i 0).irr)
    exact h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective)
  have key : ∀ (z : Fin 2 → IrrGL (k := k)) (hz : ∑ a, (z a).1 = (x 0).1), z = ![c 0 0, c 1 0] →
      jhMult (x 0).rep (prodIrr z hz) = 0 := by
    rintro _ hz rfl
    exact H (c 1) hq (Nat.pos_of_ne_zero hb) hjm (c 0 0) hz
  refine jhMult_ne_zero_iff.2 hsub (key _ hd (funext fun i => ?_))
  fin_cases i <;> rfl

set_option maxHeartbeats 1000000 in
private theorem jacquet_multiplicity_single_cell (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (x : Fin 2 → IrrGL (k := k))
    (H : ∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = (x 1).1), 0 < (q 0).1 → jm q hq (x 1).rep ≠ 0 →
      ∀ (p : IrrGL (k := k)) (hc : ∑ a, (![p, q 0] a).1 = (x 0).1), jhMult (x 0).rep (prodIrr ![p, q 0] hc) = 0)
    {N : ℕ} (e : (Σ i, Fin (x i).1) ≃ Fin N) :
    jhMult (piTensor fun i => (x i).rep) (jac e (multiProd e fun i => (x i).rep)) = 1 := by
  classical
  have hτ : (piTensor fun i => (x i).rep).IsIrreducible := _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun i => (x i).2.rep
  let M := fun i : Fin 2 => Fin (x i).1
  haveI : Fintype (SizeMatrix M M) := Fintype.ofFinite _
  let b₀ : SizeMatrix M M := ⟨fun i j => if i = j then (x i).1 else 0, by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp [M]
    · simp [M]⟩
  have hρ : IsSmooth (piTensor fun i => (x i).rep) := isSmooth_piTensor fun i => (x i).2.rep.smooth
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_diag b₀ (fun i j hj => by simp [b₀, Ne.symm hj]) _ hρ
  let f : ∀ (b : SizeMatrix M M) i, (Σ j, Fin (b.1 i j)) ≃ M i := fun b =>
    if h : b = b₀ then h ▸ f₀ else b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix M M) j, (Σ i, Fin (b.1 i j)) ≃ M j := fun b =>
    if h : b = b₀ then h ▸ g₀ else b.nonempty_cols.some
  have hf : f b₀ = f₀ := by simp [f]
  have hg : g b₀ = g₀ := by simp [g]
  have h1 := (hG k).1.jhMult_eq (m := M) (m' := M) e e hρ f g hτ
  refine (show jhMult _ (jac e (multiProd e fun i => (x i).rep)) = _ from h1).trans ?_
  rw [Finset.sum_eq_single b₀]
  · have key : ∀ (f' : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ M i) (g' : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ M j), f' = f₀ → g' = g₀ →
        jhMult (piTensor fun i => (x i).rep) (cellFunctor f' g' (piTensor fun i => (x i).rep)) = 1 := by
      rintro _ _ rfl rfl
      exact (jhMult_congr_right _ E₀).trans (jhMult_self hτ)
    exact key _ _ hf hg
  · intro b _ hb
    by_contra hne
    have z2 := cellone_offdiag hG hBZ x H (f b) (g b) hne
    refine hb (Subtype.ext (funext fun i => funext fun j => ?_))
    have r0 := b.2.1 0
    have r1 := b.2.1 1
    have c0 := b.2.2 0
    simp only [Fin.sum_univ_two, M, Fintype.card_fin] at r0 r1 c0
    have z1 : b.1 0 1 = 0 := by omega
    have z3 : b.1 0 0 = (x 0).1 := by omega
    have z4 : b.1 1 1 = (x 1).1 := by omega
    revert i j
    simp only [Fin.forall_fin_two]
    exact ⟨⟨z3, z1⟩, z2, z4⟩
  · simp

end

theorem UpperTheory.Lit.Mix.cellone :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x y : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), (∀ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = y.1), 0 < (q 0).1 → jm q hq y.rep ≠ 0 → ∀ (p : IrrGL (k := k)) (hc : ∑ a, (![p, q 0] a).1 = x.1), jhMult x.rep (prodIrr ![p, q 0] hc) = 0) → jm ![x, y] hd (prodIrr ![x, y] hd) ≤ 1 := by
  intro hG hBZ k _ _ _ _ x y N hd H
  exact (jacquet_multiplicity_single_cell hG hBZ ![x, y] H (stdBlocks (fun a => (![x, y] a).1) hd)).le
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MDetjac
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem detjac_tprod_ne_zero {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (y : ∀ a, X a) (hy : ∀ a, y a ≠ 0) : PiTensorProduct.tprod ℂ y ≠ 0 := by
  have hφ : ∀ b, ∃ φ : X b →ₗ[ℂ] ℂ, φ (y b) ≠ 0 := fun b => by
    by_contra! h
    exact hy b ((Module.forall_dual_apply_eq_zero_iff ℂ (y b)).1 h)
  choose φ hφ using hφ
  intro h
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap φ)) h
  rw [PiTensorProduct.lift.tprod, map_zero] at h1
  exact Finset.prod_ne_zero_iff.2 (fun b _ => hφ b) (by simpa using h1)

private theorem detjac_scalar_factor {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hX : ∀ a, Nontrivial (X a)) (j : α) (g : Γ j) (c : ℂ)
    (h : ∀ w, piTensor ρ (Pi.mulSingle j g) w = c • w) (v : X j) : ρ j g v = c • v := by
  choose x hx using fun a => exists_ne (0 : X a)
  have h1 := h (PiTensorProduct.tprod ℂ (Function.update x j v))
  have h2 : (fun a => ρ a ((Pi.mulSingle j g : ∀ a, Γ a) a) (Function.update x j v a)) =
      Function.update x j (ρ j g v) := by
    funext a
    by_cases ha : a = j
    · subst ha; simp
    · simp [Pi.mulSingle_eq_of_ne ha, Function.update_of_ne ha]
  rw [piTensor_tprod, h2] at h1
  have hs : PiTensorProduct.tprod ℂ (Function.update x j (c • v)) =
      c • PiTensorProduct.tprod ℂ (Function.update x j v) := by
    simpa using (PiTensorProduct.tprod ℂ).map_update_smul x j c v
  rw [← hs, ← sub_eq_zero, ← (PiTensorProduct.tprod ℂ).map_update_sub x j] at h1
  by_contra hne
  refine detjac_tprod_ne_zero _ (fun a => ?_) h1
  by_cases ha : a = j
  · subst ha; simpa [sub_eq_zero] using hne
  · simpa [Function.update_of_ne ha] using hx a

private theorem detjac_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : jhMult σ ρ ≠ 0) :
    IsSubquotient σ ρ := by
  by_contra hn
  refine h ?_
  simp only [jhMult, ENat.iSup_eq_zero]
  rintro r ⟨S, T, -, -, h3⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rfl
  obtain ⟨φ⟩ := h3 ⟨0, hr⟩
  refine absurd ?_ hn
  refine (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans ?_
  exact ⟨S ⟨0, hr⟩, ⟨Submodule.mkQ _, fun g => rfl⟩, Submodule.mkQ_surjective _⟩

private theorem detjac_equiv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    (hi : π.IsIrreducible) (ψ : G →* ℂˣ) (h : ∀ g v, π g v = (ψ g : ℂ) • v) : Nonempty ((ofChar ψ).Equiv π) := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let f : (ofChar ψ).IntertwiningMap π := ⟨LinearMap.toSpanSingleton ℂ V x, fun g => LinearMap.ext fun c => by
    simp [h, smul_smul]⟩
  have hinj : Function.Injective f := smul_left_injective ℂ hx
  refine ⟨equivOfBijective f ⟨hinj, ?_⟩⟩
  rcases eq_bot_or_eq_top f.range with h0 | h0
  · have : x ∈ f.range := ⟨1, one_smul _ _⟩
    rw [h0] at this
    exact absurd this hx
  · intro v
    have : v ∈ f.range := by rw [h0]; trivial
    exact this

theorem UpperTheory.Lit.Mix.detjac :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = t), 0 < (q 0).1 → jm q hq (detRep (Fin t) χ) ≠ 0 → ∃ A : Multiset (IrrGL (k := k)), HasSupport (q 0).rep A ∧ (IrrGL.ofChar χ hχ).nu (-((t : ℂ) - 1) / 2) ∈ A := by
  intro k _ _ _ _ t χ hχ q hq hpos hj
  have hsub := detjac_isSubquotient hj
  have hχ' : IsSmoothChar (χ * absPow k (-((t : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
  have hm : modExp (fun i : Fin 2 => Fin (q i).1) 0 = (q 1).1 := by
    have h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
    simp [modExp, h1]
  have hc : χ * absPow k (-(modExp (fun i : Fin 2 => Fin (q i).1) 0 : ℂ) / 2) =
      (χ * absPow k (-((t : ℂ) - 1) / 2)) * absPow k (((((q 0).1 : ℕ) : ℂ) - 1) / 2) := by
    rw [mul_assoc, ← absPow_add, hm, ← hq, Fin.sum_univ_two]
    congr 2
    push_cast
    ring
  have hact : ∀ g v, (q 0).rep g v = ((detChar (Fin (q 0).1)
      ((χ * absPow k (-((t : ℂ) - 1) / 2)) * absPow k (((((q 0).1 : ℕ) : ℂ) - 1) / 2))) g : ℂ) • v := by
    intro g v
    refine detjac_scalar_factor (fun a => (q a).rep)
      (fun a => Model.nontrivial_of_isIrreducible (q a).2.rep.irr) 0 g _ (fun w => ?_) v
    rw [Model.scalar_of_isSubquotient hsub (Model.jac_detRep _ χ _) w, detLevi_apply, Fin.prod_univ_two,
      Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), map_one, map_one, mul_one, hc, detChar_apply]
  obtain ⟨φ⟩ := detjac_equiv (q 0).2.rep.irr _ hact
  refine ⟨_, (hasSupport_detRep hχ' hpos).of_equiv φ, ?_⟩
  refine Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, hpos, ?_⟩)
  rw [Nat.cast_zero, IrrGL.nu_zero, IrrGL.nu, IrrGL.tw_ofChar]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MFront
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem UpperTheory.Lit.Mix.front_support_decomposition (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (m + n)) k) V) (A₀ A₁ : Multiset (IrrGL (k := k))) (hA : HasSupport π (A₀ + A₁))
    (hm₀ : (A₀.map Sigma.fst).sum = m) (hU : ∀ x ∈ A₀, ∀ y ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    (s : ℕ) (u : Fin s → IrrGL (k := k)) (e₃ : (Σ a, Fin (u a).1) ≃ Fin (m + n)) (hc : ∀ a, (u a).IsCusp)
    (φ : π.IntertwiningMap (multiProd e₃ fun a => (u a).rep)) (hφ : Function.Injective φ) :
    ∃ (h h' : ℕ) (u : Fin h → IrrGL (k := k)) (w : Fin h' → IrrGL (k := k)) (hu : ∑ a, (u a).1 = m) (hw : ∑ a, (w a).1 = n),
      Finset.univ.val.map u = A₀ ∧
        ∃ f : π.IntertwiningMap (prod₂ (prodIrr u hu) (prodIrr w hw)), Function.Injective f := by
  classical
  have hAB : ∀ x ∈ A₀, x ∉ A₁ := fun x hx hx' => hU x hx x hx' 0 (by simp) (by simp)
  have hn₁ : (A₁.map Sigma.fst).sum = n := by
    have h := hA.sum_fst
    rw [Multiset.map_add (f := _), Multiset.sum_add, hm₀, Fintype.card_fin] at h
    omega
  have hS₁ : HasSupport π (Finset.univ.val.map u) :=
    ⟨s, u, rfl, hA.isIrreducible, fun a => ⟨(hc a).1, (u a).2.rep.irr, (hc a).2⟩, e₃, .of_injective φ hφ⟩
  have hm : Finset.univ.val.map u = A₀ + A₁ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hS₁ hA
  let S : Finset (Fin s) := Finset.univ.filter fun a => u a ∈ A₁
  let σ : ∀ a, GlobalTheory.SplitRead.Irr k (u a).1 := fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (u a).2.rep
  have mem : ∀ a, u a ∈ A₀ ∨ u a ∈ A₁ := fun a =>
    Multiset.mem_add.1 (hm ▸ Multiset.mem_map_of_mem u (Finset.mem_univ a))
  have mem1 : ∀ a, a ∈ S → u a ∈ A₁ := fun a ha => (Finset.mem_filter.1 ha).2
  have mem0 : ∀ a, a ∉ S → u a ∈ A₀ := fun a ha =>
    (mem a).resolve_right fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have mS : S.val.map u = A₁ := by
    have h : S.val.map u = (Finset.univ.val.map u).filter (· ∈ A₁) := by
      rw [Multiset.filter_map]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_self.2 (fun x hx => hx), zero_add]
  have mC : Sᶜ.val.map u = A₀ := by
    have h : Sᶜ.val.map u = (Finset.univ.val.map u).filter (· ∉ A₁) := by
      rw [Multiset.filter_map, Finset.compl_filter]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_self.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_nil.2 (fun x hx h => h hx), add_zero]
  have deg : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL (k := k))), T.val.map u = C →
      ∑ a : Fin T.card, (u (T.orderEmbOfFin rfl a)).1 = (C.map Sigma.fst).sum := by
    intro T C h
    rw [← h, ← GlobalTheory.CompanionTheory.Hypotheses₂.TD.map_orderEmb T u, Multiset.map_map]
    rfl
  have c₁ : ∑ a : Fin Sᶜ.card, (u (Sᶜ.orderEmbOfFin rfl a)).1 = m := (deg _ _ mC).trans hm₀
  have c₂ : ∑ a : Fin S.card, (u (S.orderEmbOfFin rfl a)).1 = n := (deg _ _ mS).trans hn₁
  have hΦ := _root_.GlobalTheory.ProdReorder.reorder_split k s (fun a => (u a).1) σ S m n e₃
    (stdBlocks (fun a => (u (Sᶜ.orderEmbOfFin rfl a)).1) c₁) (stdBlocks (fun a => (u (S.orderEmbOfFin rfl a)).1) c₂)
    (fun a b ha hb n _ _ f f' => GlobalTheory.CompanionTheory.Hypotheses₂.TDZ.commute_pair hG hBZ hZ (fun i => u (![a, b] i)) (hc a) (hc b)
      (hU _ (mem0 a ha) _ (mem1 b hb)) f f')
  exact hΦ.elim fun Φ => ⟨_, _, fun a => u (Sᶜ.orderEmbOfFin rfl a), fun a => u (S.orderEmbOfFin rfl a), c₁, c₂,
    (GlobalTheory.CompanionTheory.Hypotheses₂.TD.map_orderEmb _ u).trans mC, Φ.toIntertwiningMap.comp φ, Φ.toLinearEquiv.injective.comp hφ⟩

theorem UpperTheory.Lit.Mix.front :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin (m + n)) k) V) (A₀ A₁ : Multiset (IrrGL (k := k))), HasSupport σ (A₀ + A₁) → (A₀.map Sigma.fst).sum = m → (∀ x ∈ A₀, ∀ y ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) → ∃ (h h' : ℕ) (u : Fin h → IrrGL (k := k)) (w : Fin h' → IrrGL (k := k)) (hu : ∑ a, (u a).1 = m) (hw : ∑ a, (w a).1 = n), Finset.univ.val.map u = A₀ ∧ ∃ f : σ.IntertwiningMap (prod₂ (prodIrr u hu) (prodIrr w hw)), Function.Injective f := by
  intro hG hBZ hZ k _ _ _ _ m n V _ _ π A₀ A₁ hA hm₀ hU
  exact (GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k _ (GlobalTheory.SplitRead.Irr.mk V π hA.isSmooth hA.isIrreducible)).elim fun s H =>
    H.elim fun u H => H.elim fun e H => H.2.elim fun φ hφ =>
      UpperTheory.Lit.Mix.front_support_decomposition hG hBZ hZ k m n V π A₀ A₁ hA hm₀ hU s u e H.1 φ hφ
end

