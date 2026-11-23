module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtShl

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EquivTripleProductOfIso
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdFlatten

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso in
theorem product_append_iso {p q r t : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (h : ∑ a, (Fin.append x y a).1 = r + t) : Iso (two rfl (pr x hx) (pr y hy)) (pr (Fin.append x y) h) :=
  GlobalTheory.T.product_irreducible_append_equiv k p q r t x y hx hy h

theorem pr_app {p q c r t N : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (z : Fin c → IrrGL (k := k))
    (e : List.ofFn z = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (z a).1 = N)
    (h : r + t = N) : Iso (pr z hz) (two h (pr x hx) (pr y hy)) := by
  subst h
  have h' : ∑ a, (Fin.append x y a).1 = r + t := by
    rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hx, hy]
  exact iso_trans (pr_congr (e.trans (List.ofFn_fin_append x y).symm) hz h') (iso_symm (product_append_iso x y hx hy h'))

theorem sum_get_eq' (L : List (IrrGL (k := k))) : ∑ a, (L.get a).1 = (L.map fun x => x.1).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp

theorem stage3_iso (A M B : List (IrrGL (k := k))) {N nA nM nB m' : ℕ} (hd : ∑ a, ((A ++ M ++ B).get a).1 = N)
    (hA : ∑ a, (A.get a).1 = nA) (hM : ∑ a, (M.get a).1 = nM) (hB : ∑ a, (B.get a).1 = nB)
    (h2 : nM + nB = m') (h1 : nA + m' = N) :
    Iso (pr (A ++ M ++ B).get hd) (two h1 (pr A.get hA) (two h2 (pr M.get hM) (pr B.get hB))) := by
  have hMB : ∑ a, ((M ++ B).get a).1 = m' := by
    rw [sum_get_eq', List.map_append, List.sum_append, ← sum_get_eq', ← sum_get_eq', hM, hB, h2]
  exact iso_trans (pr_app A.get (M ++ B).get _ ((List.ofFn_get _).trans ((List.append_assoc A M B).trans (congrArg₂ _ (List.ofFn_get A).symm (List.ofFn_get (M ++ B)).symm))) hA hMB hd h1)
    (two_congr h1 (iso_refl _) (pr_app M.get B.get _ (by simp only [List.ofFn_get]) hM hB hMB h2))


end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem geometricLemmaGL : GlobalTheory.Published.GeometricLemma :=
  fun k _ _ _ _ => ⟨_root_.GlobalTheory.CompanionTheory.GeoAssembly.jacquetOfInducedFiltration k, _root_.GlobalTheory.CompanionTheory.Glob.cellSemisimplification k⟩

theorem embL_of_eq {x : IrrGL (k := k)} {l : List (IrrGL (k := k))} {y : Fin l.length → IrrGL (k := k)} (e : y = l.get)
    (hd : ∑ a, (y a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr y hd)) (hf : Function.Injective f) : EmbL x l := by
  subst e
  exact ⟨hd, f, hf⟩

theorem embL_pair {x : IrrGL (k := k)} {y : Fin 2 → IrrGL (k := k)} {hd : ∑ a, (y a).1 = x.1}
    {f : x.rep.IntertwiningMap (prodIrr y hd)} (hf : Function.Injective f) : EmbL x [y 0, y 1] :=
  embL_of_eq (l := [y 0, y 1]) (y := y) (funext fun i => by fin_cases i <;> rfl) hd f hf

theorem embL_nil (x : IrrGL (k := k)) (h0 : x.1 = 0) : EmbL x [] := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 0 := h0
  have hd : ∑ a : Fin ([] : List (IrrGL (k := k))).length, (([] : List (IrrGL (k := k))).get a).fst =
      (⟨0, c⟩ : IrrGL (k := k)).fst := by simp
  obtain ⟨E⟩ : Nonempty ((prodIrr ([] : List (IrrGL (k := k))).get hd).Equiv (IrrGL.rep ⟨0, c⟩)) :=
    exh_equiv_zero _ _ (PiTensorProduct.isEmptyEquiv (Fin 0)) _ c.rep.irr
  exact ⟨hd, E.symm.toIntertwiningMap, fun a b hab => E.symm.toLinearEquiv.injective hab⟩


variable (k) in
theorem cuspEmbP (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hR : RefineP k) : CuspEmbP k := by
  have hJ : JacquetSubLeft k := _root_.GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft hA
  suffices H : ∀ n : ℕ, ∀ x : IrrGL (k := k), x.1 = n → ∃ l : List (IrrGL (k := k)), (∀ ρ ∈ l, ρ.IsCusp) ∧ EmbL x l from
    fun x => H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · exact ⟨[], by simp, embL_nil x h0⟩
    obtain ⟨y, hd, hc, f, hf⟩ := hJ x hpos
    have h2 : (y 1).1 < n := by
      have := hc.1
      rw [Fin.sum_univ_two] at hd
      omega
    obtain ⟨l, hl, hy⟩ := ih _ h2 (y 1) rfl
    refine ⟨y 0 :: l, fun ρ hρ => ?_, ?_⟩
    · rcases List.mem_cons.1 hρ with rfl | hρ
      exacts [hc, hl ρ hρ]
    · simpa using hR x (y 1) [y 0] l [] hy (by simpa using embL_pair hf)


variable (k) in
theorem suppP : SuppP k := by
  intro x a y l 𝔫 hl hx hxy hy Δ hΔ
  obtain ⟨hd, f, hf⟩ := hx
  obtain ⟨hd2, g, hg⟩ := hxy
  have hG := geometricLemmaGL
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have h1 : HasSupport x.rep (Finset.univ.val.map l.get) :=
    hasSupport_of_isSubquotient x.2.rep.irr (fun i => hl _ (List.get_mem l i)) (.of_injective f hf)
  obtain ⟨h, z, hdz, ⟨D, ⟨hD, -⟩, hz⟩, hcos⟩ := hy
  have hsy : HasSupport y.rep (∑ i, (D i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hz i).hasSupport) y.2.rep.irr
      hcos.isSubquotient
  obtain ⟨sa, hsa⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG a
  have ht : ∀ i, HasSupport (([a, y] : List (IrrGL (k := k))).get i).rep (![sa, ∑ i, (D i).ms] i) := by
    intro i
    fin_cases i
    exacts [hsa, hsy]
  have h2 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr ht x.2.rep.irr (.of_injective g hg)
  have heq := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ h1 h2
  rw [← hD] at hΔ
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hΔ
  have heq' : Finset.univ.val.map l.get = sa + ∑ i, (D i).ms := heq.trans (Fin.sum_univ_two _)
  have hm : (D j).first ∈ sa + ∑ i, (D i).ms := by
    refine Multiset.mem_add.2 (Or.inr (Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, ?_⟩))
    exact Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, (D j).len_pos, by simp⟩)
  rw [← heq'] at hm
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hm
  rw [← hi]
  exact List.get_mem l i

theorem irreducibleAdmissibleGL : GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun k _ _ _ _ n => _root_.GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n)


variable (k) in
theorem cuspEmbP_of_refine (hR : RefineP k) : CuspEmbP k :=
  cuspEmbP k irreducibleAdmissibleGL hR

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtPOfFineUniq
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem juxtP (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hM : MidP k) (hR : RefineP k) (hS : SwapP k)
    (hC : CuspEmbP k) (hW : ShlP k) (hD : DecLP k) : JuxtP k := by
  intro σ b Δ hb hσ
  change SubqL σ [nxt Δ, b] at hσ
  change IsLSeg (up Δ) σ.rep ∨ EmbL σ [b, nxt Δ]
  obtain ⟨l, hl, he⟩ := hC σ
  obtain ⟨P, Q, h1, rfl⟩ := words_of_subq hA hW σ b Δ hb hσ l hl he
  rcases eq_or_ne P [] with rfl | hP
  · left
    refine hD (up Δ) σ ?_
    rw [decW_up]
    simp only [List.nil_append] at h1 he
    rw [h1]
    exact he
  · right
    have h2 := emb_move_end hA hS σ Δ P Q h1 hP he
    obtain ⟨τ, -, h3⟩ := hM σ [] (decW Δ) [nxt Δ] (by simpa using h2)
    obtain ⟨u, hu, h4⟩ := hC τ
    have h5 : EmbL σ (u ++ [nxt Δ]) := by simpa using hR σ τ [] u [nxt Δ] h4 h3
    obtain ⟨P', Q', h6, h7⟩ := words_of_subq hA hW σ b Δ hb hσ (u ++ [nxt Δ])
      (by
        intro ρ hρ
        rcases List.mem_append.1 hρ with h | h
        · exact hu ρ h
        · rw [List.mem_singleton.1 h]; exact Δ.isCusp_first.nu _) h5
    have h8 := eq_decW_of_append hA Δ u P' Q' h6 h7
    subst h8
    have h9 := eq_of_isLSeg Δ τ b (hD Δ τ h4) hb
    subst h9
    simpa using h3

theorem juxtP_of_fineUniq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hM : MidP k) (hR : RefineP k) (hS : SwapP k)
    (hC : CuspEmbP k) (hW : ShlP k) (hF : FineUniqP k) : JuxtP k :=
  juxtP hA hM hR hS hC hW (decLP hF)

end PositivityTheory.Exh

end
end

