module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0056
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0048
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0007

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EquivTripleProductOfIso
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdFlatten

namespace CompanionTheory.Exh

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


end CompanionTheory.Exh

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace CompanionTheory.Exh

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
  have hd : ∑ a, (([] : List (IrrGL (k := k))).get a).1 = (⟨0, c⟩ : IrrGL (k := k)).1 := by simp
  obtain ⟨φ⟩ := exh_equiv_zero (stdBlocks (fun a => (([] : List (IrrGL (k := k))).get a).1) hd)
    (piTensor fun a => (([] : List (IrrGL (k := k))).get a).rep) (PiTensorProduct.isEmptyEquiv (Fin 0)) c.rep.ρ c.rep.irr
  exact ⟨hd, φ.symm.toIntertwiningMap, fun v w h => φ.symm.toLinearEquiv.injective h⟩


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

end CompanionTheory.Exh

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtShl
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

section Comb

variable {T : Type*}

theorem interleave_nil_left {v w : List T} (h : Zc.Comb.Interleave [] v w) : w = v := by
  generalize hu : ([] : List T) = u at h
  induction h with
  | nil => rfl
  | left _ _ => cases hu
  | right _ ih => rw [ih hu]

theorem interleave_nil_right {u w : List T} (h : Zc.Comb.Interleave u [] w) : w = u := by
  generalize hv : ([] : List T) = v at h
  induction h with
  | nil => rfl
  | left _ ih => rw [ih hv]
  | right _ _ => cases hv

theorem interleave_single {a : T} {v w : List T} (h : Zc.Comb.Interleave [a] v w) :
    ∃ P Q : List T, v = P ++ Q ∧ w = P ++ a :: Q := by
  generalize hu : [a] = u at h
  induction h with
  | nil => cases hu
  | @left a' u v w h _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hu
    exact ⟨[], v, rfl, by rw [interleave_nil_left h]; rfl⟩
  | @right a' u v w _ ih =>
    obtain ⟨P, Q, rfl, rfl⟩ := ih hu
    exact ⟨a' :: P, Q, rfl, rfl⟩

theorem shuffle_two_single {a : T} {D w : List T} (h : Zc.Comb.Shuffle [[a], D] w) :
    ∃ P Q : List T, D = P ++ Q ∧ w = P ++ a :: Q := by
  cases h with
  | cons hs hi =>
    cases hs with
    | cons hs' hi' =>
      cases hs'
      rw [interleave_nil_right hi'] at hi
      exact interleave_single hi

end Comb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_single (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : decW (Segment.single ρ hρ) = [ρ] := by
  simp [decW, Segment.single, Segment.term]

theorem words_of_subq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hW : ShlP k) (σ b : IrrGL (k := k)) (Δ : Segment k)
    (hb : IsLSeg Δ b.rep) (hσ : SubqL σ [nxt Δ, b]) (l : List (IrrGL (k := k))) (hl : ∀ ρ ∈ l, ρ.IsCusp) (he : EmbL σ l) :
    ∃ P Q : List (IrrGL (k := k)), decW Δ = P ++ Q ∧ l = P ++ nxt Δ :: Q := by
  obtain ⟨hd1, hsub⟩ := hσ
  obtain ⟨hd2, f, hf⟩ := he
  have := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible σ.2.rep.irr
  have hnt : ∃ v, f v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : σ.2.rep.V)
    exact ⟨v, fun h => hv (hf (h.trans (f.toLinearMap.map_zero).symm))⟩
  have h1 : 1 ≤ jm l.get hd2 σ.rep := GlobalTheory.T.jacquet_multiplicity_pos hA l.get hd2 σ.rep σ.2.rep.smooth f hnt
  have hwd : Wd σ.rep l := ⟨hd2, by intro h; rw [h] at h1; simp at h1⟩
  have hwd2 : Wd (prodIrr [nxt Δ, b].get hd1) l :=
    GlobalTheory.T.word_occurs_of_subquotient _ σ.rep (isSmooth_prodIrr _ _) hsub l hwd
  have hc : (nxt Δ).IsCusp := Δ.isCusp_first.nu _
  obtain ⟨L, hL, hsh⟩ := hW [nxt Δ, b].get hd1 ![Segment.single (nxt Δ) hc, Δ] (by
      intro i
      fin_cases i
      · exact (single_spec hc).2.1
      · exact hb) l hl hwd2
  have hL' : L.Perm [Segment.single (nxt Δ) hc, Δ] := by
    rw [← Multiset.coe_eq_coe, hL]
    simp [Fin.univ_val_map]
  have h2 := GlobalTheory.T.shuffle_of_perm _ _ l hsh (hL'.map decW)
  rw [List.map_cons, List.map_cons, List.map_nil, decW_single] at h2
  exact shuffle_two_single h2

end CompanionTheory.Exh

end
end

