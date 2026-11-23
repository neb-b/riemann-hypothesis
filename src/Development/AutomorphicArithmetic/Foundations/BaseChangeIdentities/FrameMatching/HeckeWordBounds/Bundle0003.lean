module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsilet
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psilet_pf :
    FmAlg → LocOk → FrFacts → PsiLet := by
  intro hA hO hF hR E _ _ _ n π S T F₀ F i p
  obtain ⟨g, b⟩ := p
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := (hF hR E n π S T F₀ F).2.2.2
  have hok : ∀ L, F.d.IsGen (F₀.C.a i) (F₀.C.le i) L → L.Ok F.d.P := fun L hL =>
    (hO E n F.d F.ok (F₀.C.a i) (F₀.C.le i)).2.2.2 L hL
  have hadj : ∀ L, F.d.IsGen (F₀.C.a i) (F₀.C.le i) L → adjF (F.ψ i L) = F.ψ i L.adj := fun L hL =>
    (hA E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hP L L (hok L hL) (hok L hL)).2.2.2.2
  have heL : (F.d.eL (F₀.C.a i)).adj = F.d.eL (F₀.C.a i) := by
    have hm := LocComm.adj_m F.d (a := F₀.C.a i) (ha := F₀.C.le i) (L := F.d.eL (F₀.C.a i)) (Or.inl rfl)
    have hs : (F.d.eL (F₀.C.a i)).adj.s = (F.d.eL (F₀.C.a i)).s := by
      funext w
      exact LocComm.lfStar_idem _
    have ht : (F.d.eL (F₀.C.a i)).adj.t = (F.d.eL (F₀.C.a i)).t := by
      funext w
      exact LocComm.lfStar_idem _
    cases h : F.d.eL (F₀.C.a i) with
    | mk m s t =>
      rw [h] at hm hs ht
      simp only [LM.adj] at hm hs ht ⊢
      rw [LM.mk.injEq]
      exact ⟨hm, hs, ht⟩
  have heψ : adjF (F.ψ i (F.d.eL (F₀.C.a i))) = F.ψ i (F.d.eL (F₀.C.a i)) := by
    rw [hadj _ (Or.inl rfl), heL]
  rcases g with _ | x | x
  · refine Or.inr ?_
    cases b
    · exact ⟨F.t₀ i, rfl, rfl⟩
    · exact ⟨(F.t₀ i).adj, rfl, heψ⟩
  · by_cases hi : i = x.1
    · refine Or.inr ?_
      cases b
      · exact ⟨F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, by simp [gl, RunFrame.g, hi], rfl⟩
      · refine ⟨(F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).adj, by simp [gl, RunFrame.g, hi, BGen.adj], heψ⟩
    · refine Or.inl ?_
      cases b
      · exact ⟨F.dval x, by simp [gl, RunFrame.g, hi], rfl⟩
      · exact ⟨starRingEnd ℂ (F.dval x), by simp [gl, RunFrame.g, hi, BGen.adj], rfl⟩
  · refine Or.inr ?_
    cases b
    · exact ⟨F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2), rfl, by simp [lt, locL]; rfl⟩
    · exact ⟨(F.ptL i (F.d.hL _ (F₀.C.le i) x.1.1 x.2.1 x.2.2)).adj, rfl,
        (hadj _ (Or.inr ⟨x.1.1, x.2.1, x.2.2, x.1.2.2, rfl⟩)).trans (by simp [lt, locL])⟩

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsiword
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psiword_pf :
    PsiGen → PsiLet → heckeLevelWordBase → LocOk → MLM.MatchLMId → FrFacts → PsiWord := by
  intro hG hPL hW hLO hId hFF hR E _ _ _ n π S T F₀ F i ws
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  have hE := hW E n F.d F.ok (F₀.C.a i) ha (.inr (.inl ()))
  have hB := hW E n F.d F.ok (F₀.C.a i) ha (.inl ())
  have hFx : (F.d.fixL (F₀.C.a i)).Ok F.d.P := (hLO E n F.d F.ok (F₀.C.a i) ha).2.2.1
  have hFe : ((F.d.eL (F₀.C.a i)).mul (F.d.fixL (F₀.C.a i))).Eqv F.d.P (F.d.fixL (F₀.C.a i)) :=
    (hId E n F.d F.ok (F₀.C.a i) ha _ (Or.inr (Or.inl rfl))).2
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := (hFF hR E n π S T F₀ F).2.2.2
  let l : List (BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) :=
    (Sum.inr (F.t₁ i), F.d.fixL (F₀.C.a i)) ::
      (ws.map fun w => List.replicate F.m
          ((Sum.inr (F.β i), F.d.betaL (F₀.C.a i) ha) : BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) ++
        w.map fun p => (gl F i p, locL F.d (F₀.C.a i) ha (lt F p))).flatten
  have e1 : l.map Prod.fst = Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten := by
    simp only [l, bw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e2 : (l.map Prod.snd).foldr LM.mul (F.d.eL (F₀.C.a i)) = prodL F.d (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws) (F₀.C.a i) := by
    have : l.map Prod.snd = F.d.fixL (F₀.C.a i) :: (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws).map (locL F.d (F₀.C.a i) ha) := by
      simp only [l, UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
      rfl
    rw [this, prodL, dite_eq_left ha]
  have hl : ∀ x ∈ l, x.2.Ok F.d.P ∧ ((F.d.eL (F₀.C.a i)).mul x.2).Eqv F.d.P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = F.d.eL (F₀.C.a i)) ∨
        ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) x.2) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hFx, hFe, Or.inr ⟨_, rfl, rfl⟩⟩
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatten.1 hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
      rcases List.mem_append.1 hxy with h | h
      · rw [List.eq_of_mem_replicate h]
        exact ⟨hB.1, hB.2.1, Or.inr ⟨_, rfl, rfl⟩⟩
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
        have hp := hW E n F.d F.ok (F₀.C.a i) ha (lt F p)
        refine ⟨hp.1, hp.2.1, ?_⟩
        rcases hPL hR E n π S T F₀ F i p with ⟨c, h1, h2⟩ | ⟨s, h1, h2⟩
        · exact Or.inl ⟨c, h1, h2⟩
        · exact Or.inr ⟨s, h1, h2⟩
  have key := hG E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hP (F₀.u₁ _) (F₀.u₂ _)
    (F.d.eL (F₀.C.a i)) (F.t₂ i) hE.1 hE.2.1 rfl l hl
  rw [e1, e2] at key
  exact key

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PTraceword
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.traceword_pf :
    U.UWord → LocMatch → ChainSc → FBL.EllHom → AdelWord → ArchSc → USph → UOk → FrFacts → TraceWord := by
  intro hUW hLM hCS hEH hAW hAS hUS hUO hFF hR E _ _ _ n π S T F₀ F hE hF ws hws
  obtain ⟨hμ, hnorm, hgood, hP⟩ := hFF hR E n π S T F₀ F
  obtain ⟨hcnt, hsph⟩ := hUS hR E n π S T F₀ F ws
  have hk : 1 ≤ ws.length := List.length_pos_iff.2 hws
  obtain ⟨hHecke, hsep, hall⟩ := hLM E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne hnorm hgood (lw F ws) F.m ws.length
    F.m_pos hk hcnt (ws.flatten.map (ul F)) (fun w _ => hsph w)
  have hlU : ∀ x ∈ ws.flatten.map (ul F), U.UGen.Ok F₀.Sec F.d.B x := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact (hUO hR E n π S T F₀ F hE p).1
  obtain ⟨hT, htr⟩ := hUW E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff hHecke ws.length _ hlU
  rw [htr hsep]
  have hch := hCS E n F₀.μ F₀.e F₀.lam F₀.C F₀.Sec F₀.hSec F.d.KU _ F.levOff.2.1 hT F₀.u₁ F₀.u₂ F₀.hu
    (fun a => (prodL F.d (lw F ws) a).tr F.d.P F.d.one) (fun a => (prodL F.d (lw F ws) a).t)
    (fun a ha => by
      obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hall a ha
      refine ⟨h1, h2, h3, fun w hw => ?_⟩
      rw [← hμ w]
      exact h4 w hw)
    (fun i => by
      obtain ⟨-, w, hw, hns, hreg⟩ := hall (F₀.C.a i) (F₀.C.le i)
      refine ⟨w, hw, ?_⟩
      have : seen ((prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one) (prodL F.d (lw F ws) (F₀.C.a i)).t w =
          (prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one w := by
        funext y
        simp [seen, hns]
      rw [this]
      exact hreg)
    (fun i v => (tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v))
    (fun i => (tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb)
    (fun i v => ((hAW hR E n π S T F₀ F hF i ws).2.2 v))
    (fun i => BGen.sc (ws.map (bw F i)).flatten) (U.UGen.sc (ws.flatten.map (ul F)))
    (fun i => by
      rw [Finset.prod_mul_distrib]
      exact hAS hR E n π S T F₀ F hF i ws)
  rw [hch]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, h2, -⟩ := hAW hR E n π S T F₀ F hF i ws
  rw [h1, hEH]
  field_simp

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.TwokPf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (l : List (BGen B)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s, Sum.inr s ∈ l → s.T ≤ R ∧ s.r + B.c ≤ R := by
  induction l with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons g l ih =>
    obtain ⟨R, hR, hs⟩ := ih
    rcases g with c | t
    · refine ⟨R, hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
      · exact hs s h
    · refine ⟨max R (max t.T (t.r + B.c)), le_max_of_le_left hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
        exact ⟨le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
      · exact ⟨(hs s h).1.trans (le_max_left _ _), (hs s h).2.trans (le_max_left _ _)⟩

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.twok_pf :
    BlockWordOperators → TwOk := by
  intro hW hR E _ _ _ n π S T F₀ F h i
  have hadj := (hW E (F.B i) [] (F.t₂ i) 0 (by simp) (h.tok i).2 le_rfl (by simp)).2.2.2.2.1
  have hgl : ∀ p, (gl F i p).Ok ∧ (gl F i p).op = if p.2 then star (F.g p.1 i).op else (F.g p.1 i).op := by
    rintro ⟨x, s⟩
    cases s with
    | false => exact ⟨h.ok x i, rfl⟩
    | true =>
      refine ⟨(hadj _ (h.ok x i)).1, ?_⟩
      show (F.g x i).adj.op = star (F.g x i).op
      rw [(hadj _ (h.ok x i)).2, ContinuousLinearMap.star_eq_adjoint]
  have hbw : ∀ w, ∀ g ∈ bw F i w, g.Ok := by
    intro w g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.eq_of_mem_replicate hg]
      exact h.βok i
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
      exact (hgl p).1
  refine ⟨hgl, hbw, fun ws => ?_⟩
  obtain ⟨R, hR0, hRs⟩ := exists_bound (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten)
  refine (hW E (F.B i) _ (F.t₂ i) R ?_ (h.tok i).2 hR0 hRs).1
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact (h.tok i).1
  · obtain ⟨l, hl, hgl'⟩ := List.mem_flatten.1 hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    exact hbw w g hgl'

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.UokPf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.uok_pf :
    U.UAdj → HuHecke → UOk := by
  intro hA hH hR E _ _ _ n π S T F₀ F hE p
  have hB : ∀ {w : Pl E}, F.d.Good w → w ∉ F.d.B := by
    intro w hw
    obtain ⟨-, hT, hS, hB, -⟩ := hw
    simp [LocData.B, hT, hS, hB]
  have hok : ∀ x, (F.ug x).Ok F₀.Sec F.d.B := by
    intro x
    rcases x with _ | x | x
    · exact trivial
    · exact trivial
    · exact ⟨x.1.2.1, hB x.1.2.2, hH E n F.d F.ok _ x.1.2.2 x.2.1⟩
  obtain ⟨x, b⟩ := p
  have hadj := hA E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff (F.ug x) (hok x)
  cases b
  · simpa [ul] using hok x
  · simpa [ul] using hadj

end
end

