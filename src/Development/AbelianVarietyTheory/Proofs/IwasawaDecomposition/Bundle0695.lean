module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFramesLatticesModelsAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel
variable {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}


set_option maxHeartbeats 4000000 in
theorem ΛV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛV i) (z'.R.ΛV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛV) i).symm


set_option maxHeartbeats 4000000 in
theorem ΛW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.ΛW i) (z'.R.ΛW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.ΛW) i).symm


set_option maxHeartbeats 4000000 in
theorem βV_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βV i) (z'.R.βV i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βV) i).symm


set_option maxHeartbeats 4000000 in
theorem βW_at (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    HEq (z.R.βW i) (z'.R.βW i') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact heq_of_eq (congrFun (eq_of_heq hx.βW) i).symm


set_option maxHeartbeats 4000000 in
theorem sameVec_gen (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar} {S' : (w'.st Z').toD7.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Formalism.IndefR.Links.Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (g : HEq M'.fr M.fr)
    (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v) : GlobalTheory.TwInputs.Move.SameVec v v' := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d g
  cases a; cases b; cases c; cases d; cases g
  intro τ τ' hτ
  cases hτ
  have e := eq_of_heq hv
  subst e
  rfl


set_option maxHeartbeats 4000000 in
theorem v₀_of_extN (q : B'.toPre = B.toPre) (hx : ExtN z z') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    GlobalTheory.TwInputs.Move.SameVec (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) :=
  have h := hx.MW i i' hi
  sameVec_gen q i i' hi _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 _ _ h.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.HeightCounting.SerMove.FrameValuesAtLevel

namespace GlobalTheory.HeightCounting.SerMove


set_option maxHeartbeats 4000000 in
theorem frames_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Frames (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have q : B'.toPre = B.toPre := l.enl.1
  have hx := l.extN
  refine ⟨hx.Pg.symm, hx.ψ.symm, hx.θ.symm, fun j j' h => FrameValuesAtLevel.ΛV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.ΛW_at q hx j j' h,
    fun j j' h => FrameValuesAtLevel.βV_at q hx j j' h, fun j j' h => FrameValuesAtLevel.βW_at q hx j j' h,
    fun j j' h => ((hx.BV j j' h).2.2.2.2.2).symm, fun j j' h => ((hx.BV j j' h).2.2.1).symm, fun j j' h => ?_, fun j j' h => ?_⟩
  · show GlobalTheory.TwInputs.Move.SameModel (x.m.z.R.MW j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (x'.m.z.R.MW j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    have m := hx.MW j j' h
    exact ⟨m.1.symm, m.2.1.symm, m.2.2.1.symm, m.2.2.2.1.symm, m.2.2.2.2.1.symm, m.2.2.2.2.2.1.symm, m.2.2.2.2.2.2.1.symm⟩
  · show GlobalTheory.TwInputs.Move.SameVec (g.v₀ j (Formalism.IndefR.Links.sg0 (Dof x) (sideAt x g hg a).A3.A)) (g'.v₀ j' (Formalism.IndefR.Links.sg0 (Dof x') (sideAt x' g' hg' a').A3.A))
    rw [GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a), GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a')]
    exact FrameValuesAtLevel.v₀_of_extN q hx j j' h

end GlobalTheory.HeightCounting.SerMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesGeometricActionsCorrespond
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr

noncomputable section

section General
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.HeightCounting.SerMove.RhoLink

open Formalism.IndefR.FWT GlobalTheory.Mem.R3.GoodBC

theorem rel_of_span {LL LL' : Type} [Field LL] [Field LL'] (φ : LL →+* LL') {n n' : ℕ} (hn : n = n')
    (S : Set (Fin n → LL)) (hS : Submodule.span LL S = ⊤)
    (ρ : (Fin n → LL) →ₗ[LL] (Fin n → LL)) (ρ' : (Fin n' → LL') →ₗ[LL'] (Fin n' → LL'))
    (h : ∀ s ∈ S, ∀ (x' : Fin n' → LL'), (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (s k)) →
      ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ s k))
    (x : Fin n → LL) (x' : Fin n' → LL') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ x k) := by
  subst hn
  have hx' : x' = cw φ x := funext fun k => hx k k rfl
  subst hx'
  have key : ∀ y ∈ Submodule.span LL S, ρ' (cw φ y) = cw φ (ρ y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      funext k
      exact h s hs (cw φ s) (fun k k' hk => by rw [Fin.ext hk]; rfl) k k rfl
    | zero => rw [cw_zero, map_zero, map_zero, cw_zero]
    | add a b _ _ ha hb => rw [cw_add, map_add (f := _), ha, hb, map_add (f := _), cw_add]
    | smul c a _ ha => rw [cw_smul, LinearMap.map_smul, ha, LinearMap.map_smul, cw_smul]
  intro k k' hk
  rw [← Fin.ext hk]
  exact congrFun (key x (hS ▸ Submodule.mem_top)) k

variable {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
  {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Wt' : Set B'.places.Pl}


set_option maxHeartbeats 2000000 in
theorem cusp_gen (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z'.core.R ((j' : ℕ) + 1) = z.core.R ((j : ℕ) + 1) ∧
    (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r → (r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n ↔ r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) ∧
    (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (h : r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) (h' : r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n), HEq r' r →
      HEq (⟨r', h'⟩ : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) (⟨r, h⟩ : z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e
  obtain ⟨h1, h2, h3⟩ := hx.κ j' j' rfl
  have e1 : (z'.geo.κ j').aP = (z.geo.κ j').aP := eq_of_heq h1
  have e2 : (z'.geo.κ j').aM = (z.geo.κ j').aM := eq_of_heq h2
  have hw : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j') := by
    funext x
    unfold Formalism.L2.Pj.wtA
    rw [e1, e2]
    rfl
  obtain ⟨hR, hm, hs⟩ := GlobalTheory.Mem.R3.CuspExt.cusp_heq (r := (w.st Z).toD7.R.r) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.U hw h3 ((j' : ℕ) + 1)
  exact ⟨hR, hm, hs⟩


set_option maxHeartbeats 2000000 in
theorem act_gen (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px) (hg : HEq g' g)
    (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (hr : HEq r' r) :
    HEq (Formalism.L2.Pj.actLev z'.core.Q.c (z'.geo.O j').lev2 g' r') (Formalism.L2.Pj.actLev z.core.Q.c (z.geo.O j).lev2 g r) := by
  have hA := GlobalTheory.OneMapAllCompare.second_level_eq_one (z.geo.pins j).2.cov ()
  have h : GlobalTheory.Mem.R3.ActExt.LevB _ j z.R.Pg z.R.βW z.R.eG (z.core.iota _) _ _ (z.geo.O j).lev := (z.geo.pins j).2.lift.lev
  have h' : GlobalTheory.Mem.R3.ActExt.LevB _ j' z'.R.Pg z'.R.βW z'.R.eG (z'.core.iota _) _ _ (z'.geo.O j').lev := (z'.geo.pins j').2.lift.lev
  have hU := letI := z.alg; GlobalTheory.LevelUnique.levUnique _ _ _ _ _ z.core z.R.toRealDat z.lev.is z.geo.fw.laws ((z.geo.pins j).2.tuple ()).half.1 j
  have e1 := hx.H
  have e2 := hx.l
  have e3 := hx.c
  have e4 := hx.Dw
  have e5 := hx.Xo
  have e6 := hx.iota
  have e7 := hx.Pg
  have e8 := hx.βW
  have e9 := hx.eG
  clear hx
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hB
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  obtain ⟨j', hj'⟩ := j'
  dsimp only at hj
  subst hj
  exact GlobalTheory.Mem.R3.ActExt.act_heq (w.st Z).toD7 j ((j : ℕ) + 1) e1 e2 e3 e4 e5 e6 e7 e8 e9 hA hU h h' g g' hg r r' hr


set_option maxHeartbeats 4000000 in
theorem rho_gen     (hB : B'.toPre = B.toPre) (hf : HEq f' f) (hpx : HEq w'.px w.px)
    {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hx : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL) (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px) (hg : HEq g' g)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hxx' : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → (z'.R.toRealDat.FW j').ρ g' x' k' = φ ((z.R.toRealDat.FW j).ρ g x k) := by
  obtain ⟨hR, hmem, hsub⟩ := cusp_gen hB z z' hx j j' hj
  have hact := act_gen hB hf hpx z z' hx j j' hj
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P => P.R.m) hB
  have hn : z'.R.nW j' = z.R.nW j := nat_heq_app hm z.R.nW z'.R.nW hx.nW j j' hj
  obtain ⟨eG, heG⟩ := gc_iso (w.st Z).B (w'.st Z').B hB w.px w'.px hpx
  have hF : ∀ f f', HEq f' f → ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' →
      ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) k' =
        φ (((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) k) :=
    fun f f' h k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hx.forms j j' hj f f' h k k' hk).trans (hφ _).symm)
  have hkeep : ActKeeps (κ := z'.geo.κ) z'.geo.O j' ↔ ActKeeps (κ := z.geo.κ) z.geo.O j := by
    constructor
    · intro hk g0 f0 hf0
      have hr : HEq (cast hR.symm f0) f0 := cast_heq _ _
      have h1 := hk (eG g0) (cast hR.symm f0) ((hmem _ _ hr).2 hf0)
      exact (hmem _ _ (hact g0 (eG g0) (heG g0) f0 _ hr)).1 h1
    · intro hk g0' f0' hf0'
      have hr : HEq f0' (cast hR f0') := (cast_heq _ _).symm
      have hg0 : HEq g0' (eG.symm g0') := by
        have := heG (eG.symm g0')
        rwa [MulEquiv.apply_symm_apply] at this
      have h1 := hk (eG.symm g0') (cast hR f0') ((hmem _ _ hr).1 hf0')
      exact (hmem _ _ (hact _ _ hg0 _ _ hr)).2 h1
  by_cases hk : ActKeeps (κ := z.geo.κ) z.geo.O j
  · have A := (z.geo.rhoGeo j).1 hk
    have A' := (z'.geo.rhoGeo j').1 (hkeep.2 hk)
    have hS : Submodule.span (w.st Z).toD7.what₂.LL ((z.R.FW j).WK : Set (Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL)) = ⊤ := by
      obtain ⟨m, b, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
      exact top_unique (hsp ▸ Submodule.span_mono (Set.range_subset_iff.2 hb))
    refine rel_of_span φ hn.symm _ hS ((z.R.toRealDat.FW j).ρ g) ((z'.R.toRealDat.FW j').ρ g') ?_ x x' hxx'
    intro s hs y' hy' k k' hk'
    obtain ⟨f0, hf0⟩ : ∃ f0, f0 = (z.geo.fw.e j).symm ⟨s, hs⟩ := ⟨_, rfl⟩
    have hs0 : ((z.geo.fw.e j f0 : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = s := by
      rw [hf0, LinearEquiv.apply_symm_apply]
    have hr : HEq (cast hR.symm (f0 : z.core.R ((j : ℕ) + 1))) (f0 : z.core.R ((j : ℕ) + 1)) := cast_heq _ _
    obtain ⟨f0', hf0'⟩ : ∃ f0' : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n,
        (f0' : z'.core.R ((j' : ℕ) + 1)) = cast hR.symm (f0 : z.core.R ((j : ℕ) + 1)) :=
      ⟨⟨_, (hmem _ _ hr).2 f0.2⟩, rfl⟩
    have hff : HEq f0' f0 := hsub f0.1 f0'.1 f0.2 f0'.2 (hf0' ▸ hr)
    have hy : ((z'.geo.fw.e j' f0' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = y' := by
      funext k1'
      have e1 := hF f0 f0' hff (Fin.cast hn k1') k1' rfl
      rw [e1, hs0, hy' (Fin.cast hn k1') k1' rfl]
    obtain ⟨h1, e1⟩ := A g f0
    obtain ⟨h1', e1'⟩ := A' g' f0'
    have hh := hsub _ _ h1 h1' (hact g g' hg _ _ (hf0' ▸ hr))
    rw [← hy, ← e1', hF _ _ hh k k' hk', e1, hs0]
  · have e0 : (z.R.toRealDat.FW j).ρ g = 1 := (z.geo.rhoGeo j).2 hk g
    have e0' : (z'.R.toRealDat.FW j').ρ g' = 1 := (z'.geo.rhoGeo j').2 (fun h => hk (hkeep.1 h)) g'
    intro k k' hk'
    rw [e0, e0', Module.End.one_apply, Module.End.one_apply]
    exact hxx' k k' hk'

end GlobalTheory.HeightCounting.SerMove.RhoLink
end General

theorem GlobalTheory.HeightCounting.SerMove.rho_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → ∀ (u : (sideAt x g hg a).Γ) (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → ((sideAt x' g' hg' a').R.FW j').ρ (γ u) y' k' = ι (((sideAt x g hg a).R.FW j).ρ u y k) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ j j' hj y y' hy u k k' hk
  exact GlobalTheory.HeightCounting.SerMove.RhoLink.rho_gen l.enl.1 l.fr l.px (datAt x g) (datAt x' g') l.extN j j' hj ι l.cp.embLL u (γ u) (hγ u) y y' hy k k' hk

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesRationalFormsCorrespondCoordinatewis
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_addEquiv_of_coord {L L' R R' : Type} [Field L] [Field L'] [Semiring R] [Semiring R'] {n n' : ℕ}
    [Module R (Fin n → L)] [Module R' (Fin n' → L')] (hn : n = n') (W : Submodule R (Fin n → L))
    (W' : Submodule R' (Fin n' → L')) (ι : L →+* L')
    (h1 : ∀ y : W, ∃ y' : W', ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → y'.1 k' = ι (y.1 k))
    (h2 : ∀ y' : W', ∃ y : W, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → y'.1 k' = ι (y.1 k)) :
    ∃ φ : W ≃+ W', ∀ (y : W) (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k) := by
  subst hn
  choose F hF using h1
  have hF' : ∀ y k, (F y).1 k = ι (y.1 k) := fun y k => hF y k k rfl
  let ψ : W →+ W' :=
    { toFun := F
      map_zero' := Subtype.ext (funext fun k => by rw [hF']; simp)
      map_add' := fun a b => Subtype.ext (funext fun k => by
        simp only [Submodule.coe_add, Pi.add_apply, hF', map_add (f := _)]) }
  have hb : Function.Bijective ψ := by
    constructor
    · intro a b hab
      refine Subtype.ext (funext fun k => ι.injective ?_)
      rw [← hF', ← hF']
      exact congrArg (fun v : W' => v.1 k) hab
    · intro y'
      obtain ⟨y, hy⟩ := h2 y'
      exact ⟨y, Subtype.ext (funext fun k => (hF' y k).trans (hy k k rfl).symm)⟩
  exact ⟨AddEquiv.ofBijective ψ hb, fun y k k' hk => hF y k k' hk⟩


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem cusp_type_eq_of_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {H H' : Host E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {U : ∀ j (σ : c.F →+* ℂ), Formalism.L2.Pj.Unf (Xo j) c σ r} {U' : ∀ j (σ : c'.F →+* ℂ), Formalism.L2.Pj.Unf (Xo' j) c' σ r}
    (hU : HEq U' U) {a a' : (E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {j j' : ℕ} (hj : j' = j) :
    (Formalism.L2.Pj.cusp (Xo' j') c' (U' j') a' n' : Type) = (Formalism.L2.Pj.cusp (Xo j) c (U j) a n : Type) := by
  subst hH ha hn hj
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hU
  rfl

theorem extendByZero_congr_of_heq {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : Formalism.L2.Pj.ext0 (a' t) = Formalism.L2.Pj.ext0 (a t) := by
  subst hj; cases h; rfl


set_option maxHeartbeats 4000000 in
theorem cusp_type_eq_dat {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hN : ExtN z z')
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z.R.nW j = z'.R.nW j' ∧
    (z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n : Type) =
      (z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n : Type) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j) := by
    funext x
    unfold Formalism.L2.Pj.wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : Formalism.L2.Pj.ext0 ((z'.geo.κ j').aP t) = Formalism.L2.Pj.ext0 ((z.geo.κ j).aP t) :=
      extendByZero_congr_of_heq (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : Formalism.L2.Pj.ext0 ((z'.geo.κ j').aM t) = Formalism.L2.Pj.ext0 ((z.geo.κ j).aM t) :=
      extendByZero_congr_of_heq (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M := cusp_type_eq_of_heq hH hN.l hN.c hN.Dw hN.Xo hN.U ha hκ.2.2 hj1
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  refine ⟨hn.symm, ?_⟩
  exact (by with_unfolding_all exact (M :))


set_option maxHeartbeats 4000000 in
theorem forms_match_dat {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (hB : B'.toPre = B.toPre) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hN : ExtN z z') (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ t, (w'.st Z').toD7.what₂.embLL (φ t) = (w.st Z).toD7.what₂.embLL t)
    (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') :
    z.R.nW j = z'.R.nW j' ∧
    (∀ y : (z.R.FW j).WK, ∃ y' : (z'.R.FW j').WK, ∀ (k : Fin (z.R.nW j))
      (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y'.1 k' = φ (y.1 k)) ∧
    (∀ y' : (z'.R.FW j').WK, ∃ y : (z.R.FW j).WK, ∀ (k : Fin (z.R.nW j))
      (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y'.1 k' = φ (y.1 k)) := by
  obtain ⟨hn, M⟩ := cusp_type_eq_dat hB z z' hN j j' hj
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  refine ⟨hn, fun y => ?_, fun y' => ?_⟩
  · obtain ⟨u, rfl⟩ : ∃ u, z.geo.fw.e j u = y := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    exact ⟨z'.geo.fw.e j' (cast M.symm u), fun k k' hk =>
      hinj ((hN.forms j j' hj u (cast M.symm u) (cast_heq _ _) k k' hk).trans (hφ _).symm)⟩
  · obtain ⟨u', rfl⟩ : ∃ u', z'.geo.fw.e j' u' = y' := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    exact ⟨z.geo.fw.e j (cast M u'), fun k k' hk =>
      hinj ((hN.forms j j' hj (cast M u') u' (cast_heq _ _).symm k k' hk).trans (hφ _).symm)⟩

theorem forms_corr_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → (sideAt x g hg a).R.nW j = (sideAt x' g' hg' a').R.nW j' ∧ ∃ φ : ↥((sideAt x g hg a).R.FW j).WK ≃+ ↥((sideAt x' g' hg' a').R.FW j').WK, ∀ (y : ↥((sideAt x g hg a).R.FW j).WK) (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj
  obtain ⟨hn, h1, h2⟩ := forms_match_dat l.enl.1 (datAt x g) (datAt x' g') l.extN ι l.cp.embLL j j' hj
  exact ⟨hn, exists_addEquiv_of_coord hn _ _ ι h1 h2⟩

end GlobalTheory.HeightCounting.SerMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelIffUnipotentAtTypePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevUniLoc

theorem mem_iff_uniRT : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (kv0 : Σ kk : Fin 2, D.nd.PlG kk),
    (∀ kv, kv ≠ kv0 → (M.sp (NX.pG D kv)).v ≠ (M.sp (NX.pG D kv0)).v) →
    (∀ P ∈ M.QP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) → (∀ P ∈ M.DP, (M.sp P).v ≠ (M.sp (NX.pG D kv0)).v) →
    ∀ κ, TrivOutside {(M.sp (NX.pG D kv0)).v} κ →
      (κ ∈ M.J ↔ NG.UniRT (M.sp (NX.pG D kv0)) D.R.r ((M.sp (NX.pG D kv0)).loc D.R.nV κ)) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M kv0 hG hQ hD κ hκ
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, hL, -, -⟩
    obtain ⟨⟨_, hll⟩, huni⟩ := hL kv0
    exact ⟨⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, hll⟩, huni⟩
  · rintro ⟨⟨hGL, hll⟩, huni⟩
    refine ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, fun kv => ?_, fun P hP => ?_, fun P hP => ?_⟩
    · by_cases hk : kv = kv0
      · subst hk
        exact ⟨⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩, huni⟩
      · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hG kv hk)]; exact NX.inLevG_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hQ P hP)]; exact NX.inParah_one _ _
    · rw [GlobalTheory.LevParaLoc.locM_eq_one_of_ne _ _ hκ (hD P hP)]; exact NX.inParah_one _ _

end GlobalTheory.LevUniLoc

end
end

