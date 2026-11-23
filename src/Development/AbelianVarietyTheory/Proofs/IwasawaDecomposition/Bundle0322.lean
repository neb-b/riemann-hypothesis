module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLevelOfStepZeroFormsLevelTrueColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctiona
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 8000000 in
theorem chart_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : Ch i),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
      P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
      (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i h1 h2 β
  obtain ⟨k, hk⟩ := hS.mid i h1 h2
  obtain ⟨L, hLb, hUl, hU⟩ := _root_.GlobalTheory.Mem.Col2.TC.level_of_chart I hOk hP l Z u F hS i (le_of_succ_m h2) (F.ch i h1 h2 β) (F.glevC i h1 h2 β) (hk.lb β)
  obtain ⟨C, hy, hst⟩ := _root_.GlobalTheory.HermTransport.classTie_of_chart (I.rec7 l Z) i (le_of_succ_m h2) (Equiv.refl _) (fun c : {c // chOf i c = β} => (I.rec7 l Z).clsLat u i c.1)
    (F.ch i h1 h2 β) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := hy, st_eq := hst }⟩

set_option maxHeartbeats 8000000 in
theorem top_level_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hm : i ≤ (I.rec7 l Z).R.m) (him : i = (I.rec7 l Z).R.m) (β : Ch i) (hβ : ∀ c, chOf i c = β),
  ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
    SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
      P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
      (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1) := by
  intro B X I hOk hP l Z u Ch chOf F hS i hm him β hβ
  subst him
  obtain ⟨k, hk⟩ := hS.ends _ hm (Or.inr rfl)
  obtain ⟨L, hLb, hUl, hU⟩ := _root_.GlobalTheory.Mem.Col2.TC.level_of_chart I hOk hP l Z u F hS _ hm ((F.cls _ hm (Or.inr rfl)).toChart) F.glevM (hk.lb ())
  obtain ⟨C, hy, hst⟩ := _root_.GlobalTheory.HermTransport.classTie_of_chart (I.rec7 l Z) _ hm (Equiv.subtypeUnivEquiv hβ) (fun c => (I.rec7 l Z).clsLat u _ c)
    ((F.cls _ hm (Or.inr rfl)).toChart) L hLb hU
  exact ⟨⟨L, C⟩, { Lb_eq := hLb, Uloc_eq := hUl, U_eq := hU, y_eq := fun c => hy ⟨c, hβ c⟩, st_eq := fun c => hst ⟨c, hβ c⟩ }⟩

set_option maxHeartbeats 8000000 in
theorem level_classes_of {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
    (hS : I.StdF l Z u F) (hU : Nonempty (Unique (Ch (I.rec7 l Z).R.m))) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : Ch i) :
    ∃ P : (L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f) ×'
      Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) L.Lb L.U (fun c : {c // chOf i c = β} => ((I.rec7 l Z).mem u).C.stab i c.1) (fun c => (I.rec7 l Z).clsLat u i c.1),
      (∀ h2 : i + 1 ≤ (I.rec7 l Z).R.m,
        SameCar (rankN (I.rec7 l Z) i (le_of_succ_m h2)) P.1.Lb (F.ch i h1 h2 β).lev.Lb P.1.Uloc (F.ch i h1 h2 β).lev.Uloc
          P.1.U (F.ch i h1 h2 β).lev.U (fun c => (P.2.y c).1) (fun c => ((F.ch i h1 h2 β).y c).1)
          (fun c s => (P.2.stabI c s).1) (fun c s => ((F.ch i h1 h2 β).stabI c s).1)) ∧
      (∀ (him : i = (I.rec7 l Z).R.m) (hβ : ∀ c, chOf i c = β),
        SameCar (rankN (I.rec7 l Z) i hm) P.1.Lb (F.cls i hm (Or.inr him)).lev.Lb P.1.Uloc (F.cls i hm (Or.inr him)).lev.Uloc
          P.1.U (F.cls i hm (Or.inr him)).lev.U (fun c => (P.2.y ⟨c, hβ c⟩).1) (fun c => ((F.cls i hm (Or.inr him)).y c).1)
          (fun c s => (P.2.stabI ⟨c, hβ c⟩ s).1) (fun c s => ((F.cls i hm (Or.inr him)).stabI c s).1)) := by
  by_cases h2 : i + 1 ≤ (I.rec7 l Z).R.m
  · obtain ⟨P, hP2⟩ := chart_level_classes I hOk hP l Z u F hS i h1 h2 β
    exact ⟨P, fun _ => hP2, fun him _ => absurd h2 (by omega)⟩
  · have him : i = (I.rec7 l Z).R.m := by omega
    have hβ : ∀ c, chOf i c = β := by
      intro c
      subst him
      obtain ⟨U⟩ := hU
      exact Subsingleton.elim _ _
    obtain ⟨P, hP3⟩ := top_level_classes I hOk hP l Z u F hS i hm him β hβ
    exact ⟨P, fun h => absurd h h2, fun _ _ => hP3⟩

set_option maxHeartbeats 8000000 in
theorem hermColsCh_of_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  intro B X I hOk hP l Z Ch chOf F hf hm hS
  have L0 := fun u => _root_.GlobalTheory.Mem.LevZero.colLevel_of_forms I hOk hP l Z u (F u) (hS u)
  have LP := fun u i h1 hm' β => level_classes_of I hOk hP l Z u (F u) (hS u) (hm u) i h1 hm' β
  have LF := fun u v => GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns I hOk hP l Z u (F u) (hS u) v
  refine ⟨fun u => (L0 u).choose, fun u i h1 hm' β => (LP u i h1 hm' β).choose.1,
    fun u i h1 hm' β => (LP u i h1 hm' β).choose.2, fun u => (F u).atT.eV, fun u v => (LF u v).choose, ?_⟩
  exact {
    eV := fun u => rfl
    fv := fun u v a => (LF u v).choose_spec a
    car0 := fun u => (L0 u).choose_spec.1
    carC := fun u i h1 h2 β => (LP u i h1 (le_of_succ_m h2) β).choose_spec.1 h2
    carM := fun u => (LP u _ (one_le_m _) le_rfl _).choose_spec.2 rfl (fun c => @Unique.eq_default _ (hm u).some (chOf u _ c))
    sp := fun u => (L0 u).choose_spec.2.1
    fr0 := fun u => (L0 u).choose_spec.2.2 }

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure AlgWtM where
  d : ℕ
  ρ : Representation ℂ (GQ L n) (Fin d → ℂ)
  alg : IsAlgWeight L n ρ
  irr : ρ.IsIrreducible

structure AutRepM extends AlgWtM L n where
  S : Submodule ℂ (GAf L n → (Fin d → ℂ))
  irrS : NG.IsIrrRep ρ S

variable {L n}

def AlgWtM.toAlgWt (m : AlgWtM L n) : NG.AlgWt L n := ⟨Fin m.d → ℂ, m.ρ, m.alg, m.irr⟩

def AutRepM.toAutRep (m : AutRepM L n) : NG.AutRep L n := ⟨m.toAlgWtM.toAlgWt, m.S, m.irrS⟩

variable (L n)

def AUq : Type := {X : Set (AutRepM L n) // ∃ π : NG.AutRep L n, X = {m | π.Iso m.toAutRep}}

def WtQ : Type := {X : Set (AlgWtM L n) // ∃ a : NG.AlgWt L n, X = {m | a.Iso m.toAlgWt}}

variable {L n}

def clsA (π : NG.AutRep L n) : AUq L n := ⟨{m | π.Iso m.toAutRep}, π, rfl⟩

def clsW (a : NG.AlgWt L n) : WtQ L n := ⟨{m | a.Iso m.toAlgWt}, a, rfl⟩

def AUq.rep (X : AUq L n) : NG.AutRep L n := X.2.choose

def WtQ.rep (X : WtQ L n) : NG.AlgWt L n := X.2.choose

theorem AUq.cls_rep (X : AUq L n) : clsA X.rep = X := Subtype.ext X.2.choose_spec.symm

theorem WtQ.cls_rep (X : WtQ L n) : clsW X.rep = X := Subtype.ext X.2.choose_spec.symm

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LocAt (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) (x : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion L)) : Prop :=
  ∃ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (h : s.w = w),
    IsLocS π.S s σ ∧ HEq (GlobalTheory.LocLanglands.cls σ) x

end


open Classical in
def hwOf (a : NG.AlgWt L n) (τ : L →+* ℂ) : Fin n → ℤ :=
  if h : ∃ lam, a.HWAt τ lam ∧ Antitone lam then h.choose else 0

theorem hwOf_antitone (a : NG.AlgWt L n) (τ : L →+* ℂ) : Antitone (hwOf a τ) := by
  unfold hwOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact fun _ _ _ => le_rfl


open Classical in
def satOf (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset ℂ :=
  if h : ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ),
      NG.OverPl w v ∧ NG.SatAt π Dv α
  then Finset.univ.val.map h.choose_spec.choose_spec.choose else Multiset.replicate (n / 2) 1

theorem satOf_card (π : NG.AutRep L n) (w : HeightOneSpectrum (𝓞 L)) : Multiset.card (satOf π w) = n / 2 := by
  unfold satOf
  split_ifs <;> simp

theorem infOf_card (lam : Fin n → ℤ) : Multiset.card (NG.infOf lam) = n := by
  simp [NG.infOf]

theorem infOf_nodup_alg {lam : Fin n → ℤ} (hl : Antitone lam) : (NG.infOf lam).Nodup ∧
    ∀ x ∈ NG.infOf lam, ∃ k : ℤ, x = (k : ℂ) + ((n : ℂ) - 1) / 2 := by
  refine ⟨?_, ?_⟩
  · unfold NG.infOf
    refine Multiset.Nodup.map_on (fun i _ j _ hij => ?_) Finset.univ.nodup
    have h1 : ((lam i - (i : ℕ) : ℤ) : ℂ) = ((lam j - (j : ℕ) : ℤ) : ℂ) := by
      push_cast; linear_combination hij
    have h2 : lam i - (i : ℕ) = lam j - (j : ℕ) := by exact_mod_cast h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hl (le_of_lt h); have : (i : ℕ) < (j : ℕ) := h; omega
    · have := hl (le_of_lt h); have : (j : ℕ) < (i : ℕ) := h; omega
  · intro x hx
    unfold NG.infOf at hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam i - (i : ℕ), by push_cast; ring⟩

end GlobalTheory.AutQuot

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

open Classical in
def wtOf (D : D7) (π : NG.AutRep D.host.E D.R.nV) : WtQ D.host.E D.R.nV :=
  if h : ∃ b, π.toAlgWt.IsDual b then clsW h.choose else clsW π.toAlgWt

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)


open Classical in
def locOf (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w


end GlobalTheory.AutQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfTypeSpaceNeBotOfIsotypicPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MoveTyped

open Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem isSubrep_bot (ρ : Representation ℂ (GQ L n) W) :
    IsSubrep ρ (⊥ : Submodule ℂ (GAf L n → W)) :=
  ⟨bot_le, fun h f hf => by
    rw [Submodule.mem_bot] at hf ⊢
    subst hf
    exact map_zero _⟩

theorem isSubrep_sup {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊔ Y) :=
  ⟨sup_le hX.le hY.le, fun h f hf => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hX.stable h a ha) (hY.stable h b hb)⟩

theorem isSubrep_inf {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊓ Y) :=
  ⟨inf_le_right.trans hY.le, fun h f hf => ⟨hX.stable h f hf.1, hY.stable h f hf.2⟩⟩

theorem sup_typed_eq_bot {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {X Y : Submodule ℂ (GAf L n → W)} (hX : IsSubrep ρ X) (hXT : X ⊓ TypeSp ρ J χ = ⊥)
    (hY : IsIrrRep ρ Y) (hYT : Y ⊓ TypeSp ρ J χ = ⊥) : (X ⊔ Y) ⊓ TypeSp ρ J χ = ⊥ := by
  by_cases hXY : X ⊓ Y = ⊥
  · rw [eq_bot_iff]
    rintro v ⟨hv, hvT⟩
    have hvT' : v ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) v = ((χ κ : ℂˣ) : ℂ) • v := hvT
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have key : ∀ κ : J, rt L n (κ : GAf L n) a = ((χ κ : ℂˣ) : ℂ) • a ∧
        rt L n (κ : GAf L n) b = ((χ κ : ℂˣ) : ℂ) • b := by
      intro κ
      have e := hvT'.2 κ
      rw [map_add (f := _), smul_add] at e
      have hmem : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a ∈ X ⊓ Y := by
        refine ⟨Submodule.sub_mem _ (hX.stable _ a ha) (Submodule.smul_mem _ _ ha), ?_⟩
        have hab : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a =
            ((χ κ : ℂˣ) : ℂ) • b - rt L n (κ : GAf L n) b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        rw [hab]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) (hY.1.stable _ b hb)
      rw [hXY, Submodule.mem_bot, sub_eq_zero] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at e
      exact add_left_cancel e
    have ha0 : a ∈ X ⊓ TypeSp ρ J χ := ⟨ha, hX.le ha, fun κ => (key κ).1⟩
    have hb0 : b ∈ Y ⊓ TypeSp ρ J χ := ⟨hb, hY.1.le hb, fun κ => (key κ).2⟩
    rw [hXT, Submodule.mem_bot] at ha0
    rw [hYT, Submodule.mem_bot] at hb0
    simp [ha0, hb0]
  · have hle : X ⊓ Y = Y := (hY.2.2 _ (isSubrep_inf hX hY.1) inf_le_right).resolve_left hXY
    have hYX : Y ≤ X := hle ▸ inf_le_left
    rw [sup_eq_left.2 hYX, hXT]

theorem typed_eq_bot_of_iso {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {S S' : Submodule ℂ (GAf L n → W)} (hS : IsSubrep ρ S) (hiso : IsoRep S S')
    (h : S ⊓ TypeSp ρ J χ = ⊥) : S' ⊓ TypeSp ρ J χ = ⊥ := by
  obtain ⟨T, hT⟩ := hiso
  rw [eq_bot_iff]
  rintro u ⟨hu, huT⟩
  have huT' : u ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) u = ((χ κ : ℂˣ) : ℂ) • u := huT
  obtain ⟨f, hfu⟩ : ∃ f : S, T f = ⟨u, hu⟩ := ⟨T.symm _, T.apply_symm_apply _⟩
  have hf : ∀ κ : J, rt L n (κ : GAf L n) (f : GAf L n → W) = ((χ κ : ℂˣ) : ℂ) • (f : GAf L n → W) := by
    intro κ
    let f' : S := ⟨rt L n (κ : GAf L n) f, hS.stable _ _ f.2⟩
    have e := hT κ f f' rfl
    have hTT : T f' = T (((χ κ : ℂˣ) : ℂ) • f) := by
      apply Subtype.ext
      rw [e, map_smul, Submodule.coe_smul, hfu]
      exact huT'.2 κ
    have := congrArg Subtype.val (T.injective hTT)
    simpa [f'] using this
  have hfm : (f : GAf L n → W) ∈ S ⊓ TypeSp ρ J χ := ⟨f.2, hS.le f.2, hf⟩
  rw [h, Submodule.mem_bot] at hfm
  have hf0 : f = 0 := Subtype.ext hfm
  rw [hf0, map_zero] at hfu
  have := congrArg Subtype.val hfu
  simpa using this.symm

theorem typed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S →
    Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  intro L _ _ _ n W _ _ ρ J χ S hS hne h0
  apply hne
  have hfam : ∀ S' ∈ {S' | IsIrrRep ρ S' ∧ IsoRep S S'}, S' ⊓ TypeSp ρ J χ = ⊥ :=
    fun S' hS' => typed_eq_bot_of_iso hS hS'.2 h0
  have fin : ∀ s : Finset (Submodule ℂ (GAf L n → W)), (↑s : Set _) ⊆ {S' | IsIrrRep ρ S' ∧ IsoRep S S'} →
      IsSubrep ρ (⨆ i ∈ s, i) ∧ (⨆ i ∈ s, i) ⊓ TypeSp ρ J χ = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [isSubrep_bot]
    | insert a s ha ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨h1, h2⟩ := ih hs.2
      rw [Finset.iSup_insert, sup_comm]
      exact ⟨isSubrep_sup h1 hs.1.1.1, sup_typed_eq_bot h1 h2 hs.1.1 (hfam a hs.1)⟩
  rw [eq_bot_iff]
  rintro v ⟨hv, hvT⟩
  unfold isoTyp at hv
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hv
  have hb := (fin s hs).2
  rw [eq_bot_iff] at hb
  exact hb ⟨hvs, hvT⟩

end GlobalTheory.MoveTyped
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntMaxFinExt

theorem mem_maximalIdeal_iff_norm_lt_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) [IsLocalRing ↥(Loc.OL K)] (y : ↥(Loc.OL K)), y ∈ IsLocalRing.maximalIdeal ↥(Loc.OL K) ↔ ‖((y : ↥K.1) : PadicAlgCl l)‖ < 1 := by
  intro l _ K _ y
  have hle : ∀ z : ↥(Loc.OL K), ‖((z : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := fun z =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (z : ↥K.1)).1 z.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hlt
    have h1 : ‖((y : ↥K.1) : PadicAlgCl l)‖ = 1 := le_antisymm (hle y) (not_lt.1 hlt)
    have hy0 : (y : ↥K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have hinv : ((y : ↥K.1)⁻¹ : ↥K.1) ∈ Loc.OL K := by
      rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
      rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
    apply hnu
    refine ⟨⟨y, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show (y : ↥K.1) * (y : ↥K.1)⁻¹ = 1
      exact mul_inv_cancel₀ hy0
    · apply Subtype.ext
      show (y : ↥K.1)⁻¹ * (y : ↥K.1) = 1
      exact inv_mul_cancel₀ hy0
  · intro hlt hu
    obtain ⟨u, rfl⟩ := hu
    have hm : ((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l)) * ((((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l) = 1 := by
      have := congrArg (fun z : ↥(Loc.OL K) => (((z : ↥K.1)) : PadicAlgCl l)) u.mul_inv
      exact this
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    have h2 := hle ((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K))
    have h0 : 0 ≤ ‖((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l))‖ := norm_nonneg _
    nlinarith

end GlobalTheory.IntMaxFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVEqAbsNorm
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.ChiLocGal

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]


open Pointwise in
theorem isFrob_conj {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

theorem frob_any [IsAlgClosure E Ω] {B : Type} [CommGroup B] {r r' : G E Ω →* B}
    {v : HeightOneSpectrum (𝓞 E)} {A₀ A : ValuationSubring Ω} (h0 : IsPlaceOver A₀ v) (hA : IsPlaceOver A v)
    (h : ∀ σ : G E Ω, IsFrob (F := E) A₀ (normV v) σ → r σ = r' σ) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) : r σ = r' σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver h0 hA
  have e : ∀ f : G E Ω →* B, f (g⁻¹ * σ * g) = f σ := fun f => by
    rw [map_mul, map_mul, map_inv, mul_comm (f g)⁻¹ (f σ), mul_assoc, inv_mul_cancel, mul_one]
  rw [← e r, ← e r']
  exact h _ (isFrob_conj hσ)

theorem locM_eq (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    Units.map (Formalism.L2.NC.locM P) x = localIdele E P x := by
  rfl

end General

section Values

variable {E : Type} [Field E] [NumberField E]

theorem val_of_at {χ : HChar E} {ψ : Formalism.L2.NC.HC E} (h : ∀ x, ψ.χ x = χ.1 x) {P : HeightOneSpectrum (𝓞 E)} {α : ℂ}
    (hα : ψ.At P α) : ((χ.val P : ℂˣ) : ℂ) = α := by
  rw [← hα.2 _ (unif_spec P), h, locM_eq]
  rfl

theorem normV_eq_absNorm (P : HeightOneSpectrum (𝓞 E)) : normV P = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem val_block {μ η : HChar E} {r : ℕ} {P : HeightOneSpectrum (𝓞 E)} {α z : ℂ}
    (hα : (((μ * η⁻¹).val P : ℂˣ) : ℂ) = α) (hz : z = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ (-(r : ℤ))) :
    (((GlobalTheory.GalChar.block μ η r).val P : ℂˣ) : ℂ) = z⁻¹ := by
  rw [GlobalTheory.GalChar.block_val, hα, hz, mul_inv, inv_inv, zpow_neg, inv_inv, zpow_natCast, ← normV_eq_absNorm]
  congr 1
  have h0 : (0 : ℝ) ≤ (normV P : ℝ) := Nat.cast_nonneg _
  rw [show ((normV P : ℕ) : ℂ) = ((normV P : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow h0,
    Real.sqrt_eq_rpow, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 2
  ring

end Values

end GlobalTheory.ChiLocGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctionaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → ∀ u, ∃ x : Formalism.L2.Herm.ColLevelX (H.lev0 u) (fun x => x ∈ (I.rec7 l Z).host.K) (A u).piU (H.vT u) (fun v c z => ((I.rec7 l Z).fm u).fv 0 v c ((A u).pr 0 v c z)), x.piG = X.piG := by
  first | exact @GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem | exact GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem | (intros; apply GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem <;> assumption)
end

