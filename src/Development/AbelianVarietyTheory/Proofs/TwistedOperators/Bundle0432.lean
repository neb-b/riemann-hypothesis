module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteDatumIsSchwartzBruhatHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta

theorem isSBHalf_levDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) (levDatum S T βS βT LT Q m e) := by
  intro D S T ΛS ΛT βS βT LT Q m Z e hS hT hfS hfT he
  classical

  have hlin : ∀ (k : ℕ) (u : WO S T), frMapAdj S T βS βT (k • u) = k • frMapAdj S T βS βT u := by
    intro k u
    induction k with
    | zero =>
      have h0 := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT 0 0
      simpa using h0
    | succ n ih =>
      rw [succ_nsmul, GlobalTheory.PlaceVec.frMapAdj_add, ih, succ_nsmul]
  have hadd : ∀ (x u : WO S T) (k : ℕ) i j,
      frMapAdj S T βS βT (x + k • u) i j = frMapAdj S T βS βT x i j + k * frMapAdj S T βS βT u i j := by
    intro x u k i j
    rw [GlobalTheory.PlaceVec.frMapAdj_add, hlin, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]

  have hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True), ∀ i j, (M : EAf D) * frMapAdj S T βS βT u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    obtain ⟨M, hM, hMl⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
    obtain ⟨k, hk, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
    refine ⟨k * M, Nat.mul_pos hk hM, fun u hu i j => ?_⟩
    have hint : IsIntM ((M • u).map (toEAf D)) := by
      intro a b
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, nsmul_eq_mul]
      exact hMl u hu a b
    have h := hup (M • u) hint i j
    rw [hlin, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc] at h
    simpa [Nat.cast_mul] using h

  have hC : ∃ K : ℕ, 0 < K ∧ ∀ t, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) →
      K • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    obtain ⟨k, hk, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
    obtain ⟨K, hK, hKl⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
    refine ⟨K * k, Nat.mul_pos hK hk, fun t ht hti => ?_⟩
    have hinf : t.map (infPart D) = 0 :=
      GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)) ht
    have hinf' : (k • t).map (infPart D) = 0 := by
      ext a b
      have h1 := congrFun (congrFun hinf a) b
      rw [Matrix.map_apply, Matrix.zero_apply] at h1
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, h1, smul_zero, Matrix.zero_apply]
    have hint' : ∀ a b, toEAf D ((k • t) a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro a b
      have h2 := hdown t hti a b
      rwa [Matrix.smul_apply, Matrix.map_apply, ← map_nsmul] at h2
    rw [← smul_smul]
    exact hKl (k • t) hinf' hint'

  have hω : ∀ y y' : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)),
      (∀ PP ∈ LT.Pg ∪ Q, y PP = y' PP) →
        omegaG LT m y * omegaQ Q T.rank m (-1) y = omegaG LT m y' * omegaQ Q T.rank m (-1) y' := by
    intro y y' h
    rw [GlobalTheory.PlaceDatum.omegaG_congr LT m y y' (fun PP hP => h PP (Finset.mem_union_left _ hP)),
      GlobalTheory.PlaceDatum.omegaQ_congr Q T.rank m (-1) y y' (fun PP hP => h PP (Finset.mem_union_right _ hP))]
  have key := GlobalTheory.PlaceDatum.isSBHalf_of_red (cA D e)
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (frMapAdj S T βS βT) hadd hB hC (LT.Pg ∪ Q) (fun y => omegaG LT m y * omegaQ Q T.rank m (-1) y) hω
  unfold levDatum
  exact key

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

def edgeOf : Arrow T → GlobalTheory.SplitFlip.Edge
  | .right i j => .ex i j
  | .down _ i j => .theta i j
  | _ => .ex 0 0

def IsGridArrow (m : ℕ) (t : T) (a : Arrow T) : Prop :=
  (∃ i j, i < m ∧ j ≤ m ∧ a = .right i j) ∨ ∃ i j, i ≤ m ∧ j < m ∧ a = .down t i j

variable {X Y : Node}

def OnGrid (m : ℕ) (t : T) (p : Path T X Y) : Prop := ∀ a ∈ p.arrows, IsGridArrow m t a

def edges (p : Path T X Y) : List GlobalTheory.SplitFlip.Edge := p.arrows.map edgeOf

section Grid

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def vacOf {W : G.Weil} (ρ : RealMatch W) : ∀ a : Arrow T, Sch G a
  | .right i j => ρ.vX i j
  | .down _ i j => ρ.vT i j
  | _ => 0

def locArg (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair) →
    Matrix (Fin ((locGrid G t w).rank (edgeOf a).tgt)) (Fin ((locGrid G t w).rank (edgeOf a).src)) (Kw w)
  | .right i j, x => if h : i < D.R.m ∧ j ≤ D.R.m then
      B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨h.1.le, h.2⟩ ⟨h.1, h.2⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .down _ i j, x => if h : i ≤ D.R.m ∧ j < D.R.m then
      B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨h.1, h.2⟩ ⟨h.1, h.2.le⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .coreUp _, _ => 0
  | .coreDown _, _ => 0
  | .col _ _, _ => 0

abbrev ArgT (G : GridData L sc) (p : Path T X Y) : Type := p.Fam fun a => WO (G.pS a.pair) (G.pT a.pair)

def castArg {t : T} {w : Pl D.host.E} {e₁ e₂ : GlobalTheory.SplitFlip.Edge} (h : e₁ = e₂)
    (y : Matrix (Fin ((locGrid G t w).rank e₁.tgt)) (Fin ((locGrid G t w).rank e₁.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e₂.tgt)) (Fin ((locGrid G t w).rank e₂.src)) (Kw w) := h ▸ y

def argAt (B : Frames G) (t : T) (w : Pl D.host.E) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) (e : GlobalTheory.SplitFlip.Edge)
    (d : Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w) :=
  if h : edgeOf a = e then castArg h (locArg B t w a x) else d

noncomputable def pathArgs (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → (locGrid G t w).Args
  | _, .nil, _ => 0
  | _, .snoc a p, x => fun e => argAt B t w a x.2 e (pathArgs B t w p x.1 e)

noncomputable def famProd : ∀ {Y : Node} (p : Path T X Y), PureT G p → ArgT G p → ℂ
  | _, .nil, _, _ => 1
  | _, .snoc _ p, d, x => famProd p d.1 x.1 * d.2 x.2

noncomputable def HalfAll (e : AE D) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → Prop
  | _, .nil, _ => True
  | _, .snoc _ p, x => HalfAll e p x.1 ∧ IsHalf e x.2

noncomputable def VecAll {W : G.Weil} (ρ : RealMatch W) (e : AE D) : ∀ {Y : Node} (p : Path T X Y), PureT G p → PureT G p → Prop
  | _, .nil, _, _ => True
  | _, .snoc a p, φ, f => VecAll ρ e p φ.1 f.1 ∧ IsLocVec W a.pair e (vacOf ρ a) φ.2 f.2

def RepFin {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (p : Path T X Y) (τ : TotT G p)
    (Tl : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧ ∃ φ : PureT G p → PureT G p, (∀ d ∈ τ.support, VecAll ρ e p (φ d) d) ∧
    ∀ x : ArgT G p, HalfAll e p x → (τ.sum fun d c => c * famProd p (φ d) x) = ∏ w ∈ locPl G t, Tl w (pathArgs B t w p x)


variable (G) in
abbrev PolE : Type := ∀ e : GlobalTheory.SplitFlip.Edge, PolF D (G.V (.grid e.src.1 e.src.2)).rank (G.V (.grid e.tgt.1 e.tgt.2)).rank

def polOf (P : PolE G) : ∀ a : Arrow T, PolF D (G.pT a.pair).rank (G.pS a.pair).rank
  | .right i j => P (.ex i j)
  | .down _ i j => P (.theta i j)
  | .coreUp _ => 0
  | .coreDown _ => 0
  | .col _ _ => 0

noncomputable def restrictPol (P : PolE G) : ∀ {Y : Node} (p : Path T X Y), PolT G p
  | _, .nil => ()
  | _, .snoc a p => (restrictPol P p, polOf P a)

def tensE (W : G.Weil) (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) : TotT G p :=
  tensT W (Q.mapDomain fun P => restrictPol P p) τ

def toOpp (P : PolE G) : GlobalTheory.RowClaim.PolRow G × GlobalTheory.RowClaim.PolDown G :=
  (fun i => P (.ex i D.R.m), fun j => P (.theta D.R.m j))

end Grid

end GlobalTheory.FlipRun

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.ChiGrid GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem range_snd_rel (ρ : RealMatch W) (i j : ℕ) :
    LinearMap.range ((LinearMap.snd ℂ _ _).comp (ρ.rel i j).subtype) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun b => ?_
  obtain ⟨a, h⟩ := ρ.onto_small i j b
  exact ⟨⟨(a, b), h⟩, rfl⟩

def matchLin (ρ : RealMatch W) (i j : ℕ) : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ]
    PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) :=
  (LinearMap.fst ℂ _ _).comp ((ρ.rel i j).subtype.comp
    (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose)

theorem matchLin_mem (ρ : RealMatch W) (i j : ℕ) (b : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) :
    (matchLin ρ i j b, b) ∈ ρ.rel i j := by
  have h := LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose_spec b
  set g := (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose
  have e : ((g b : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j))) = (matchLin ρ i j b, b) :=
    Prod.ext rfl h
  exact e ▸ (g b).2

def flipPol (ρ : RealMatch W) (i j : ℕ) (P : PolE G) : PolE G →₀ ℂ :=
  (toTens_surjective (matchLin ρ i j (P (.theta i j) ⊗ₜ P (.ex i j)))).choose.sum fun q c =>
    Finsupp.single (Function.update (Function.update P (.ex i (j + 1)) q.1.2) (.theta (i + 1) j) q.2) c

def flipPolE (ρ : RealMatch W) (i j : ℕ) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ := Q.sum fun P c => c • flipPol ρ i j P

def flipsPolE (ρ : RealMatch W) (l : List (ℕ × ℕ)) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ :=
  l.foldl (fun Q x => flipPolE ρ x.1 x.2 Q) Q

def IsCuspListed (θ : InfFam D) (X : Node) (F : Fn G X) : Prop :=
  IsAutFunSm θ (G.V X) F ∧ IsCuspFun (G.V X) F ∧ G.IsListed θ X F

def CuspStep (W : G.Weil) (M : Vol G) (ρ : RealMatch W) (t : T) : Prop :=
  ∀ a : Arrow T, IsGridArrow D.R.m t a → ∀ e, IsIdemSum e (locPl G t) → ∀ φ f, IsLocVec W a.pair e (vacOf ρ a) φ f →
    ∀ (Q : PolF D (G.pT a.pair).rank (G.pS a.pair).rank) (F : Fn G a.src), IsCuspListed W.θ a.src F →
      LiftConv W M a (W.fock a.pair f Q) F ∧ IsCuspListed W.θ a.tgt (liftA W M a (W.fock a.pair f Q) F)

end GlobalTheory.FlipRun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def PeriodsOnLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
      ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P

def RealLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ell ≠ 0 ∧
    (∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, ∃ K : ℂ, ∀ σ : PolCol ch.G × PolRow ch.G →₀ ℂ,
        defTot t ch.S.toGridChoice M σ τ (colFn ch a) (formTop ch t y) = (σ.sum fun P c => c * ell P) * K) ∧
    ∀ z : ℂ, ∃ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, (z = 0 → σ = 0) ∧ (σ.sum fun P c => c * ell P) = z

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem sum_sum_line {P D' : Type} (σ : P →₀ ℂ) (τ : D' →₀ ℂ) (f : P → D' → ℂ) (ell : P → ℂ)
    (κ : D' → ℂ) (h : ∀ d ∈ τ.support, ∀ p, f p d = κ d * ell p) :
    (σ.sum fun p c => τ.sum fun d c' => c * c' * f p d) =
      (σ.sum fun p c => c * ell p) * τ.sum fun d c' => c' * κ d := by
  rw [Finsupp.sum_mul]
  refine Finsupp.sum_congr fun p _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d hd => ?_
  rw [h d hd p]
  ring

theorem realLine_of_periodsOnLine (ch : Choice R) (h : PeriodsOnLine ch) : RealLine ch := by
  obtain ⟨ell₀, h₀⟩ := h
  classical
  let ell : PolCol ch.G × PolRow ch.G → ℂ := if ell₀ = 0 then fun _ => 1 else ell₀
  have hne : ell ≠ 0 := by
    by_cases e : ell₀ = 0
    · simp only [ell, e, if_true]
      intro h1
      have := congrFun h1 (Classical.arbitrary _)
      simp at this
    · simpa [ell, e] using e
  have hline : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P := by
    intro t a hS β hβ M hM τ hτ d hd y
    obtain ⟨κ, hκ⟩ := h₀ t a hS β hβ M hM τ hτ d hd y
    by_cases e : ell₀ = 0
    · refine ⟨0, fun P => ?_⟩
      rw [hκ P, e]
      simp
    · exact ⟨κ, fun P => by simp only [ell, e, if_false]; exact hκ P⟩
  refine ⟨ell, hne, fun t a hS β hβ M hM τ hτ y => ?_, fun z => ?_⟩
  · choose κ hκ using hline t a hS β hβ M hM τ hτ
    let κ' : PureDat ch.G t → ℂ := fun d => if hd : d ∈ τ.support then κ d hd y else 0
    refine ⟨τ.sum fun d c' => c' * κ' d, fun σ => ?_⟩
    refine sum_sum_line σ τ _ ell κ' fun d hd P => ?_
    simp only [κ', dif_pos hd]
    exact hκ d hd y P
  · obtain ⟨P₀, hP₀⟩ := Function.ne_iff.1 hne
    refine ⟨Finsupp.single P₀ (z / ell P₀), fun hz => by simp [hz], ?_⟩
    rw [Finsupp.sum_single_index (zero_mul _)]
    exact div_mul_cancel₀ z hP₀

theorem big_mono {Q Q' : ChP} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), Q ch → Q' ch) (hQ : Big Q) : Big Q' := by
  obtain ⟨CF0, hC⟩ := hQ
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => h ch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.FormulaTwo

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem mem_xiVals {L : LevCh D T} {t : T} {n : ℕ} (hn : (L.xiH t).OrderDvd n) (hL : LocIn D.what₂.embLL (L.xiH t))
    {z : ℂˣ} (hz : z ∈ xiVals L t) : z ^ n = 1 ∧ (z : ℂ) ∈ Set.range D.what₂.embLL := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, x, rfl⟩ := hz
    refine ⟨?_, hL w x⟩
    have : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from hn]; rfl
    exact this
  | one => exact ⟨one_pow _, 1, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha.2
    obtain ⟨y, hy⟩ := hb.2
    exact ⟨by rw [mul_pow, ha.1, hb.1, one_mul], x * y, by simp [hx, hy]⟩
  | inv a _ ha =>
    obtain ⟨x, hx⟩ := ha.2
    exact ⟨by rw [inv_pow, ha.1, inv_one], x⁻¹, by simp [hx]⟩

theorem Bplus_smul_form {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (c : ℂ) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M φ (c • F) = c * Bplus W M φ F := by
  simpa using Bplus_smul W M 1 c φ F

theorem scalar_calc {e z z' c p b s u κ v w : ℂ} (he : e = z * z') (hz : z ≠ 0) (hz' : z' ≠ 0) (hc : c ≠ 0)
    (h1 : p = (z * c)⁻¹ * b) (h2 : b = z'⁻¹ * s * u) (h3 : u = κ * v) (h4 : w = s * v) : e * c * p = κ * w := by
  subst he h1 h2 h3 h4
  field_simp

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


set_option maxHeartbeats 4000000 in
theorem formulaAt_steps (hL : R.toLevCh.Is A.μ0) (hC : R.IsChain) (ch : Choice R) (hP : ProjAt ch) (hF : FlipAt ch)
    (hU : UnfoldAt ch) (hJ : JetsAt ch) (hc : ∀ i j t, ch.c i j t ≠ 0) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hK : ch.FieldOK) : ∃ κ ze, FormulaAt ch κ ze := by
  obtain ⟨τi, z, hF⟩ := hF
  obtain ⟨σ, z', hU⟩ := hU τi
  obtain ⟨hM, hJ⟩ := hJ
  obtain ⟨κ, hJ⟩ := hJ σ
  have key : ∀ t, ∃ e : D.what₂.LL, D.what₂.embLL e = (z t : ℂ) * z' t ∧ ∃ n : ℕ, 0 < n ∧ e ^ n = 1 := fun t => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    obtain ⟨h1, e, he⟩ := mem_xiVals ho (hK.chars.xi t) (mul_mem (hF t).1 (hU t).1)
    refine ⟨e, he, n, hn, D.what₂.embLL.injective ?_⟩
    rw [map_pow, he, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  choose ze hze hzn using key
  refine ⟨κ, ze, hzn, fun t x hx a => ?_⟩
  obtain ⟨τ, hτ, hfl⟩ := (hF t).2 (ch.Phi a)
  obtain ⟨M, hMt⟩ := exists_vol ch.G hL t
  choose Mβ hMβ using hM t (ch.Phi a)
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ch.S.IsExpansion t (ch.Phi a) β
      (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) := fun β hβ => Classical.epsilon_spec ((hS t a).ex β hβ)
  have e1 : psiK ch a (R.Th t (R.jX t x)) =
      Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.cv.lift t (R.jX t x))) := by
    exact congrArg (fun u => Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) u))
      ((form_Th ch hC t _).trans (hP t x hx))
  have e2 := (hU t).2 a τ hτ M hMt Mβ (fun β => Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β))
    (fun β hβ => ⟨hMβ β, hex β hβ⟩) (R.jX t x)
  have e3 : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
      defTot t ch.S.toGridChoice (Mβ β) σ (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (colFn ch a)
        (formTop ch t (R.jX t x))) = κ * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := by
    rw [(hS t a).vCore_eq _ hex, finsum_mem_eq_finite_toFinset_sum _ (hS t a).fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := (Set.Finite.mem_toFinset _).1 hβ
    exact (congrArg (HMul.hMul _) (hJ t a β hβ' (Mβ β) _ (hMβ β) (hex β hβ') (R.jX t x))).trans (mul_left_comm _ _ _)
  have e4 : vK ch t x a = ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := rfl
  have hct : cTot ch t ≠ 0 := (cTot_ne_zero_iff ch t).2 fun i j => hc i j t
  have e5 := congrArg (Bplus ch.W ch.M (colFn ch a)) (hfl M hMt (R.jX t x)).2
  exact scalar_calc (hze t) (z t).ne_zero (z' t).ne_zero hct (e1.trans (e5.trans (Bplus_smul_form _ _ _ _ _))) e2 e3 e4

theorem formula2K (hP : StepProj) (hF : StepFlip) (hU : StepUnfold) (hJ : StepJets) (hc : ConstK) (hS : SumOKK) :
    Formula2K := by
  obtain ⟨C0, H⟩ := ((((hP.and hF).and hU).and hJ).and hc).and hS
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j hK => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact formulaAt_steps s.core.lev s.core.chain ch a b c d (fun i j t => (f i j t).2) g hK

end GlobalTheory.RowClaim.FormulaTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowSizes

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D := by
  intro D large₂ h
  obtain ⟨⟨Pm, _, _⟩, _, hmf, hm44, _⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 := D.R.f_le_k
    have h2 : D.R.f = 2 * D.R.ord := rfl
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    have h4 : 44 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm44 4
    omega
  · intro τ j hj
    have hg := (Pm.nodes_gap τ j hj).1
    have hf := Pm.heightBound_ge_rank_cubic
    have hN : ((GlobalTheory.Grid.bigN D : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      unfold GlobalTheory.Grid.bigN GlobalTheory.Grid.sLen; push_cast; ring
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have key : ((2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 : ℚ) : ℝ) <
        (((D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
      push_cast at hg ⊢
      rw [hN]
      linarith
    exact_mod_cast key

end GlobalTheory.RowSizes
end

