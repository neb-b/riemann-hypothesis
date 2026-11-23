module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0003
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
section
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

structure Pt (C : FC) : Type 1 where
  D : D7
  L : SizeData₂ D
  gatT : GatTies D
  ta : TiesAt C L gatT
  xa : ExtraAt C L gatT ta.Gx ta.Gy

abbrev PtProp : Type 1 :=
  ∀ (D : D7) (L : SizeData₂ D) (gatT : GatTies D) (Gx : G.Inst D L) (Gy : G.LatInst D) (K : G.Consts) (X : DivX D) (cX : ExtraC),
    Extra D L gatT Gx Gy K X cX → Prop

def Pt.Has {C : FC} (p : Pt C) (Q : PtProp) : Prop :=
  Q p.D p.L p.gatT p.ta.Gx p.ta.Gy C.GK p.xa.X C.cX p.xa.ex

def classOf (Q : PtProp) : FamClass := fun Fm =>
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Q (Fm.D x i) (Fm.L x i) (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK (Fm.X x i) Fm.cX (Fm.ex x hx i)

def Pt.Same {C : FC} (p p' : Pt C) : Prop :=
  p.D.R = p'.D.R ∧ p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val ∧ p.D.host.T2 = p'.D.host.T2 ∧
  p.D.host.q = p'.D.host.q ∧ p.D.host.d = p'.D.host.d ∧ p.D.host.g = p'.D.host.g ∧
  p.D.host.pde = p'.D.host.pde ∧ p.D.host.pde' = p'.D.host.pde' ∧
  p.L.etaSz = p'.L.etaSz ∧ p.L.Sc = p'.L.Sc ∧ (∀ l, (G.hP p.D l).val = (G.hP p'.D l).val) ∧
  (∀ (h t : G.HH p.D) (h' t' : G.HH p'.D), h.val = h'.val → t.val = t'.val → (p.ta.Gx.bs h t).val = (p'.ta.Gx.bs h' t').val) ∧
  (∀ j (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → p.ta.Gx.off j (false, t) = p'.ta.Gx.off j (false, t')) ∧
  p.ta.Gx.kapI = p'.ta.Gx.kapI ∧ p.ta.Gx.ep = p'.ta.Gx.ep ∧
  (∀ (t : p.D.host.TT) (t' : p'.D.host.TT), (t : p.D.R.A).val = (t' : p'.D.R.A).val →
    p.L.aT t = p'.L.aT t' ∧ p.L.bT t = p'.L.bT t') ∧
  p.D.host.QS = p'.D.host.QS ∧ artNum p.D.host.toHostRaw = artNum p'.D.host.toHostRaw ∧ p.D.host.rdE = p'.D.host.rdE

structure Kit (C : FC) (cD ch : ℝ) (s : Scale) : Type 1 where
  Ix : Type
  ne : Nonempty Ix
  pt : Ix → Pt C
  sc_eq : ∀ i, (pt i).L.sc = s
  val : ∀ i, Val C cD ch (pt i).L
  arith : ∀ i, HostArith (pt i).D.host
  same : ∀ i i', (pt i).Same (pt i')
  W : Type
  eW : ∀ i, (pt i).D.what₂.Word ≃ W
  eW_code : ∀ i i' u u', eW i u = eW i' u' → wordBits (pt i).D u = wordBits (pt i').D u'
  cover : ∀ i0 (u0 : ℕ), u0 < (pt i0).D.R.n → ∃ i, (pt i).D.host.u0.val = u0

def PtProp.and (Q Q' : PtProp) : PtProp := fun D L gatT Gx Gy K X cX ex =>
  Q D L gatT Gx Gy K X cX ex ∧ Q' D L gatT Gx Gy K X cX ex

def BoxesW (D : D7) (s : Scale) : Prop := ∃ Y : ℝ, PairWin s Y ∧ Boxes_at D Y s.eps ∧ GlobalTheoryTheory.BoxE D Y s.eps

def QDRowsW (D : D7) (s : Scale) : Prop := ∃ Y : ℝ, PairWin s Y ∧ QDRows_at D Y s.eps

def BoxesWF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧
    Boxes_at (Fm.D x i) Y eps ∧ GlobalTheoryTheory.BoxE (Fm.D x i) Y eps

def QDRowsWF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧ QDRows_at (Fm.D x i) Y eps

def ReqPt : PtProp := fun D L _ Gx _ K _ _ _ =>
  AuxBlock8.admW D L Gx K ∧ BoxesW D L.sc ∧ QDRowsW D L.sc

def TwPt : PtProp := fun D _ _ _ _ _ _ _ ex => LocalQuadraticParts.TWAt D ex.nch ex.xd

theorem Pt.Same.weights {C : FC} {p p' : Pt C} (h : p.Same p') (t : p.D.host.TT) (t' : p'.D.host.TT)
    (e : (t : p.D.R.A).val = (t' : p'.D.R.A).val) : p.L.aT t = p'.L.aT t' ∧ p.L.bT t = p'.L.bT t' :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t t' e

theorem Pt.Same.QS_eq {C : FC} {p p' : Pt C} (h : p.Same p') : p.D.host.QS = p'.D.host.QS :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.Same.art_eq {C : FC} {p p' : Pt C} (h : p.Same p') :
    artNum p.D.host.toHostRaw = artNum p'.D.host.toHostRaw :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Pt.Same.rd_eq {C : FC} {p p' : Pt C} (h : p.Same p') : p.D.host.rdE = p'.D.host.rdE :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Kit.cover_weights {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) (i0 : k.Ix) (u0 : ℕ)
    (hu : u0 < (k.pt i0).D.R.n) : ∃ i, (k.pt i).D.host.u0.val = u0 ∧
      ∀ (t : (k.pt i).D.host.TT) (t0 : (k.pt i0).D.host.TT),
        (t : (k.pt i).D.R.A).val = (t0 : (k.pt i0).D.R.A).val →
          (k.pt i).L.aT t = (k.pt i0).L.aT t0 ∧ (k.pt i).L.bT t = (k.pt i0).L.bT t0 := by
  obtain ⟨i, hi⟩ := k.cover i0 u0 hu
  exact ⟨i, hi, (k.same i i0).weights⟩

theorem Val.mem_box {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) :
    G.aL L ∈ G.box D (G.winA D L.sc) ∧ G.bL L ∈ G.box D (G.winB D C.GK L.sc) := by
  classical
  constructor
  · refine Fintype.mem_piFinset.2 fun t => ?_
    by_cases ht : t ∈ D.host.TT
    · simp only [G.aL, ht, dif_pos, if_true, G.winA, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
      exact L.aT_win ⟨t, ht⟩
    · simp [G.aL, ht]
  · refine Fintype.mem_piFinset.2 fun t => ?_
    by_cases ht : t ∈ D.host.TT
    · simp only [G.bL, ht, dif_pos, if_true, G.winB, Finset.mem_Icc, Int.ceil_le, Int.le_floor, G.Nstar]
      exact ⟨L.bT_ge ⟨t, ht⟩, h.La_eq ▸ h.bT_le ⟨t, ht⟩⟩
    · simp [G.bL, ht]

theorem classOf_reqPt {eps : ℝ} (Fm : FamP eps) (h : classOf ReqPt Fm) :
    (∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, AuxBlock8.admW (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK) ∧ BoxesWF Fm ∧ QDRowsWF Fm := by
  refine ⟨fun x hx i => (h x hx i).1, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, ⟨Fm.x1 + 1, fun x hx i => ?_⟩⟩
  · have hx' : Fm.x1 < x := by linarith
    have := (h x hx' i).2.1
    unfold BoxesW PairWin at this
    rwa [Fm.L_x x i hx', Fm.L_eps x i, Fm.L_J x i] at this
  · have hx' : Fm.x1 < x := by linarith
    have := (h x hx' i).2.2
    unfold QDRowsW PairWin at this
    rwa [Fm.L_x x i hx', Fm.L_eps x i, Fm.L_J x i] at this

theorem mod_lcm_of_mod_mul {p N : ℕ} (hN : 0 < N) (h : p % (15 * N) = 1) : p % Nat.lcm 15 N = 1 := by
  have h1 : 1 < Nat.lcm 15 N := lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.lcm_pos (by norm_num) hN) (Nat.dvd_lcm_left 15 N))
  rw [← Nat.mod_mod_of_dvd p (Nat.lcm_dvd_mul 15 N), h, Nat.mod_eq_of_lt h1]

theorem mod_of_mod_lcm {p N : ℕ} (hN : 1 < N) (h : p % Nat.lcm 15 N = 1) : p % 15 = 1 ∧ p % N = 1 := by
  constructor
  · rw [← Nat.mod_mod_of_dvd p (Nat.dvd_lcm_left 15 N), h]
  · rw [← Nat.mod_mod_of_dvd p (Nat.dvd_lcm_right 15 N), h, Nat.mod_eq_of_lt hN]

theorem classOf_twPt {eps : ℝ} (Fm : FamP eps) (h : classOf TwPt Fm) : TwGood Fm := ⟨0, fun x _ hx i => h x hx i⟩

end GlobalTheory.EX

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsIntegralPendingObjectSymmetricFormsLevel
section
noncomputable section

namespace GlobalTheory.LvT.PendExample

open Formalism.BasicNotions Classical NumberField GlobalTheory.MemberTorsor
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

section Span
variable (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

variable {D lam}


variable {g : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ}

end Span

section Lat
variable (K : Type) [Field K] [NumberField K] [StarRing K] (κ : Type) [Fintype κ] [DecidableEq κ]

variable {K κ}

end Lat

section Chain
variable (D : D7) (u : D.what₂.Word) (T : ℕ) [Fact T.Prime]

end Chain

theorem nfAll_pos {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ≠ 0) : 0 < (nfAll l p p).re := by
  unfold nfAll
  simp only [fockF_self_eq (extremal ℂ n _)]
  rw [← Complex.ofReal_prod, Complex.div_ofReal_re]
  refine div_pos (fockF_self_pos hp) (Finset.prod_pos fun τ _ => ?_)
  have := fockF_self_pos (f := extremal ℂ n (l τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (l τ).natW)
  rwa [fockF_self_eq, Complex.ofReal_re] at this

end GlobalTheory.LvT.PendExample
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.InfiniteGroup
section
noncomputable section
namespace GlobalTheory.LvT.LevModel
open Formalism.BasicNotions Classical

section Pairs

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

lemma mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

def stdPair (Lc : LocF q F) (a : Fin n) : LocF.PP Lc n :=
  ⟨⟨Lc.std n, fun x => if h : x ∈ Lc.std n then Lc.res ⟨x a, (mem_std x).1 h a⟩ else 0⟩,
   { lat := ⟨1, fun x => by simp⟩
     add := fun x hx y hy => by
       dsimp only at hx hy ⊢
       rw [dif_pos hx, dif_pos hy, dif_pos ((Lc.std n).add_mem hx hy), ← map_add (f := _)]; rfl
     smul := fun c x hx => by
       dsimp only at hx ⊢
       rw [dif_pos hx, dif_pos ((Lc.std n).smul_mem c hx), ← map_mul]; rfl
     off := fun x hx => dif_neg hx
     ne := by
       have h : (fun _ => 1 : Fin n → Lc.K) ∈ Lc.std n := (mem_std _).2 fun _ => Lc.O.one_mem
       refine ⟨fun _ => 1, ?_⟩
       dsimp only
       rw [dif_pos h]
       exact (map_one Lc.res).trans_ne one_ne_zero }⟩

def mvO (g : GL (Fin n) Lc.K) : (Fin n → Lc.K) →ₗ[Lc.O] (Fin n → Lc.K) :=
  (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) Lc.K)).restrictScalars Lc.O

lemma inv_mv (g : GL (Fin n) Lc.K) (x : Fin n → Lc.K) :
    mvO g⁻¹ (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x) = x := by
  show Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K)
    (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x) = x
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

def actPP (g : GL (Fin n) Lc.K) (p : LocF.PP Lc n) : LocF.PP Lc n :=
  ⟨⟨p.1.L.comap (mvO g⁻¹), fun x => p.1.f (mvO g⁻¹ x)⟩,
   { lat := by
       obtain ⟨h, hh⟩ := p.2.lat
       refine ⟨g * h, fun x => ?_⟩
       rw [← hh x, Units.val_mul, ← Matrix.mulVec_mulVec]
       show mvO g⁻¹ _ ∈ p.1.L ↔ _
       rw [inv_mv]
     add := fun x hx y hy => by
       show p.1.f (mvO g⁻¹ (x + y)) = _
       rw [map_add (f := _)]; exact p.2.add _ hx _ hy
     smul := fun c x hx => by
       show p.1.f (mvO g⁻¹ (c • x)) = _
       rw [map_smul]; exact p.2.smul c _ hx
     off := fun x hx => p.2.off _ hx
     ne := by
       obtain ⟨x, hx⟩ := p.2.ne
       refine ⟨Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x, ?_⟩
       show p.1.f (mvO g⁻¹ _) ≠ 0
       rwa [inv_mv] }⟩

theorem isAct_actPP (g : GL (Fin n) Lc.K) (p : LocF.PP Lc n) : LocF.PP.IsAct g p (actPP g p) := by
  intro x
  refine ⟨?_, ?_⟩
  · show mvO g⁻¹ _ ∈ p.1.L ↔ _
    rw [inv_mv]
  · show p.1.f (mvO g⁻¹ _) = _
    rw [inv_mv]

private lemma mulVec_mvO_inv (g : GL (Fin n) Lc.K) (y : Fin n → Lc.K) :
    Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) (mvO g⁻¹ y) = y := by
  show Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K)
    (Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) y) = y
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem isAct_unique {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n} (h₁ : LocF.PP.IsAct g p p₁)
    (h₂ : LocF.PP.IsAct g p p₂) : p₁ = p₂ := by
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext y
    rw [← mulVec_mvO_inv g y, (h₁ _).1, (h₂ _).1]
  · funext y
    rw [← mulVec_mvO_inv g y, (h₁ _).2, (h₂ _).2]

end Pairs

variable {D : D7} {u : D.what₂.Word}

end GlobalTheory.LvT.LevModel
end
end

