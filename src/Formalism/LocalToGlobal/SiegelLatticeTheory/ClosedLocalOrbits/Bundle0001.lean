module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.LemmaN
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Corank
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Corank

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def ScalRel (Λ : Submodule (𝓞 E) S.V) (g k : ℕ) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T') : Prop :=
  ∃ β : S.V ≃ₗ[E] S.V, IsPair Λ F F' F'' β g ∧ s0 Λ F F' F'' β k = 1 ∧ IsScalar Λ F F' F'' β

end Gen

def CorankPosG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsFullLattice E Λ →
    ∀ (T T' : E) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V),
      IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → 1 ≤ s0 Λ F F' F'' β k

def ScalarEquivG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k g : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsFullLattice E Λ →
    ∀ (T T' : E), T ≠ 0 → T' ≠ 0 → ∀ F : LFlag S r T, IsLift Λ F →
      Equivalence (fun x y : {F' : LFlag S r T' // IsLift Λ F' ∧ Gval F F' ≠ 0} => ScalRel Λ g k F x.1 y.1)

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem finrank_VS : finrank D.host.E (VS D).V = D.R.k + 2 * D.R.rS + 1 := by
  have h1 := (D.sp.Y 0).rank_eq
  have h2 := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have h3 := D.R.two_le_m
  simp only [VS] at *
  rw [h1, h2]
  simp only [Ranks.rankY, Ranks.r, Ranks.rS]
  omega

structure Pair (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) where
  lam : Submodule (𝓞 D.host.E) (VS D).V
  mem : lam ∈ what₂
  fst : Carrier (PD D lam (lf D F0) u')
  snd : Carrier (PD D lam (lf D F0) u')
  G_fst : Gval (lf D F0) fst.1 ≠ 0
  G_snd : Gval (lf D F0) snd.1 ≠ 0
  beta : (VS D).V ≃ₗ[D.host.E] (VS D).V
  isPair : IsPair lam (lf D F0) fst.1 snd.1 beta (gS D)

variable {D}

section PairAttr

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def Pair.pfst (p : Pair D u u' F0 what₂) : Term D u u' F0 what₂ := ⟨p.lam, p.mem, TermDef.mk _ _ _ p.fst⟩

def Pair.psnd (p : Pair D u u' F0 what₂) : Term D u u' F0 what₂ := ⟨p.lam, p.mem, TermDef.mk _ _ _ p.snd⟩

def Pair.s0 (p : Pair D u u' F0 what₂) : ℕ := Lat.s0 p.lam (lf D F0) p.fst.1 p.snd.1 p.beta D.R.k

def Pair.scalarPair (p : Pair D u u' F0 what₂) : Prop :=
  p.s0 = 1 ∧ IsScalar p.lam (lf D F0) p.fst.1 p.snd.1 p.beta

end PairAttr

variable (D)

def ScalRelD {u : D.what₂.Word} (u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x y : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0}) : Prop :=
  ScalRel Λ (gS D) D.R.k (lf D F0) x.1.1 y.1.1

def ScalarEquiv (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Equivalence (ScalRelD D u' F0 Λ)

def BetaL (u u' : D.what₂.Word) : Prop :=
  (∀ i, 3 ≤ D.host.g i ∧ LemmaN.Unram D.host.E (D.host.g i)) →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y : Carrier (PD D Λ (lf D F0) u'),
      Gval (lf D F0) x.1 ≠ 0 → Gval (lf D F0) y.1 ≠ 0 →
      ∀ β₁ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V,
        IsPair Λ (lf D F0) x.1 y.1 β₁ (gS D) → IsPair Λ (lf D F0) x.1 y.1 β₂ (gS D) →
        ∀ v ∈ orth (VS D) (Xsp x.1), β₁ v - β₂ v ∈ Xsp y.1

def BetaFree (u u' : D.what₂.Word) : Prop :=
  (∀ i, 3 ≤ D.host.g i ∧ LemmaN.Unram D.host.E (D.host.g i)) →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y : Carrier (PD D Λ (lf D F0) u'),
      Gval (lf D F0) x.1 ≠ 0 → Gval (lf D F0) y.1 ≠ 0 →
      ∀ β₁ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V,
        IsPair Λ (lf D F0) x.1 y.1 β₁ (gS D) → IsPair Λ (lf D F0) x.1 y.1 β₂ (gS D) →
        Lat.s0 Λ (lf D F0) x.1 y.1 β₁ D.R.k = Lat.s0 Λ (lf D F0) x.1 y.1 β₂ D.R.k ∧
        (IsScalar Λ (lf D F0) x.1 y.1 β₁ ↔ IsScalar Λ (lf D F0) x.1 y.1 β₂)

def ScalarRepFree (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y y' : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0},
      Rel Λ (lf D F0) (PD D Λ (lf D F0) u') y.1 y'.1 → ScalRelD D u' F0 Λ x y → ScalRelD D u' F0 Λ x y'

def TermScal {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (t₁ t₂ : Term D u u' F0 what₂) : Prop :=
  ∃ p : Pair D u u' F0 what₂, p.pfst = t₁ ∧ p.psnd = t₂ ∧ p.scalarPair

def ScalarEquivT (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ →
      Equivalence (fun t₁ t₂ : {t : Term D u u' F0 what₂ // t.G ≠ 0} => TermScal D t₁.1 t₂.1)

def ScalarDr (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ → ∀ p : Pair D u u' F0 what₂, p.scalarPair →
      (Dr (lf D F0) p.fst.1 = 0 ↔ Dr (lf D F0) p.snd.1 = 0)

variable {D}

theorem tu_ne_zero (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem scalarEquiv_of_G (h : ScalarEquivG) (u u' : D.what₂.Word) : ScalarEquiv D u u' := by
  intro F0 Λ hΛ
  have hlat : Submodule.IsFullLattice D.host.E Λ := hΛ.1.1
  have hlift : IsLift Λ (lf D F0) := hΛ.2.1.2.2.1
  have e := h D.host.E (VS D) D.R.rS D.R.k (gS D) (finrank_VS D) Λ hlat ((Tu D u : ℕ) : D.host.E)
    ((Tu D u' : ℕ) : D.host.E) (tu_ne_zero u) (tu_ne_zero u') (lf D F0) hlift
  refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} h1 h2 => ?_⟩
  · exact e.refl ⟨x.1.1, x.1.2.1, x.2⟩
  · exact e.symm (x := ⟨x.1.1, x.1.2.1, x.2⟩) (y := ⟨y.1.1, y.1.2.1, y.2⟩) hxy
  · exact e.trans (x := ⟨x.1.1, x.1.2.1, x.2⟩) (y := ⟨y.1.1, y.1.2.1, y.2⟩) (z := ⟨z.1.1, z.1.2.1, z.2⟩) h1 h2

theorem scalarEquivT_of {D : D7} {u u' : D.what₂.Word} (hEq : TermEqIff D u u') (hE : ScalarEquiv D u u')
    (hR : ScalarRepFree D u u') : ScalarEquivT D u u' := by
  intro F0 what₂ hrows
  refine ⟨fun t => ?_, fun {t₁ t₂} h => ?_, fun {t₁ t₂ t₃} h₁ h₂ => ?_⟩
  · obtain ⟨⟨lam, mem, cls⟩, hG⟩ := t
    have hΛ := hrows.1 lam mem
    have hx : Gval (lf D F0) (Quot.out cls).1 ≠ 0 := hG
    obtain ⟨β, hp, hs, hsc⟩ := (hE F0 lam hΛ).refl ⟨Quot.out cls, hx⟩
    refine ⟨⟨lam, mem, Quot.out cls, Quot.out cls, hx, hx, β, hp⟩, ?_, ?_, hs, hsc⟩
    · simp only [Pair.pfst]; congr 1; exact Quot.out_eq cls
    · simp only [Pair.psnd]; congr 1; exact Quot.out_eq cls
  · obtain ⟨p, h1, h2, hs, hsc⟩ := h
    have hΛ := hrows.1 p.lam p.mem
    obtain ⟨β, hp, hs', hsc'⟩ := (hE F0 p.lam hΛ).symm (x := ⟨p.fst, p.G_fst⟩) (y := ⟨p.snd, p.G_snd⟩)
      ⟨p.beta, p.isPair, hs, hsc⟩
    exact ⟨⟨p.lam, p.mem, p.snd, p.fst, p.G_snd, p.G_fst, β, hp⟩, h2, h1, hs', hsc'⟩
  · obtain ⟨p, hp1, hp2, hps, hpsc⟩ := h₁
    obtain ⟨q, hq1, hq2, hqs, hqsc⟩ := h₂
    have hpq : p.psnd = q.pfst := hp2.trans hq1.symm
    obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := p
    obtain ⟨lq, mq, q1, q2, gq1, gq2, bq, iq⟩ := q
    simp only [Pair.psnd, Pair.pfst, Term.mk.injEq] at hpq
    obtain ⟨rfl, hcls⟩ := hpq
    have hcls' : TermDef.mk lp (lf D F0) (PD D lp (lf D F0) u') p2 = TermDef.mk lp (lf D F0) (PD D lp (lf D F0) u') q1 :=
      eq_of_heq hcls
    have hΛ := hrows.1 lp mp
    have hrel := (hEq F0 lp hΛ p2 q1).1 hcls'
    have a1 : ScalRelD D u' F0 lp ⟨p1, gp1⟩ ⟨p2, gp2⟩ := ⟨bp, ip, hps, hpsc⟩
    have a2 : ScalRelD D u' F0 lp ⟨p1, gp1⟩ ⟨q1, gq1⟩ := hR F0 lp hΛ ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨q1, gq1⟩ hrel a1
    have a3 : ScalRelD D u' F0 lp ⟨q1, gq1⟩ ⟨q2, gq2⟩ := ⟨bq, iq, hqs, hqsc⟩
    obtain ⟨β, hb, hs, hsc⟩ := (hE F0 lp hΛ).trans a2 a3
    exact ⟨⟨lp, mp, p1, q2, gp1, gq2, β, hb⟩, hp1, hq2, hs, hsc⟩

end D7

end Formalism.L2.SG.Corank
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.FourParts

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def InSF {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  (∀ a : Fin r, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) ∧ F'.fl.z - F.fl.z ∈ Xsp F

def IsIdF (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  ∃ n ∈ NLam Λ F, (∀ a, n (F.fl.e a) = F'.fl.e a) ∧ n F.fl.z - F'.fl.z ∈ Xsp F

theorem e_mem_Xflag {T : E} (F : LFlag S r T) (a : Fin r) : F.fl.e a ∈ Xflag F (a.val + 1) :=
  Submodule.subset_span ⟨a, by simp, rfl⟩

theorem Xflag_zero {T : E} (F : LFlag S r T) : Xflag F 0 = ⊥ := by
  simp [Xflag, FlagG.Xa]

theorem Xflag_r {T : E} (F : LFlag S r T) : F.fl.Xa r = Xsp F := by
  simp only [FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext x
  simp

theorem z_mem_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F.fl.z_orth a
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

theorem inSF_of_isIdF (Λ : Submodule (𝓞 E) S.V) {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}
    (h : IsIdF Λ F F') : InSF F F' := by
  obtain ⟨n, hn, he, hz⟩ := h
  refine ⟨fun a => ?_, ?_⟩
  · rw [← he a]
    exact hn.2.1 a.val _ (e_mem_Xflag F a)
  · have e : F'.fl.z - F.fl.z = (n F.fl.z - F.fl.z) - (n F.fl.z - F'.fl.z) := by abel
    rw [e]
    exact Submodule.sub_mem _ (hn.2.2 _ (z_mem_orth F)) hz

theorem gval_eq_zero_of_inSF {T T' : E} (hT : star T = T) {F : LFlag S r T} {F' : LFlag S r T'}
    (h : InSF F F') : Gval F F' = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hz : F'.fl.z = F.fl.z := by
      have := h.2
      simp [Xsp, FlagG.X] at this
      exact sub_eq_zero.1 this
    have hTT : T' = T := by
      have h1 := F'.fl.z_norm
      have h2 := F.fl.z_norm
      rw [hz, h2] at h1
      exact (neg_inj.1 h1).symm
    subst hTT
    have hf : ∀ {T₁ : E} (G : LFlag S 0 T₁) (i : Fin 1), G.fl.fvec i = G.fl.z := by
      intro T₁ G i
      rw [Subsingleton.elim i (Fin.last 0)]
      exact Fin.snoc_last (α := fun _ => S.V) (p := G.fl.e) (x := G.fl.z)
    have hD1 : Dl F.fl F'.fl 1 = -T' := by
      simp only [Dl, leadMinorE]
      simp only [Nat.le_refl, dif_pos, Matrix.det_unique]
      show S.hT (F.fl.fvec _) (F'.fl.fvec _) = -T'
      rw [hf F, hf F', hz, F.fl.z_norm]
    have hD0 : Dl F.fl F'.fl 0 = 1 := by
      simp [Dl, leadMinorE]
    simp only [Gval, Gflag, zero_add, hD1, hD0]
    simp [star_neg, hT]
  · have h0 : F'.fl.e ⟨0, hr⟩ = F.fl.e ⟨0, hr⟩ := by
      have := h.1 ⟨0, hr⟩
      rw [Xflag_zero, Submodule.mem_bot] at this
      exact sub_eq_zero.1 this
    have hcol : ∀ a : Fin (r + 1), Zhat F.fl F'.fl a ⟨0, by omega⟩ = 0 := by
      intro a
      have hv : F'.fl.fvec ⟨0, by omega⟩ = F.fl.e ⟨0, hr⟩ := by
        show Fin.snoc (α := fun _ => S.V) F'.fl.e F'.fl.z (Fin.castSucc ⟨0, hr⟩) = _
        rw [Fin.snoc_castSucc, h0]
      simp only [Zhat, brS, hv]
      refine Fin.lastCases ?_ (fun b => ?_) a
      · simp only [FlagG.fvec, Fin.snoc_last]
        exact S.herm.eq_iff.1 (F.fl.z_orth ⟨0, hr⟩)
      · simp [FlagG.fvec, F.fl.e_iso]
    have hDl : ∀ l, 1 ≤ l → l ≤ r + 1 → Dl F.fl F'.fl l = 0 := by
      intro l hl1 hl2
      simp only [Dl, leadMinorE, dif_pos hl2]
      refine Matrix.det_eq_zero_of_column_eq_zero ⟨0, by omega⟩ (fun i => ?_)
      simp only [Matrix.submatrix_apply]
      have : (Fin.castLE hl2 ⟨0, by omega⟩ : Fin (r + 1)) = ⟨0, by omega⟩ := rfl
      rw [this]
      exact hcol _
    simp only [Gval, Gflag, hDl (r + 1) (by omega) le_rfl, hDl r hr (by omega)]
    simp

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop)

def IsInS (t : TermQ Λ F P) : Prop := ∃ F', Rep Λ F P t F' ∧ InSF F F'

def IsIdT (t : TermQ Λ F P) : Prop := ∃ F', Rep Λ F P t F' ∧ IsIdF Λ F F'

def InSFun : Prop := ∀ x y : Carrier P, Rel Λ F P x y → (InSF F x.1 ↔ InSF F y.1)

def IdIffInS (K : Type) [Field K] [Algebra K E] : Prop :=
  ∀ x : Carrier P, Relevant K F.fl x.1.fl → InSF F x.1 → IsIdF Λ F x.1

def InSRel (K : Type) [Field K] [Algebra K E] : Prop :=
  ∀ x : Carrier P, InSF F x.1 → Relevant K F.fl x.1.fl

variable {Λ F P}

theorem isInS_of_isIdT {t : TermQ Λ F P} (h : IsIdT Λ F P t) : IsInS Λ F P t := by
  obtain ⟨F', hr, hid⟩ := h
  exact ⟨F', hr, inSF_of_isIdF Λ hid⟩

theorem isInS_mk (hI : InSFun Λ F P) (x : Carrier P) : IsInS Λ F P (mk Λ F P x) ↔ InSF F x.1 := by
  constructor
  · rintro ⟨F', ⟨h, hmk⟩, hin⟩
    have := const_of_mk (fun y : Carrier P => InSF F y.1) (fun a b hab => propext (hI a b hab)) hmk
    simpa [this] using hin
  · intro h
    exact ⟨x.1, rep_mk x, h⟩

theorem gt_eq_zero_of_isInS (hG : GFun Λ F P) (hT : star T = T) {t : TermQ Λ F P} (h : IsInS Λ F P t) :
    Gt Λ F P t = 0 := by
  obtain ⟨F', ⟨hP, hmk⟩, hin⟩ := h
  subst hmk
  rw [Gt_mk hG]
  exact gval_eq_zero_of_inSF hT hin

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def termInS (t : Term D u u' F0 what₂) : Prop := IsInS _ _ _ t.cls

def termIsId (t : Term D u u' F0 what₂) : Prop := IsIdT _ _ _ t.cls

theorem termInS_of_termIsId {t : Term D u u' F0 what₂} (h : termIsId t) : termInS t := isInS_of_isIdT h

variable (D u u' F0 what₂)

variable {D u u' F0 what₂}

theorem G_eq_zero_of_termInS {t : Term D u u' F0 what₂} (hG : GFun t.lam (lf D F0) (PD D t.lam (lf D F0) u'))
    (h : termInS t) : t.G = 0 := by
  refine gt_eq_zero_of_isInS (T := ((Tu D u : ℕ) : D.host.E)) hG ?_ h
  exact star_natCast _

variable (D)

def TermInSFun (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → InSFun Λ (lf D F0) (PD D Λ (lf D F0) u')

def TermIdIffInS (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → IdIffInS Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F

def TermInSRel (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → InSRel (lf D F0) (PD D Λ (lf D F0) u') D.host.F

variable {D}

end D7

end Formalism.L2.SG.FourParts
end
end

