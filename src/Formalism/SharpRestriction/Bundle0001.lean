module

public import Formalism.LocalRingCardinality.DataParams₂

@[expose] public section

-- bundled from Formalism.SharpRestriction.ElevenLe
section
noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

variable {D : D7} (L : SizeData₂ D)

def szTh : ℝ := L.sc.eps / 100

def szNst : ℝ := 2 * (D.R.n : ℝ) * L.sc.delta1

def szlA : ℝ := (D.R.k : ℝ) * L.sc.x ^ L.sc.eps / ((D.R.m : ℝ) * L.de2)

def szlStar : ℝ :=
  (D.R.m : ℝ) * L.sc.b /
    ((D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
      (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L))

def szCond (_L : SizeData₂ D) : ℝ := (D.host.QS : ℝ) * D.host.q * D.host.d

def SizeN : Prop :=
  L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L)

def SizeM : Prop :=
  L.sc.x ^ (-szTh L) * Real.sqrt (L.sc.x * L.sc.delta1) ≤ (D.R.m : ℝ) ∧
    (D.R.m : ℝ) ≤ L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)

def SizeK : Prop :=
  L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) ≤ (D.R.k : ℝ) ∧
    (D.R.k : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps + szTh L)

def SizeKRel : Prop :=
  L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps ≤ D.R.k ∧
  8 * L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L ≤ D.R.k ∧
  (D.R.k : ℝ) ≤ Real.sqrt L.sc.x * D.R.n * rankBudget D.R L.sc.x L.sc.eps ∧
  Real.sqrt ((D.R.k : ℝ) / D.R.m) ≤ rankBudget D.R L.sc.x L.sc.eps ∧
  (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k ∧
  (D.R.m : ℝ) * Real.sqrt L.sc.x * Real.log L.sc.x ≤ D.R.k ∧
  L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 6 * L.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 3 * L.sc.L * Real.log D.host.rdE ≤ (D.R.k : ℝ) * Real.log D.R.k ^ 2 ∧
  Real.log D.R.f ≤ Real.sqrt D.R.rS ∧
  Real.log D.R.f ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L ∧
  L.sc.x ^ szTh L * Real.log (Real.log L.sc.b) ≤ (D.R.r : ℝ) * D.R.f * Real.log D.R.r ∧
  L.sc.x ^ szTh L * L.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k ∧
  (D.R.f : ℝ) ≤ (D.R.m : ℝ) ^ 2 * D.R.n ∧
  (D.R.f : ℝ) ≤ (D.R.r : ℝ) ^ 2

def SizeT : Prop :=
  1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ L.sc.x ^ (L.Ct + szTh L)

def SizeCond : Prop := szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b

def SizeQD : Prop :=
  L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q ∧
  L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ Real.log D.host.q ∧
  Real.log D.host.q ≤ L.sc.x ^ (L.sc.eps / 5 + szTh L) ∧
  L.sc.x ^ (L.sc.ez / 5 - L.sc.ez / 100) ≤ Real.log D.host.d ∧
  Real.log D.host.d ≤ L.sc.x ^ (L.sc.eps / 5 + szTh L) ∧
  |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps ∧
  1 ≤ D.host.rdE ∧ D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)

def SizeTT : Prop :=
  L.sc.x ^ (-szTh L) * D.R.n * L.sc.delta1 ≤ (D.host.TT.card : ℝ) ∧ (D.host.TT.card : ℝ) ≤ szNst L

def SizeLa : Prop := L.sc.x ^ L.sc.eps ≤ L.LaG ∧ L.LaG ≤ L.sc.x ^ (L.sc.eps + szTh L)

def SizeRho : Prop :=
  4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k + L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤
    L.sc.x ^ (-2 : ℝ)

def SizeBot : Prop :=
  ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k

def SizeDe2 : Prop := L.sc.x ^ (-L.sc.eps) ≤ L.de2

def SizeLw : Prop := (D.host.Lw : ℝ) ≤ Real.log L.sc.x ^ 2

def SizeEta : Prop :=
  (D.R.t : ℝ) ≤ L.etaSz ∧
  L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) ∧
  Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4) ∧
  (D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x ∧
  (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧
  (D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L ∧
  (D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ∧
  L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2 ∧
  (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * szlA L ≤ L.de2 * D.R.m * L.sc.b

def SizeNodes : Prop :=
  12 * L.sc.b / szlStar L + 2 * D.R.t + 8 ≤ L.etaSz / D.R.m ∧
  (D.R.k : ℝ) * D.R.t * L.sc.L ≤ L.etaSz / D.R.m ∧
  L.sc.x ^ szTh L * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ L.etaSz / D.R.m ∧
  4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ L.etaSz / D.R.m ∧
  L.sc.x ^ szTh L * D.R.k * (D.R.m : ℝ) ^ (9 / 2 : ℝ) ≤ L.etaSz / D.R.m ∧
  2 * ((D.R.r : ℝ) + D.R.m * D.R.t) ^ 3 + D.R.t + 3 ≤ L.etaSz / D.R.m ∧
  (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ L.etaSz / D.R.m

def SizeLstar : Prop :=
  L.sc.b' + L.Sc + L.etaSz + L.sc.b / szlStar L < szlStar L ∧
  2 * L.etaSz + D.R.t + 8 * L.sc.b / szlStar L + 7 < szlStar L

def SizeDel : Prop :=
  (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) ∧
  L.sc.x ^ szTh L * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧
  Real.log (D.s.Del : ℝ) ≤ L.sc.x ^ (L.sc.eps / 4) / 2 ∧
  (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
  L.sc.x ^ szTh L * D.R.m * D.R.k * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n ∧
  4 * L.Sc ≤ L.LaG * L.sc.b' / D.R.k ∧
  4 * L.sc.x ^ szTh L * (D.R.k : ℝ) ^ 2 * (D.s.Del : ℝ) ≤ L.LaG * L.sc.b' ∧
  L.sc.x ^ szTh L * D.R.m * Real.log D.host.v ≤ D.R.k

def SizeW : Prop := Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n

def SizeBm (_L : SizeData₂ D) : Prop :=
  ∀ τ (h : 0 < D.R.m), (((D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) ≤ 2 * (((D.hc τ).b ⟨0, h⟩ : ℚ) : ℝ)

def SizeXpp : Prop :=
  ∀ j τ j' τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m → wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ'

def SizeG : Prop :=
  ∀ i j : Fin 2, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * (D.host.g j : ℝ) ∧
    Real.log (D.host.g i : ℝ) ≤ L.sc.x ^ szTh L * L.sc.L

def SizeTu : Prop := ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ L.sc.x ^ szTh L * D.R.m * L.sc.L

def SizePde : Prop :=
  Real.log (D.host.pde : ℝ) ≤ L.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ L.sc.L

def SizeWords (_L : SizeData₂ D) : Prop := @Fintype.card D.what₂.Word D.wordFin ≤ 2 ^ (D.R.k - 3)

def SizesAt : Prop :=
  SizeN L ∧ SizeM L ∧ SizeK L ∧ SizeKRel L ∧ SizeT L ∧ SizeCond L ∧ SizeQD L ∧ SizeTT L ∧
  SizeLa L ∧ SizeRho L ∧ SizeBot L ∧ SizeDe2 L ∧ SizeLw L ∧ SizeEta L ∧ SizeNodes L ∧
  SizeLstar L ∧ SizeDel L ∧ SizeW L ∧ SizeBm L ∧ SizeXpp L ∧ SizeG L ∧ SizePde L ∧
  SizeWords L ∧ 11 ≤ D.host.splitBound

theorem SizesAt.eleven_le {D : D7} {L : SizeData₂ D} (S : SizesAt L) : 11 ≤ D.host.splitBound :=
  S.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Formalism.MainNotions

end
end

-- bundled from Formalism.SharpRestriction.FamCore
section
noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions NumberField

def aWin {D : D7} (L : SizeData₂ D) (a : ℤ) : Prop :=
  L.sc.a ≤ (a : ℝ) ∧ (a : ℝ) ≤ L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))

def wordBits (D : D7) (u : D.what₂.Word) (l : ℕ) : Bool :=
  if h : l < D.R.k - 2 then D.s.letter u ⟨l, h⟩ else false

def suppAt {D : D7} (L : SizeData₂ D) (p : ℕ) : Finset D.what₂.places.Pl :=
  L.supp.filter (fun w => D.what₂.places.resChar w = p)

theorem wt_self {D : D7} (L : SizeData₂ D) (TTn : Finset ℕ) (bTop : ℝ) (hTT : D.host.TT.image Formalism.HC.Frame.A.val = TTn)
    (hb : ∀ t : D.host.TT, (L.bT t : ℝ) ≤ bTop) :
    ∃ a b : ℕ → ℤ, (∀ t ∈ TTn, aWin L (a t) ∧ L.sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ bTop) ∧
      ∀ t : D.host.TT, a (t : D.R.A).val = L.aT t ∧ b (t : D.R.A).val = L.bT t := by
  classical
  have hinj : ∀ t1 t2 : D.host.TT, (t1 : D.R.A).val = (t2 : D.R.A).val → t1 = t2 :=
    fun t1 t2 h => Subtype.ext (Fin.ext h)
  refine ⟨fun v => if h : ∃ t : D.host.TT, (t : D.R.A).val = v then L.aT h.choose else 0,
    fun v => if h : ∃ t : D.host.TT, (t : D.R.A).val = v then L.bT h.choose else 0, ?_, ?_⟩
  · intro v hv
    rw [← hTT] at hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hv
    have h : ∃ t' : D.host.TT, (t' : D.R.A).val = t.val := ⟨⟨t, ht⟩, rfl⟩
    simp only [dif_pos h]
    exact ⟨L.aT_win _, L.bT_ge _, hb _⟩
  · intro t
    have h : ∃ t' : D.host.TT, (t' : D.R.A).val = (t : D.R.A).val := ⟨t, rfl⟩
    have e := hinj _ _ h.choose_spec
    refine ⟨?_, ?_⟩ <;> simp only [dif_pos h, e]

def artNum {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) : Formalism.FrobeniusOrbits.G0 × ℕ :=
  if h : Nat.Coprime p H.condN then
    ((H.art (ZMod.unitOfCoprime p h)).1, (φ.iotaInv (H.art (ZMod.unitOfCoprime p h)).2).val) else (1, 0)

structure FamCore (eps : ℝ) where

  x1 : ℝ
  one_lt_family_threshold : 1 < x1

  Ix : ℝ → Type

  Win : Set ℝ
  Win_unb : ∀ y : ℝ, ∃ x ∈ Win, y ≤ x
  Ix_win : ∀ x ∈ Win, Nonempty (Ix x)
  Ix_zero : Nonempty (Ix 0)
  D : ∀ x, Ix x → D7
  L : ∀ x (i : Ix x), SizeData₂ (D x i)
  L_x : ∀ x i, x1 < x → (L x i).sc.x = x
  L_eps : ∀ x i, (L x i).sc.eps = eps

  J : ℝ
  L_J : ∀ x i, (L x i).sc.J = J

  R_eq : ∀ x (i i' : Ix x), (D x i).R = (D x i').R
  TTn : ℝ → Finset ℕ
  TT_eq : ∀ x i, (D x i).host.TT.image Formalism.HC.Frame.A.val = TTn x
  realisedChain_torus_eq : ∀ x (i i' : Ix x), (D x i).host.T2 = (D x i').host.T2
  q_eq : ∀ x (i i' : Ix x), (D x i).host.q = (D x i').host.q
  d_eq : ∀ x (i i' : Ix x), (D x i).host.d = (D x i').host.d

  QS_eq : ∀ x (i i' : Ix x), (D x i).host.QS = (D x i').host.QS
  art_eq : ∀ x (i i' : Ix x), artNum (D x i).host.toHostRaw = artNum (D x i').host.toHostRaw
  rd_eq : ∀ x (i i' : Ix x), (D x i).host.rdE = (D x i').host.rdE

  Co : ℝ
  o_le_Co : ∀ x i, x1 < x → ((D x i).R.o : ℝ) ≤ Co
  QS_le_Co : ∀ x i, x1 < x → ((D x i).host.QS : ℝ) ≤ Co * (D x i).R.n
  g_eq : ∀ x (i i' : Ix x), (D x i).host.g = (D x i').host.g
  pde_eq : ∀ x (i i' : Ix x), (D x i).host.pde = (D x i').host.pde ∧ (D x i).host.pde' = (D x i').host.pde'

  W : ℝ → Type
  eW : ∀ x (i : Ix x), (D x i).what₂.Word ≃ W x

  eW_code : ∀ x (i i' : Ix x) (u : (D x i).what₂.Word) (u' : (D x i').what₂.Word),
    eW x i u = eW x i' u' → wordBits (D x i) u = wordBits (D x i') u'

  CGam : ℝ
  CGam_eq : ∀ x i, (L x i).CGam = CGam

  Cc : ℝ
  Cc_eq : ∀ x i, (L x i).Cc = Cc
  Ct : ℝ
  Ct_eq : ∀ x i, (L x i).Ct = Ct
  CT2 : ℝ
  secondConstant_eq : ∀ x i, (D x i).host.CT2 = CT2

  bTop : ℝ → ℝ
  bTop_eq : ∀ x, x1 < x → ∀ i, bTop x = (L x i).sc.b' +
    2 * ((D x i).R.n : ℝ) * (L x i).sc.delta1 * x ^ eps * (L x i).LaG * (L x i).sc.b' / ((D x i).R.k : ℝ)

  bTop_ge : ∀ x, x1 < x → ∀ i, (L x i).sc.b' +
    2 * ((D x i).R.n : ℝ) * (L x i).sc.delta1 * x ^ (2 * eps) * (L x i).sc.b' / ((D x i).R.k : ℝ) ≤ bTop x

  bT_le : ∀ x, x1 < x → ∀ i (t : (D x i).host.TT), ((L x i).bT t : ℝ) ≤ bTop x

  coverS : ∀ x, x1 < x → ∀ (i0 : Ix x) (u0 : ℕ), u0 < (D x i0).R.n →
    ∃ i : Ix x, (D x i).host.u0.val = u0 ∧
      ∀ (t : (D x i).host.TT) (t0 : (D x i0).host.TT),
        (t : (D x i).R.A).val = (t0 : (D x i0).R.A).val →
          (L x i).aT t = (L x i0).aT t0 ∧ (L x i).bT t = (L x i0).bT t0

theorem FamCore.exists_pt {eps : ℝ} (Fm : FamCore eps) (y : ℝ) : ∃ x, y ≤ x ∧ Fm.x1 < x ∧ x ∈ Fm.Win ∧ Nonempty (Fm.Ix x) := by
  obtain ⟨x, hx, hyx⟩ := Fm.Win_unb (max y (Fm.x1 + 1))
  have h1 := le_max_left y (Fm.x1 + 1)
  have h2 := le_max_right y (Fm.x1 + 1)
  exact ⟨x, le_trans h1 hyx, by linarith, hx, Fm.Ix_win x hx⟩

theorem FamCore.one_le_J {eps : ℝ} (Fm : FamCore eps) : 1 ≤ Fm.J := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_J 0 i]
  exact (Fm.L 0 i).sc.one_le_J

def FamCore.ez {eps : ℝ} (Fm : FamCore eps) : ℝ := eps / Fm.J

theorem FamCore.L_ez {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (i : Fm.Ix x) : (Fm.L x i).sc.ez = Fm.ez := by
  show (Fm.L x i).sc.eps / (Fm.L x i).sc.J = eps / Fm.J
  rw [Fm.L_eps, Fm.L_J]

def FamCore.Windows {eps : ℝ} (Fm : FamCore eps) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ Fm.Win

theorem FamCore.coverS_carry {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (hx : Fm.x1 < x) (i0 : Fm.Ix x) (av bv : ℕ → ℤ)
    (hc : ∀ t : (Fm.D x i0).host.TT, (Fm.L x i0).aT t = av (t : (Fm.D x i0).R.A).val ∧
      (Fm.L x i0).bT t = bv (t : (Fm.D x i0).R.A).val)
    (u0 : ℕ) (hu : u0 < (Fm.D x i0).R.n) :
    ∃ i : Fm.Ix x, (Fm.D x i).host.u0.val = u0 ∧
      ∀ t : (Fm.D x i).host.TT, (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val := by
  classical
  obtain ⟨i, hi, hag⟩ := Fm.coverS x hx i0 u0 hu
  refine ⟨i, hi, fun t => ?_⟩
  have hv : (t : (Fm.D x i).R.A).val ∈ Fm.TTn x := by
    rw [← Fm.TT_eq x i]
    exact Finset.mem_image_of_mem _ t.2
  rw [← Fm.TT_eq x i0] at hv
  obtain ⟨t0, ht0, he⟩ := Finset.mem_image.1 hv
  obtain ⟨h1, h2⟩ := hag t ⟨t0, ht0⟩ he.symm
  obtain ⟨h3, h4⟩ := hc ⟨t0, ht0⟩
  rw [h1, h2, h3, h4]
  exact ⟨by rw [he], by rw [he]⟩

theorem FamCore.coverU_hyp_self {eps : ℝ} (Fm : FamCore eps) (x : ℝ) (hx : Fm.x1 < x) (i0 : Fm.Ix x) :
    ∃ a b : ℕ → ℤ,
      (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (a t) ∧ (Fm.L x i0).sc.b' ≤ (b t : ℝ) ∧ (b t : ℝ) ≤ Fm.bTop x) ∧
      ∀ t : (Fm.D x i0).host.TT, a (t : (Fm.D x i0).R.A).val = (Fm.L x i0).aT t ∧
        b (t : (Fm.D x i0).R.A).val = (Fm.L x i0).bT t := by
  exact wt_self (Fm.L x i0) (Fm.TTn x) (Fm.bTop x) (Fm.TT_eq x i0) (fun t => Fm.bT_le x hx i0 t)

end Formalism.MainNotions

end
end

