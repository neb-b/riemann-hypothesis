module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CloseOfTarget
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount

section Lat

variable {K : Type*} [CommRing K] (I : Subring K)

def lat (c : K) : AddSubgroup K where
  carrier := {x | ∃ y ∈ I, x = c * y}
  zero_mem' := ⟨0, I.zero_mem, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', I.add_mem hy hy', by ring⟩
  neg_mem' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, I.neg_mem hy, by ring⟩

variable {I}

theorem lat_mul {c c' x x' : K} (hx : x ∈ lat I c) (hx' : x' ∈ lat I c') : x * x' ∈ lat I (c * c') := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hx'
  exact ⟨y * y', I.mul_mem hy hy', by ring⟩

theorem lat_bmul {t c b x : K} (hb : t * b ∈ I) (hx : x ∈ lat I (t * c)) : b * x ∈ lat I c := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨t * b * y, I.mul_mem hb hy, by ring⟩

theorem lat_mulb {t c b x : K} (hb : t * b ∈ I) (hx : x ∈ lat I (t * c)) : x * b ∈ lat I c := by
  rw [mul_comm]; exact lat_bmul hb hx

theorem lat_mono {t c x : K} (ht : t ∈ I) (hx : x ∈ lat I (t * c)) : x ∈ lat I c := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨t * y, I.mul_mem ht hy, by ring⟩

theorem mem_of_lat {c x : K} (hc : c ∈ I) (hx : x ∈ lat I c) : x ∈ I := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact I.mul_mem hc hy

theorem lat_one {x : K} (hx : x ∈ lat I 1) : x ∈ I := mem_of_lat I.one_mem hx

theorem lat_sq {c : K} (hc : c ∈ I) : ∀ x ∈ lat I c, ∀ y ∈ lat I c, x * y ∈ lat I c :=
  fun _ hx _ hy => lat_mono hc (lat_mul hx hy)

variable {n : ℕ}

theorem ent_bmul {t c : K} {B X : Matrix (Fin n) (Fin n) K} (hB : ∀ i j, t * B i j ∈ I)
    (hX : EntIn (lat I (t * c)) X) : EntIn (lat I c) (B * X) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (lat I c).sum_mem fun k _ => lat_bmul (hB i k) (hX k j)

theorem ent_mulb {t c : K} {B X : Matrix (Fin n) (Fin n) K} (hB : ∀ i j, t * B i j ∈ I)
    (hX : EntIn (lat I (t * c)) X) : EntIn (lat I c) (X * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (lat I c).sum_mem fun k _ => lat_mulb (hB k j) (hX i k)

theorem ent_mono {t c : K} (ht : t ∈ I) {X : Matrix (Fin n) (Fin n) K} (hX : EntIn (lat I (t * c)) X) :
    EntIn (lat I c) X := fun i j => lat_mono ht (hX i j)

end Lat

section Bnd

variable {Fp : Type*} [Field Fp] {K : Type*} [CommRing K] [Algebra Fp K] {I : Subring K}

theorem bnd_fin (O : Subring Fp) (hI : ∀ s ∈ O, algebraMap Fp K s ∈ I) {ι : Type*} [Fintype ι] (f : ι → K)
    (h : ∀ i, ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ algebraMap Fp K s * f i ∈ I) :
    ∃ s : Fp, s ≠ 0 ∧ s ∈ O ∧ ∀ i, algebraMap Fp K s * f i ∈ I := by
  classical
  choose s hs0 hsO hs using h
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, O.prod_mem fun i _ => hsO i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), map_mul,
    mul_comm (algebraMap Fp K (s i)), mul_assoc]
  exact I.mul_mem (hI _ (O.prod_mem fun j _ => hsO j)) (hs i)

end Bnd

section Stab

variable {K : Type*} [CommRing K]

theorem stab_core {r : ℕ} {P P' Q Q' N kL kR : Matrix (Fin (r + 1)) (Fin (r + 1)) K} {s e : K} (hs : IsUnit s)
    (hP : P' * P = 1) (hQ : Q * Q' = 1) (hkL : IsLo kL) (hkR : IsUp kR)
    (hk : kL * (s • (P * N * Q) - e • Ecorner r) * kR = s • (P * N * Q) - e • Ecorner r) :
    (P' * kL * P) * N * (Q * kR * Q') = N := by
  have h1 : kL * (s • (P * N * Q) - e • Ecorner r) * kR = s • (kL * (P * N * Q) * kR) - e • Ecorner r := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hkL hkR]
  rw [h1] at hk
  have h2 : s • (kL * (P * N * Q) * kR) = s • (P * N * Q) := sub_left_injective hk
  have h3 : kL * (P * N * Q) * kR = P * N * Q := hs.smul_left_cancel.mp h2
  calc (P' * kL * P) * N * (Q * kR * Q') = P' * (kL * (P * N * Q) * kR) * Q' := by
        simp only [Matrix.mul_assoc]
    _ = N := by
        rw [h3]
        simp only [Matrix.mul_assoc]
        rw [hQ, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]

variable {n : ℕ}

theorem fix_of {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {z w : Matrix (Fin n) (Fin n) K} (hw : IsUp w) (h : z * mono σ ν * w = mono σ ν) :
    (∀ i j, σ j < σ i → z i j = 0) ∧ cOf σ ν z * w = 1 ∧ w * cOf σ ν z = 1 := by
  have hdw : IsUnit w.det := by rw [det_up' hw]; exact isUnit_one
  have e1 : z * mono σ ν = mono σ ν * w⁻¹ := by
    calc z * mono σ ν = z * mono σ ν * (w * w⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdw, Matrix.mul_one]
      _ = mono σ ν * w⁻¹ := by rw [← Matrix.mul_assoc, h]
  have hwi := isUp_inv hw
  have hpat := fix_pat hσ ν hν (fun i j hij => hwi.2 j i hij) e1
  have e2 : cOf σ ν z = w⁻¹ := by
    have e3 : mono σ ν * cOf σ ν z = mono σ ν * w⁻¹ := by rw [← fix_cOf hσ ν hν z, e1]
    ext a b
    have := congrFun (congrFun e3 (σ a)) b
    rw [mono_mul, mono_mul, hσ] at this
    exact (hν (σ a)).mul_left_cancel this
  refine ⟨hpat, ?_, ?_⟩
  · rw [e2, Matrix.nonsing_inv_mul _ hdw]
  · rw [e2, Matrix.mul_nonsing_inv _ hdw]

theorem fix_inv {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {x w : Matrix (Fin n) (Fin n) K} (hx : IsLo x) (hw : IsUp w) (h : x * mono σ ν * w = mono σ ν) :
    IsLo x⁻¹ ∧ (∀ i j, σ j < σ i → x⁻¹ i j = 0) ∧ x * x⁻¹ = 1 := by
  have hdx : IsUnit x.det := by rw [det_lo' hx]; exact isUnit_one
  have e1 : x⁻¹ * mono σ ν = mono σ ν * w := by
    calc x⁻¹ * mono σ ν = x⁻¹ * (x * mono σ ν * w) := by rw [h]
      _ = mono σ ν * w := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdx, Matrix.one_mul]
  exact ⟨isLo_inv hx, fix_pat hσ ν hν (fun i j hij => hw.2 j i hij) e1, Matrix.mul_nonsing_inv _ hdx⟩

end Stab

section Close

variable {K : Type*} [CommRing K] {I : Subring K} {n : ℕ}

theorem cOf_sub_one {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) {ν : Fin n → K} (hν : ∀ a, IsUnit (ν a))
    {t c : K} (hb : ∀ a, t * ν a ∈ I) (hb' : ∀ a, t * Ring.inverse (ν a) ∈ I) {z : Matrix (Fin n) (Fin n) K}
    (hz : EntIn (lat I (t * (t * c))) (z - 1)) : EntIn (lat I c) (cOf σ ν z - 1) := by
  intro a b
  have e : (cOf σ ν z - 1) a b = Ring.inverse (ν (σ a)) * (z - 1) (σ a) (σ b) * ν (σ b) := by
    rw [Matrix.sub_apply, Matrix.sub_apply]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      simp only [cOf, Matrix.of_apply]
      rw [mul_sub, sub_mul, mul_one, Ring.inverse_mul_cancel _ (hν _)]
    · have : σ a ≠ σ b := fun h => hab (by rw [← hσ a, h, hσ])
      rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne this]
      simp only [cOf, Matrix.of_apply, sub_zero]
  rw [e]
  exact lat_mulb (hb _) (lat_bmul (hb' _) (hz _ _))

theorem close_of_target {t c : K} {x T G : Matrix (Fin n) (Fin n) K} (hxT : x * T = 1) (bx : ∀ i j, t * x i j ∈ I)
    (hG : EntIn (lat I (t * c)) (G - T)) : EntIn (lat I c) (x * G - 1) := by
  have e : x * G - 1 = x * (G - T) := by rw [Matrix.mul_sub, hxT]
  rw [e]
  exact ent_bmul bx hG

theorem conj_eq {P P' X : Matrix (Fin n) (Fin n) K} (hPP : P * P' = 1) : P * (P' * X * P) * P' = X := by
  simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [Matrix.mul_assoc, hPP, Matrix.mul_one]

theorem conj_sub_one {P P' X : Matrix (Fin n) (Fin n) K} (hPP : P * P' = 1) : P * (P' * X * P - 1) * P' = X - 1 := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP, conj_eq hPP]

theorem close_pair {r : ℕ} {σ : Fin (r + 1) → Fin (r + 1)} (hσ : ∀ a, σ (σ a) = a) {ν : Fin (r + 1) → K}
    (hν : ∀ a, IsUnit (ν a)) {t c : K} (ht : t ∈ I) (hc : c ∈ I) (hbν : ∀ a, t * ν a ∈ I)
    (hbν' : ∀ a, t * Ring.inverse (ν a) ∈ I) {P P' Q Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hPP : P * P' = 1) (hP'P : P' * P = 1) (hQQ : Q * Q' = 1) (hQ'Q : Q' * Q = 1) (bP : ∀ i j, t * P i j ∈ I)
    (bP' : ∀ i j, t * P' i j ∈ I) (bQ : ∀ i j, t * Q i j ∈ I) (bQ' : ∀ i j, t * Q' i j ∈ I) {s e : K}
    (hs : IsUnit s) {a b : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (ha : IsLo a) (hb : IsUp b)
    (hab : a * (s • (P * mono σ ν * Q) - e • Ecorner r) * b = s • (P * mono σ ν * Q) - e • Ecorner r)
    (hz : IsLo (P' * a * P)) (hw : IsUp (Q * b * Q'))
    (hcl : EntIn (lat I (t * (t * (t * (t * c))))) (P' * a * P - 1)) :
    EntIn (lat I c) (a - 1) ∧ EntIn (lat I c) (b - 1) := by
  have hzw := stab_core hs hP'P hQQ ha hb hab
  obtain ⟨hpat, h1, h2⟩ := fix_of hσ hν hw hzw
  have hz2 : EntIn (lat I (t * (t * c))) (P' * a * P - 1) := ent_mono ht (ent_mono ht hcl)
  refine ⟨?_, ?_⟩
  · rw [← conj_sub_one hPP]
    exact ent_mulb bP' (ent_bmul bP hz2)
  · have hcO := cOf_sub_one hσ hν hbν hbν' hcl
    let x : GL (Fin (r + 1)) K := ⟨cOf σ ν (P' * a * P), Q * b * Q', h1, h2⟩
    have hup := cOf_up hσ ν (P' * a * P) hz.1 hpat hν
    have hJ : ∀ u ∈ lat I (t * (t * c)), ∀ v ∈ lat I (t * (t * c)), u * v ∈ lat I (t * (t * c)) :=
      lat_sq (I.mul_mem ht (I.mul_mem ht hc))
    have hlow : ∀ i j : Fin (r + 1), (fun k : Fin (r + 1) => r - k.val) i ≤ (fun k : Fin (r + 1) => r - k.val) j →
        ((x : Matrix (Fin (r + 1)) (Fin (r + 1)) K) - 1) i j = 0 := by
      intro i j hij
      have hij' : r - i.val ≤ r - j.val := hij
      have hji : j ≤ i := by
        rw [Fin.le_iff_val_le_val]
        have := i.isLt; have := j.isLt
        omega
      rw [Matrix.sub_apply]
      rcases hji.eq_or_lt with hji | hji
      · subst hji
        rw [Matrix.one_apply_eq]
        show cOf σ ν (P' * a * P) j j - 1 = 0
        rw [hup.1 j, sub_self]
      · rw [Matrix.one_apply_ne (Fin.ne_of_gt hji)]
        show cOf σ ν (P' * a * P) i j - 0 = 0
        rw [hup.2 i j hji, sub_self]
    have hinv := (inv_sub_one (fun k : Fin (r + 1) => r - k.val) (fun i => Nat.lt_succ_of_le (Nat.sub_le r i.val)) hJ x hlow hcO).1
    have hw1 : EntIn (lat I (t * (t * c))) (Q * b * Q' - 1) := hinv
    rw [← conj_sub_one hQ'Q]
    exact ent_mulb bQ (ent_bmul bQ' hw1)

end Close

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCut
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def yT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : MatP D p :=
  CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p

def LocClsE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p,
    IntP M p (yT M δ u u' F0 what₂ γ p) ∧ InOrbP δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def PhCls : Prop :=
  ∀ (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y Y' : MatP D p), (M p).OK →
    IntP M p Y → InOrbP δ T T' p w Y → InOrbP δ T T' p w Y' → Y' ∈ kkOrb M p Y →
    phL M δ T T' p w Y' = phL M δ T T' p w Y

def PhaseProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)).Finite ∧
    PairVal.phaseAt γ w = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def VolProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite ∧
    (PairVal.vRdef D u u' F0 what₂ δ M γ : ℂ) =
      ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) *
        ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)

end Steps

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem repL_spec' {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {O : Set (MatP D p)}
    (h : IsLCls M δ T T' p w O) :
    IntP M p (repL M δ T T' p w O) ∧ InOrbP δ T T' p w (repL M δ T T' p w O) ∧ O = kkOrb M p (repL M δ T T' p w O) := by
  unfold repL; rw [dite_eq_left h]; exact h.choose_spec

theorem wtL_congr {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y Y' : MatP D p}
    (h : kkOrb M p Y = kkOrb M p Y') : wtL M δ T T' p w Y = wtL M δ T T' p w Y' := by
  unfold wtL; rw [h]

theorem hL_at {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y : MatP D p}
    (hPC : PhCls M δ) (hOK : (M p).OK) (hY : IntP M p Y) (hO : InOrbP δ T T' p w Y) :
    hL M δ T T' p w (kkOrb M p Y) = phL M δ T T' p w Y * (wtL M δ T T' p w Y : ℂ) := by
  have hcls : IsLCls M δ T T' p w (kkOrb M p Y) := ⟨Y, hY, hO, rfl⟩
  obtain ⟨-, hrO, hrE⟩ := repL_spec' hcls
  unfold hL
  rw [if_pos hcls]
  generalize repL M δ T T' p w (kkOrb M p Y) = R at hrO hrE ⊢
  have hmem : R ∈ kkOrb M p Y := by
    rw [hrE]; exact PCount.mem_kkOrb_self p R
  rw [hPC T T' p w Y R hOK hY hO hrO hmem, wtL_congr hrE.symm]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coefProd_of (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂) (hPC : PhCls M δ) (hP : PhaseProd M δ u u' F0 what₂)
    (hV : VolProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨hPf, hPe⟩ := hP γ w hγ
  obtain ⟨hVf, hVe⟩ := hV γ w hγ
  have hfac : ∀ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p) =
      phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) *
        (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) := by
    intro p
    obtain ⟨hyI, hyObP⟩ := hC γ w hγ p
    show hL M δ (D.mem u).A.T (D.mem u').A.T p w (kkOrb M p (yT M δ u u' F0 what₂ γ p)) = _
    exact hL_at hPC (hA p).1 hyI hyObP
  unfold PairVal.cAt
  rw [hPe, hVe, finprod_congr hfac, finprod_mul_distrib hPf hVf]
  ring

end Assembly

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameGlobalPatching
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def GlobSet (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) :
    Set (Submodule (𝓞 D.host.E) (VS D).V) :=
  {Λ₂ | Submodule.IsFullLattice D.host.E Λ₂ ∧
    ∀ p, lattice₂ D Zd.M p Λ₂ ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p)}

variable (u u' F0 what₂)

def FStarC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∃ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z ∧ (∀ p, φ p = LinearEquiv.refl _ _) ∧
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) ∧
    (∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ₀ ∧
      {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite) ∧
    Nonempty (frPart γ Z ≃ GlobSet Zd γ F'₂ φ φ')

def PatchC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z →
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) →
    (∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ₀ ∧
      {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite) →
    Nat.card (GlobSet Zd γ F'₂ φ φ') = ∏ᶠ p, Nat.card (locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p))

variable {u u' F0 what₂}

theorem frGlob_of (hA : FStarC Zd u u' F0 what₂) (hB : PatchC Zd u u' F0 what₂) : FrGlob Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ
  obtain ⟨F'₂, φ, φ', hF, -, hT, hC, ⟨e⟩⟩ := hA γ w hγ w' hG' hk Z hZ
  refine ⟨F'₂, φ, φ', hF, hT, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr e]
  exact hB γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT hC

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThRestrPf
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Restr2

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem thRestricted_of (hA : ∀ p, Agree δ M p) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hRel : PCount.EligRel u u' F0 what₂) :
    ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) := by
  intro γ w h
  have hZ : PCount.AtMat w (zT γ) := PCount.atMat_zT hN hrows h (hRel γ w h)

  have hpt : ptT γ = w := by
    have h0 := h
    obtain ⟨⟨hgen, -⟩, hat⟩ := h
    obtain ⟨y, hy⟩ := hN γ w hat (hRel γ w h0) hgen
    have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
        PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
    have hn : nrep γ = some hex.choose := dif_pos hex
    obtain ⟨hRep, -, hL, hU, e⟩ := hex.choose_spec
    obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
    have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
      hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
    unfold ptT
    rw [hn]
    exact hw.symm
  have hfin := PCount.tupZ_restr hA u u' hZ
    ((LocModel.good_cofinite δ M hA ∅).mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (fun x => LocModel.LM.iotaIntegral_almost_all D x)
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine (hfin.union hall).subset fun p hp => ?_
  by_contra hq
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hq
  obtain ⟨htup, hg⟩ := hq
  have hg' : Good δ M w p := hg
  apply hp
  show thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ)) = _
  rw [hpt]
  have hmem : CntLocal.ZZP (M := M) δ u u' p (zT γ) * LsDatumB.sgnP p ∈ x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [← htup]
    exact ⟨1, 1, one_intLow p, one_intUp p, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  obtain ⟨l, ρ, hl, hρ, he⟩ := hmem
  have hZZ : CntLocal.ZZP (M := M) δ u u' p (zT γ) =
      l * modMat δ (D.mem u).A.T (D.mem u').A.T p w * ρ * LsDatumB.sgnP p := by
    rw [← he, Matrix.mul_assoc, permSign_mul_self₂, Matrix.mul_one]
  have e2 : CntLocal.ZZP (M := M) δ u u' p (zT γ) + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := by
    rw [hZZ, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, loU_corner p _ ⟨hl.1, hl.2.1⟩ ⟨hρ.1, hρ.2.1⟩,
      corner_sgn]
  unfold thL
  apply clsOf_triv
  have e3 : (CntLocal.ZZP (M := M) δ u u' p (zT γ) + Matrix.of fun a b =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ (D.mem u).A.T (D.mem u').A.T p w else 0) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := e2
  rw [e3]
  refine isGL_mul _ (isGL_mul _ (isGL_mul _ (isGL_of_det_one _ hl.2.2 (det_loU ⟨hl.1, hl.2.1⟩))
    (shift_isGL _ _ w p (hA p) hg')) (isGL_of_det_one _ hρ.2.2 (det_upU ⟨hρ.1, hρ.2.1⟩))) (isGL_sgn p)

end Restr2

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

theorem thRestricted_holds_of {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hN : Formalism.L2.SG.PairVal.NormRepExists D u u' F0 what₂)
    (hRel : PCount.EligRel u u' F0 what₂) :
    Formalism.L2.SG.LsDatumB.ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) :=
  LocUnramB.thRestricted_of hA hrows hN hRel

end Formalism.L2.SG.Pf
end
end

