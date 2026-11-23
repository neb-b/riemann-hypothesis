module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0066
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0065
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0067

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormals
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.NGCut.NormalInvariants.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NmlInvG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS),
        (∃ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν) →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ →
        ∃ (J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m m' : D.host.E)
          (κ : NuC D → D.host.E × D.host.E),
          J ≠ 0 ∧ J' ≠ 0 ∧ m ≠ 0 ∧ m' ≠ 0 ∧
          (∀ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν →
            (κ ν).1 ∈ J ∧ (κ ν).1 * star (κ ν).1 = m ∧ (κ ν).2 ∈ J' ∧ (κ ν).2 * star (κ ν).2 = m') ∧
          (∀ ν₁ ν₂, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν₁ →
            PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν₂ → κ ν₁ = κ ν₂ → ν₁ = ν₂) ∧
          |((Algebra.norm ℚ m : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2 ∧
          |((Algebra.norm ℚ m' : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2

theorem stepNormalsG_of (hA : NmlInvG) (hB : NormCount) (hO : StepNormOneG) : StepNormalsG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨o₀, p₀, hO2⟩ := hO Cg cb Cw cT CT C0
  refine ⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng => ?_⟩
  intro cl γ S hS
  have hrd := rd_one_le D
  have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
  have hstand := hc.2.1
  show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
    (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
    NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6
  have eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
      ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ) ^ 6 =
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 := by
    have hR := rd_cancel D
    calc _ = (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
          (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6) *
          ((((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6) := by
          ring
      _ = _ := by rw [hR, one_mul]
  rw [hv, ngPt_eq, eR]
  have hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.1
  have hT2 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.2.1
  rcases S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg (pow_nonneg (by nlinarith) _) ?_
    rw [show PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 3) ^ 2 by ring]
    exact sq_nonneg _
  have hocc : ∃ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) cl γ ν := ⟨ν0, hS ν0 hν0⟩
  have hIsPt : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ := ⟨cl, ν0, hS ν0 hν0⟩
  have hNG0 := (hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u hc
    νL νB ng γ hIsPt).1
  obtain ⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩ :=
    hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u hc νL νB ng cl γ hocc hNG0
  have hNG := hNG0
  rw [ngPt_eq] at hNG
  have hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ := by
    have hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := one_le_pow₀ (one_le_pow₀ hrd)
    have hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := lt_of_lt_of_le one_pos hX
    rw [inv_mul_eq_div, le_div_iff₀ hpos, one_mul] at hNG
    linarith

  let T1 := S.image (fun ν => (κ ν).1)
  let T2 := S.image (fun ν => (κ ν).2)
  have hcard : S.card ≤ T1.card * T2.card := by
    calc S.card = (S.image κ).card :=
          (Finset.card_image_of_injOn fun a ha b hb h => hinj a b (hS a ha) (hS b hb) h).symm
      _ ≤ (T1 ×ˢ T2).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)
      _ = T1.card * T2.card := Finset.card_product _ _
  have hB1 := hB D J m hJ hm T1 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)
  have hB2 := hB D J' m' hJ' hm' T2 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)
  have hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)
    exact_mod_cast this
  have hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J' ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)
    exact_mod_cast this
  generalize PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ = P at hN hN' hP1 ⊢
  generalize ((Tu D u : ℕ) : ℝ) = T at hN hN' hT1 hT2 ⊢
  generalize ((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp
  generalize ((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'
  generalize |((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN
  generalize |((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'
  have hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  have hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
    have h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  calc (S.card : ℝ) ≤ (T1.card : ℝ) * T2.card := by exact_mod_cast hcard
    _ ≤ _ := count_bound D.R.f T T P _ _ hT1 hT2 hP1 hc1 hc2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end Formalism.L2.SG.NGCut.NormalInvariants.Gen
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NotDvdDiff
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem not_dvd_diff (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  have hp := D.host.g_prime i
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv
  have hvq : v.asIdeal ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq D.host.F hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem diff_avoid (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ t ∈ differentIdeal ℤ (𝓞 D.host.F), algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∉ P.asIdeal := by
  have hPp := P.isPrime
  let v : HeightOneSpectrum (𝓞 D.host.F) :=
    ⟨P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.IsPrime.comap _, by
      intro hb
      apply P.ne_bot
      have hg0 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
        rw [Ideal.mem_comap, map_natCast]; exact hP
      rw [hb, Ideal.mem_bot] at hg0
      exfalso
      have : (gS D : ℕ) ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact this (by exact_mod_cast hg0)⟩
  have hgi : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    have hg : ((gS D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      show _ ∈ P.asIdeal.comap _
      rw [Ideal.mem_comap, map_natCast]; exact hP
    unfold Lat.gS at hg
    rw [Nat.cast_mul] at hg
    rcases v.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hgi
  have hnd := not_dvd_diff v i hi
  by_contra hc
  push Not at hc
  exact hnd (Ideal.dvd_iff_le.2 fun t ht => hc t ht)

end Formalism.L2.SG.Pf.FibD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftM
section
namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def RFinMax : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → {m : Ideal M.R | m.IsMaximal}.Finite

theorem srLift_of_finMax (h : RFinMax) : SRLift := by
  intro F _ _ _ E _ _ _ _ M hOK n A K hA hK
  exact Formalism.L2.SG.Pf.SRL.srLift_of_finite (h M hOK) A K hA hK

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLatSk
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def hgt (q : FreeE w) : ℕ := q.1.2.val - q.1.1.val

theorem qbar_prop (q : FreeE w) :
    pinv w q.1.2 < pinv w q.1.1 ∧ blkOf w.1 (pinv w q.1.2).val = blkOf w.1 (pinv w q.1.1).val :=
  ⟨(pinv_lt_iff w q.1.1 q.1.2 q.2.2).1 q.2.1, by rw [blkOf_pinv, blkOf_pinv]; exact q.2.2.symm⟩

def qbar (q : FreeE w) : FreeE w := ⟨(pinv w q.1.2, pinv w q.1.1), qbar_prop w q⟩

def selfP (q : FreeE w) : Prop := qbar w q = q

def upperM (q : FreeE w) : Prop := (qbar w q).1.1 < q.1.1

def hpr (q : FreeE w) : ℕ := 2 * hgt w q + if upperM w q then 1 else 0

def sgq (q : FreeE w) : D.host.E := (-1) ^ (D.R.rS - q.1.1.val) * (-1) ^ (D.R.rS - q.1.2.val)

def Xmat (y : FreeE w → D.host.E) : MatR D := fun a c =>
  if a = c then 1 else if h : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val then y ⟨(a, c), h⟩ else 0

def trunc (y : FreeE w → D.host.E) (n : ℕ) : FreeE w → D.host.E := fun q => if hgt w q < n then y q else 0

def cf (y : FreeE w → D.host.E) (q : FreeE w) : D.host.E := ((Xmat w (trunc w y (hgt w q)))⁻¹) q.1.1 q.1.2


variable (D) in
def mOdd : ℕ := (gS D + 1) / 2

def τA (q : FreeE w) (y : FreeE w → D.host.E) : D.host.E :=
  if selfP w q then (mOdd D : D.host.E) * cf w y q
  else if upperM w q then sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q))
  else 0


variable (D) in
def sLat (h : ℕ) (s : D.host.E) (_hs : D.conjF s = s) : AddSubgroup D.host.E where
  carrier := {z | z ∈ ddPow D h ∧ z + s * D.conjF z ∈ qdPow D h}
  zero_mem' := by
    refine ⟨FractionalIdeal.zero_mem _, ?_⟩
    simp only [map_zero, mul_zero, add_zero]; exact FractionalIdeal.zero_mem _
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha1 hb1, ?_⟩
    rw [map_add (f := _), show a + b + s * (D.conjF a + D.conjF b) = (a + s * D.conjF a) + (b + s * D.conjF b) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha2 hb2
  neg_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha1, ?_⟩
    rw [map_neg, show -a + s * -D.conjF a = -(a + s * D.conjF a) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha2

theorem sgq_conj (q : FreeE w) : D.conjF (sgq w q) = sgq w q := by
  simp [sgq, map_pow, map_neg, map_one]

def Iq (q : FreeE w) : FI D := if selfP w q ∨ ¬ upperM w q then ddPow D (hgt w q) else qdPow D (hgt w q)

def Λq (q : FreeE w) : AddSubgroup D.host.E :=
  if selfP w q then sLat D (hgt w q) (sgq w q) (sgq_conj w q)
  else ((Iq w q : FI D) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup


variable (D) in
def TwistC : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → Odd (gS D) → ∀ (w : Point D.host.E (D.R.rS + 1)) (y : FreeE w → D.host.E),
      CondX w (Xmat w y) ↔ ∀ q, y q - τA w q y ∈ Λq w q



end Formalism.L2.SG.Pf.StabIntLat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UniInjective
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

section Uni

variable {P : Type} [Fintype P] (ht : P → ℕ)

def IsUni (A : (P → ℂ) →ₗ[ℂ] (P → ℂ)) : Prop :=
  ∀ (x x' : P → ℂ) p, (∀ q, ht q < ht p → x q = x' q) → A x p - x p = A x' p - x' p

theorem uni_injective {A : (P → ℂ) →ₗ[ℂ] (P → ℂ)} (hA : IsUni ht A) : Function.Injective A := by
  intro x x' hxx
  have key : ∀ n, ∀ q, ht q < n → x q = x' q := by
    intro n
    induction n with
    | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
    | succ n ih =>
      intro q hq
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
      · exact ih q h
      · have h1 := hA x x' q (fun r hr => ih r (h ▸ hr))
        rw [hxx] at h1
        exact sub_right_injective h1
  funext q
  exact key (ht q + 1) q (Nat.lt_succ_self _)

theorem uni_inv {A : (P → ℂ) →ₗ[ℂ] (P → ℂ)} (hA : IsUni ht A) :
    ∃ B : (P → ℂ) →ₗ[ℂ] (P → ℂ), (∀ x, A (B x) = x) ∧ (∀ x, B (A x) = x) ∧ IsUni ht B := by
  have hinj := uni_injective ht hA
  let e := LinearEquiv.ofInjectiveEndo A hinj
  refine ⟨e.symm.toLinearMap, fun x => e.apply_symm_apply x, fun x => e.symm_apply_apply x, ?_⟩
  have low : ∀ (x x' : P → ℂ) n, (∀ q, ht q < n → A x q = A x' q) → ∀ q, ht q < n → x q = x' q := by
    intro x x' n
    induction n with
    | zero => intro _ q hq; exact absurd hq (Nat.not_lt_zero _)
    | succ n ih =>
      intro hAx q hq
      have ih' := ih (fun r hr => hAx r (Nat.lt_succ_of_lt hr))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
      · exact ih' q h
      · have h1 := hA x x' q (fun r hr => ih' r (h ▸ hr))
        rw [hAx q hq] at h1
        exact sub_right_injective h1
  intro y y' p hy
  have e1 : A (e.symm y) = y := e.apply_symm_apply y
  have e2 : A (e.symm y') = y' := e.apply_symm_apply y'
  have hx : ∀ q, ht q < ht p → e.symm y q = e.symm y' q :=
    low _ _ (ht p) (fun q hq => by rw [e1, e2]; exact hy q hq)
  have h1 := hA (e.symm y) (e.symm y') p hx
  rw [e1, e2] at h1
  show e.symm y p - y p = e.symm y' p - y' p
  linear_combination -h1

end Uni

end Formalism.L2.SG.NGCut.StabilizerCovolume
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitaryNormalVectorCount
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {s | s ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) ∧ s F.fl.z - F.fl.z ∈ Xsp F}

def NmlPtDC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t1 t2 : TauC Y u u', Gt t1 ≠ 0 → Gt t2 ≠ 0 → ptPN t1 = γ → ptPN t2 = γ →
          (Y.tO u u').rowOf t1 = (Y.tO u u').rowOf t2 →
          ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s'

def UnitaryNormalVectorCount : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          RelC Y u u' t0 t1 → RelC Y u u' t0 t2 → t1.G = t0.G → t2.G = t0.G →
          (∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s') →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem nmlSep_of (hP : NmlPtDC) (hG : UnitaryNormalVectorCount) : NmlSep := by
  intro Cg cb Cw cT CT C0
  obtain ⟨A1, B1, h1⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨A2, B2, h2⟩ := hG Cg cb Cw cT CT C0
  refine ⟨max A1 A2, max B1 B2, fun C' Cl hC hl D large₂ X Y u u' hctx γ hγ t0 t1 t2 g0 g1 g2 p0 p1 p2 r1 r2 ca ca' => ?_⟩
  have hdc := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hl) D large₂ X Y u u' hctx γ hγ t1 t2 g1 g2 p1 p2
    (r1.1.trans r2.1.symm)
  have e0 := gval_occ (t := t0) (hG := p0 ▸ hγ)
  have e1 := gval_occ (t := t1) (hG := p1 ▸ hγ)
  have e2 := gval_occ (t := t2) (hG := p2 ▸ hγ)
  have hG1 : t1.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t1), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e1, e0, p1, p0]
  have hG2 : t2.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t2), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e2, e0, p2, p0]
  exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hl) D large₂ X Y u u' hctx t0 t1 t2 g0 g1 g2 r1 r2
    hG1 hG2 hdc ca ca'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

