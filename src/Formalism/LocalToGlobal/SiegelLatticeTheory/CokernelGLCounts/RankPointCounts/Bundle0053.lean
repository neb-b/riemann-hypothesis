module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairingOmegaPrimeZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.P2MemZ2OfMemZ2
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def OccT (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u') : Prop :=
  t ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').vec t ≠ 0 ∧ clsOf Y u u' t = c ∧ ptPN t = γ

def yT (t : TauC Y u u') : (VS D).V := yv (X.Fu u) t.frame.fl

def yT' (t : TauC Y u u') : (VS D).V := t.lin.symm (yv t.frame.fl (X.Fu u))

def coefA (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT Y u u' t) (yT Y u u' t0) / brS (VS D) (yT Y u u' t0) (yT Y u u' t0)

def coefA' (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT' Y u u' t) (yT' Y u u' t0) / brS (VS D) (yT' Y u u' t0) (yT' Y u u' t0)

theorem occ_iff (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν ↔ ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    exact ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨t, h1, h2, h3, h4, h5⟩

end Defs

section Rel

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def RelC (t0 t : TauC Y u u') : Prop :=
  (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ (Y.tO u u').s0 t0 t = 1

end Rel

def NmlLine : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t : TauC Y u u', Gt t0 ≠ 0 → Gt t ≠ 0 → ptPN t0 = γ → ptPN t = γ → RelC Y u u' t0 t →
          coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1 ∧ coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1

def NmlInt : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 : TauC Y u u', Gt t0 ≠ 0 → ptPN t0 = γ →
        ∃ J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, J ≠ 0 ∧ J' ≠ 0 ∧
          (∀ t : TauC Y u u', Gt t ≠ 0 → ptPN t = γ → RelC Y u u' t0 t →
            coefA Y u u' t0 t ∈ J ∧ coefA' Y u u' t0 t ∈ J') ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2 ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u' : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2

def NmlSep : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          ptPN t0 = γ → ptPN t1 = γ → ptPN t2 = γ → RelC Y u u' t0 t1 → RelC Y u u' t0 t2 →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem relC_of_occ {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (hTie : ConcTie X Y)
    {c : Set (TauC Y u u')} {γ : PN.Pts D.host.E D.R.rS} {t0 t : TauC Y u u'}
    (h0 : OccT Y u u' c γ t0) (h : OccT Y u u' c γ t) : RelC Y u u' t0 t := by
  have hrefl := (CorankRelation.corankOne_equivalence_holds D X Y u u' hTie).1 t h.1
  have ht : t ∈ clsOf Y u u' t := ⟨h.1, rfl, hrefl⟩
  rw [h.2.2.1, ← h0.2.2.1] at ht
  exact ⟨ht.2.1, ht.2.2⟩

theorem nmlInv_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : NormalInvariants.NmlInv := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u u' hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iff Y u u' νL νB ng c γ ν0).1 hν0
  have hTie : ConcTie X Y := hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u' hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u' := fun ν =>
    if h : ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν →
      OccT Y u u' c γ (pick ν) ∧ nmlOf Y u u' (pick ν) = ν := by
    intro ν hν
    have h := (occ_iff Y u u' νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u' t0 (pick ν), coefA' Y u u' t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occ hTie ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u' hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occ hTie ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u' hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occ hTie ht0 hp1) (relC_of_occ hTie ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabApprox
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem locTarget (Zd : LocDat D) (u u' : D.what₂.Word) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    {Z₁ L₁ U₁ A₀ B₀ : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀) {l ρ : MatP D p}
    (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
      l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) :
    LocTarget Zd p w L₁ U₁ A₀ B₀ := by
  rcases hM : (Zd.M p).split with _ | g
  · exact target_L Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h
  · exact target_G Zd u u' p hM w hL₁ hU₁ hZ hA₀ hB₀ hl hρ h

theorem cf_int (Zd : LocDat D) (p : PlF D) (hδ1 : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp])
    (hδ2 : (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) (hu1 : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O)
    (hu2 : (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) :
    (∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O) ∧
      ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O := by
  have e1 : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  have e2 : (D.s.atP p).ιE (((uP p : ℚ) : D.host.E)⁻¹) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((D.s.atP p).ιF ((uP p : ℚ) : D.host.F))⁻¹) := by
    rw [← map_inv₀ (D.s.atP p).ιF, ← (D.s.atP p).compat, map_inv₀ (algebraMap D.host.F D.host.E),
      map_ratCast (algebraMap D.host.F D.host.E)]
  have hy : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p) ∈ (D.s.atP p).O := by
    unfold yP
    rw [map_mul, ← e1]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ1) hu1
  have hyi : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP Zd p)⁻¹ ∈ (D.s.atP p).O := by
    unfold yP
    rw [mul_inv, map_mul, ← e2]
    exact (D.s.atP p).O.mul_mem (LocModel.LM.algebraMap_mem_O p hδ2) hu2
  exact ⟨fun a => by unfold cf; rw [map_pow]; exact pow_mem hyi _,
    fun a => by unfold cfi; rw [map_pow]; exact pow_mem hy _⟩

theorem stabApprox (Zd : LocDat D) (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.TupGlob.StabApprox Zd u u' := by
  intro w Z₁ A₀ B₀ hAt hA₀ hB₀ hloc
  obtain ⟨L₁, U₁, hL₁u, hU₁u, e₁⟩ := hAt
  have hL₁ : IsLo L₁ := isLo_of_uni hL₁u
  have hU₁ : IsUp U₁ := isUp_of_uni hU₁u
  rw [zhatOM_eq] at e₁
  choose l ρ hl hρ hlr using hloc
  choose T c hc0 hT using fun p => locTarget Zd u u' p w hL₁ hU₁ e₁ hA₀ hB₀ (hl p) (hρ p) (hlr p)
  have hE : ∀ᶠ p in Filter.cofinite, ∀ (k : Fin 8) (i j : Fin (D.R.rS + 1)),
      (D.s.atP p).ιE ((![A₀, B₀, L₁, L₁⁻¹, U₁, U₁⁻¹, Matrix.of fun i _ => pv w.1 i,
        Matrix.of fun i _ => (pv w.1 i)⁻¹] : Fin 8 → PairVal.MatR D) k i j) ∈ (D.s.atP p).O :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      LocModel.LM.iotaIntegral_almost_all D _
  have hG := (LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅).and hE
  have hfin := Filter.eventually_cofinite.1 hG
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat D.s.atP hfin.toFinset (fun p => T p ij.1 ij.2) c (fun p _ => hc0 p)
  let X' : PairVal.MatR D := Matrix.of fun i j => if Free (fσ w) i j then t (i, j) else (1 : PairVal.MatR D) i j
  have hX'1 : ∀ i j, ¬ Free (fσ w) i j → X' i j = (1 : PairVal.MatR D) i j := fun i j h => by
    simp only [X', Matrix.of_apply, if_neg h]
  have hX'2 : ∀ i j, Free (fσ w) i j → X' i j = t (i, j) := fun i j h => by
    simp only [X', Matrix.of_apply, if_pos h]
  have hX' : IsLo X' :=
    ⟨fun a => by rw [hX'1 a a (fun h => lt_irrefl a h.1), Matrix.one_apply_eq],
      fun a b hab => by rw [hX'1 a b (fun h => absurd h.1 (not_lt.2 hab.le)), Matrix.one_apply_ne hab.ne]⟩
  have hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0 := fun i j hij => by
    have hf : ¬ Free (fσ w) i j := fun h => absurd h.2 (not_lt.2 hij.le)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rw [hX'1 i j hf, Matrix.one_apply_ne hne]
  obtain ⟨hgX, hgY, hst⟩ := glob_stab w hL₁ hU₁ e₁ hX' hpat
  refine ⟨gX L₁ X', gY w U₁ X', hgX, hgY, hst, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · exact hT p X' hX' hpat fun i j hf => by rw [hX'2 i j hf]; exact ht1 (i, j) p hp
  · have hgp : _ ∧ _ := not_not.1 ((Set.Finite.mem_toFinset hfin).not.1 hp)
    obtain ⟨⟨hM, ⟨hδ1, hδ2⟩, ⟨hu1, hu2⟩, -⟩, hEp⟩ := hgp
    obtain ⟨hcf, hcfi⟩ := cf_int Zd p hδ1 hδ2 hu1 hu2
    have hXi : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O := by
      intro i j
      by_cases hf : Free (fσ w) i j
      · rw [hX'2 i j hf]; exact ht2 (i, j) p hp
      · rw [hX'1 i j hf, Matrix.one_apply]
        split_ifs
        · rw [map_one]; exact Subring.one_mem _
        · rw [map_zero]; exact Subring.zero_mem _
    exact good_at Zd p hM w hL₁ hU₁ hA₀ hB₀ hX' hpat hcf hcfi
      (fun i j => hEp 0 i j) (fun i j => hEp 1 i j) (fun i j => hEp 2 i j) (fun i j => hEp 3 i j)
      (fun i j => hEp 4 i j) (fun i j => hEp 5 i j) (fun a => hEp 6 a a) (fun a => hEp 7 a a) hXi

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ q, Agree δ M q) (p : PlF D)

include δ M hA


omit M hA in
abbrev cc : (D.s.atP p).Ep :=
  algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)

theorem cc_unit : IsUnit (cc δ p) := LocFacts.isUnit_localConstant p ⟨δ, M, hA⟩

theorem frFac_mul (a : Fin (D.R.rS + 1)) : frFac δ p a * cc δ p ^ (D.R.rS - a.val) = 1 := by
  unfold frFac
  exact Ring.inverse_mul_cancel _ ((cc_unit δ M hA p).pow _)

theorem inv_frFac (a : Fin (D.R.rS + 1)) : Ring.inverse (frFac δ p a) = cc δ p ^ (D.R.rS - a.val) := by
  unfold frFac
  exact Ring.inverse_inverse ((cc_unit δ M hA p).pow _)

theorem cj_cc : (D.s.atP p).cj (cc δ p) = cc δ p := by
  have hE : (D.s.atP p).ιE (uP p : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((uP p : ℚ) : (D.s.atP p).Fp) := by
    rw [← map_ratCast (algebraMap D.host.F D.host.E), (D.s.atP p).compat, map_ratCast]
  simp only [cc, map_mul, hE, AlgEquiv.commutes]

theorem cj_frFac (a : Fin (D.R.rS + 1)) : (D.s.atP p).cj (frFac δ p a) = frFac δ p a := by
  have h := frFac_mul δ M hA p a
  have h' : (D.s.atP p).cj (frFac δ p a) * cc δ p ^ (D.R.rS - a.val) = 1 := by
    rw [← cj_cc δ M hA p, ← map_pow, ← map_mul, h, map_one]
  calc (D.s.atP p).cj (frFac δ p a)
      = (D.s.atP p).cj (frFac δ p a) * (cc δ p ^ (D.R.rS - a.val) * frFac δ p a) := by
        rw [mul_comm (cc δ p ^ _), h, mul_one]
    _ = frFac δ p a := by rw [← mul_assoc, h', one_mul]

theorem locMem_iff {k : ℕ} (hk : k ≤ D.R.rS) (x : D.host.E) :
    LocMem D p (ddPow D k) x ↔ cc δ p ^ k * (D.s.atP p).ιE x ∈ (D.s.atP p).O := by
  have hD := locDiffC_holds D ⟨δ, M, hA⟩ p ⟨D.R.rS - k, by omega⟩
  have e1 : (-((D.R.rS : ℤ) - ((D.R.rS - k : ℕ) : ℤ))) = -(k : ℤ) := by
    rw [Nat.cast_sub hk]; ring
  dsimp only at hD
  rw [e1] at hD
  have hg := frFac_mul δ M hA p ⟨D.R.rS - k, by omega⟩
  simp only [Nat.sub_sub_self hk] at hg
  have hO : (M p).L.O = (D.s.atP p).O := (hA p).2.2.2.1
  unfold LocMem ddPow
  rw [← SetLike.mem_coe, ← LocFacts.lf_span_coe_of_eq hO, hD, LocFacts.lf_span_coe_of_eq hO, SetLike.mem_coe,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨o, ho⟩
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_left_comm, mul_comm (cc δ p ^ k), hg, mul_one]
    exact o.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul]
    show cc δ p ^ k * (D.s.atP p).ιE x * frFac δ p ⟨D.R.rS - k, by omega⟩ = (D.s.atP p).ιE x
    rw [mul_comm (cc δ p ^ k), mul_assoc, mul_comm (cc δ p ^ k), hg, mul_one]

theorem locMem_sub (I : FI D) {x y : D.host.E} (hx : LocMem D p I x) (hy : LocMem D p I y) :
    LocMem D p I (x - y) := by
  unfold LocMem at *
  rw [map_sub]
  exact sub_mem hx hy

theorem locMem_conj {k : ℕ} (hk : k ≤ D.R.rS) {y : D.host.E} (h : LocMem D p (ddPow D k) y) :
    LocMem D p (ddPow D k) (D.conjF y) := by
  rw [locMem_iff δ M hA p hk] at *
  rw [← (D.s.atP p).cj_ιE, ← cj_cc δ M hA p, ← map_pow, ← map_mul]
  exact LocFacts.lf_cj_mem p _ h

theorem untyped (hs : (M p).split = none) :
    Loc.resChar p ≠ D.host.g 0 ∧ Loc.resChar p ≠ D.host.g 1 := by
  have h6 := (hA p).2.2.2.2.2
  have hsD : (D.s.atP p).split = none := by
    cases hD : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [hs, hD] at h6; exact h6.elim
  have := (D.s_split p).not.1 (by rw [hsD]; simp)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
  exact this

theorem unitAt_untyped (hs : (M p).split = none) : (uP p : ℚ) = 1 / (gS D : ℚ) := by
  obtain ⟨h0, h1⟩ := untyped δ M hA p hs
  unfold uP gpart
  rw [if_neg h0, if_neg h1]
  simp

theorem gS_mul_uP (hs : (M p).split = none) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * (D.s.atP p).ιE (uP p : D.host.E) = 1 := by
  rw [← map_mul, unitAt_untyped δ M hA p hs]
  have hg : (gS D : ℚ) ≠ 0 := by
    unfold gS; push_cast
    exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)
  have : ((gS D : ℕ) : D.host.E) * (((1 / (gS D : ℚ)) : ℚ) : D.host.E) = 1 := by
    rw [show ((gS D : ℕ) : D.host.E) = (((gS D : ℚ)) : D.host.E) by push_cast; rfl, ← Rat.cast_mul,
      mul_one_div_cancel hg, Rat.cast_one]
  rw [this, map_one]

omit δ M hA in
theorem gS_mem_qq : ((gS D : ℕ) : 𝓞 D.host.E) ∈ qq D :=
  Ideal.mem_span_singleton_self _

theorem locMem_qd_of (hs : (M p).split = none) (k : ℕ) {x : D.host.E} (h : LocMem D p (ddPow D k) x) :
    LocMem D p (qdPow D k) x := by
  unfold LocMem at *
  set ι := (D.s.atP p).ιE
  have key : ∀ y ∈ Submodule.span (D.s.atP p).O (ι '' (ddPow D k : Set D.host.E)),
      ι ((gS D : ℕ) : D.host.E) * y ∈ Submodule.span (D.s.atP p).O (ι '' (qdPow D k : Set D.host.E)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      rw [← map_mul]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      unfold qdPow
      have hq : ((gS D : ℕ) : D.host.E) ∈ (qq D : FI D) := by
        rw [FractionalIdeal.mem_coeIdeal]
        exact ⟨_, gS_mem_qq, map_natCast _ _⟩
      exact FractionalIdeal.mul_mem_mul hq hz
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul o y _ hy =>
      rw [Subring.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subring.smul_def]
      exact Submodule.smul_mem _ o hy
  have hu : ι (uP p : D.host.E) ∈ (D.s.atP p).O := LocFacts.unitPart_mem₂ p
  have e : ι x = ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x) := by
    rw [← mul_assoc, mul_comm (ι (uP p : D.host.E)), gS_mul_uP δ M hA p hs, one_mul]
  rw [e, show ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x) =
    (⟨_, hu⟩ : (D.s.atP p).O) • (ι ((gS D : ℕ) : D.host.E) * ι x) by rw [Subring.smul_def, smul_eq_mul]]
  exact Submodule.smul_mem _ _ (key _ h)

theorem lL_low (a : MatR D) (i j : Fin (D.R.rS + 1)) (hji : j < i) :
    StabShape.lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a i j =
      cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j) := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  simp only [StabShape.lL, Matrix.of_apply, hcj, RingHom.coe_coe]
  rw [cj_frFac δ M hA p i, cj_frFac δ M hA p j, inv_frFac δ M hA p j]
  have hi := frFac_mul δ M hA p i
  have hji' : j.val < i.val := hji
  have hi' : i.val < D.R.rS + 1 := i.isLt
  have e : D.R.rS - j.val = (D.R.rS - i.val) + (i.val - j.val) := by omega
  rw [e, pow_add]
  linear_combination (cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j)) * hi

theorem ρL_up (b : MatR D) (i j : Fin (D.R.rS + 1)) (hij : i < j) :
    StabShape.ρL (D.s.atP p).ιE (frFac δ p) b i j = cc δ p ^ (j.val - i.val) * (D.s.atP p).ιE (bt D b i j) := by
  simp only [StabShape.ρL, Matrix.of_apply, bt]
  rw [inv_frFac δ M hA p i]
  have hj := frFac_mul δ M hA p j
  have hij' : i.val < j.val := hij
  have hj' : j.val < D.R.rS + 1 := j.isLt
  have e : D.R.rS - i.val = (D.R.rS - j.val) + (j.val - i.val) := by omega
  rw [show cc δ p ^ (D.R.rS - i.val) = cc δ p ^ (D.R.rS - j.val) * cc δ p ^ (j.val - i.val) by rw [← pow_add, ← e]]
  linear_combination (cc δ p ^ (j.val - i.val) *
    (D.s.atP p).ιE ((-1) ^ (D.R.rS - i.val) * b i j * (-1) ^ (D.R.rS - j.val))) * hj

theorem R_none (hs : (M p).split = none) : (M p).R = (D.s.atP p).O := by
  unfold Loc.Model.R
  rw [hs]
  exact (hA p).2.2.2.1

theorem intLow_iff_L (hs : (M p).split = none) {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i → cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j) ∈ (D.s.atP p).O := by
  have hR := R_none δ M hA p hs
  have hl : StabShape.lOf δ M p a b =
      StabShape.lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a := by
    simp only [StabShape.lOf, hs]
  constructor
  · intro h i j hji
    have := h.2.2 i j
    rw [hR, hl, lL_low δ M hA p a i j hji] at this
    exact this
  · intro h
    refine ⟨StabShape.lOf_diag δ M (hA p) a b ha hb, fun i j hij => ?_, fun i j => ?_⟩
    · rw [hl]; simp [StabShape.lL, (ha i j).1 hij]
    · rw [hR]
      rcases lt_trichotomy j i with hji | rfl | hij
      · rw [hl, lL_low δ M hA p a i j hji]; exact h i j hji
      · rw [StabShape.lOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hl]; simp [StabShape.lL, (ha i j).1 hij]

theorem intUp_iff_L (hs : (M p).split = none) {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i → cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (bt D b j i) ∈ (D.s.atP p).O := by
  have hR := R_none δ M hA p hs
  have hr : StabShape.ρOf δ M p a b = StabShape.ρL (D.s.atP p).ιE (frFac δ p) b := by
    simp only [StabShape.ρOf, hs]
  constructor
  · intro h i j hji
    have := h.2.2 j i
    rw [hR, hr, ρL_up δ M hA p b j i hji] at this
    exact this
  · intro h
    refine ⟨StabShape.ρOf_diag δ M (hA p) a b ha hb, fun i j hji => ?_, fun i j => ?_⟩
    · rw [hr]; simp [StabShape.ρL, (hb i j).1 hji]
    · rw [hR]
      rcases lt_trichotomy i j with hij | rfl | hji
      · rw [hr, ρL_up δ M hA p b i j hij]; exact h j i hij
      · rw [StabShape.ρOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hr]; simp [StabShape.ρL, (hb i j).1 hji]


omit δ M hA p in
theorem locShapeL : LocShapeL D := by
  intro δ M p hA hs a b ha hb
  rw [intLow_iff_L δ M hA p hs ha hb, intUp_iff_L δ M hA p hs ha hb]
  constructor
  · rintro ⟨h1, h2⟩ i j hji
    have hk : i.val - j.val ≤ D.R.rS := by have := i.isLt; omega
    have m1 := (locMem_iff δ M hA p hk (a i j)).2 (h1 i j hji)
    have m2 := (locMem_iff δ M hA p hk (bt D b j i)).2 (h2 i j hji)
    exact ⟨m1, m2, locMem_qd_of δ M hA p hs _ (locMem_sub δ M hA p _ m1 (locMem_conj δ M hA p hk m2))⟩
  · intro h
    exact ⟨fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).1,
      fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).2.1⟩

end Formalism.L2.SG.Pf.StabIntSh
end
end

