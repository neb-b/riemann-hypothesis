module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0109
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountAtHolds
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbR_stable {p : PlF D} (Z0 : MP p) :
    ∀ Z ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0, ∀ l ρ, Formalism.MainNotions.S.TieN.IntLow (M p) l → Formalism.MainNotions.S.TieN.IntUp (M p) ρ →
      l * Z * ρ ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0 := by
  rintro Z ⟨l', ρ', hl', hρ', rfl⟩ l ρ hl hρ
  refine ⟨l * l', ρ' * ρ, Formalism.L2.SG.Pf.LocOrbCut.intLow_mul (M p) hl hl', Formalism.L2.SG.Pf.LocOrbCut.intUp_mul (M p) hρ' hρ, ?_⟩
  simp only [Matrix.mul_assoc]

theorem countAt_holds (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) := by
  have hA := hE.1 p
  have hL := hE.2.2.2.2.2.2.2.1
  have hU := hE.2.2.2.2.2.2.2.2.1
  have heq := hE.2.2.2.2.2.2.2.2.2
  obtain ⟨a, ha⟩ := Formalism.L2.SG.Pf.PCount.modPt_full (δ := δ) (D.mem u).A.T (D.mem u').A.T p hA.2.1 w
  obtain ⟨πa, hD, hker⟩ := blockRetr_holds M a
  have hB := baseAt_holds M δ u u' w p hE.1 a ha
  have hInt := int_zzp M δ u u' F0 what₂ γ w F' L U hE p
  have hgW : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
      Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
        Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [gU_smul, XP_eq_ZZP M δ u u' F0 hA w F' L U hL hU heq]
    rfl
  obtain ⟨hfin, hwt⟩ := Formalism.L2.SG.Pf.Coef.wtL_count M δ hA.1 ha hInt
  have hcard := card_cellRel M a πa hker (gU M δ u u' w hA L U hL hU a hB)
  rw [hgW] at hcard
  set Z0 : MP p := Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p +
    Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w with hZ0
  have hcos := Formalism.L2.SG.Pf.Coef.cellCos (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0) (orbR_stable M Z0)
  refine countAt_of_parts M δ u u' w hA L U hL hU a hB πa hD _ ?_ ?_
  · rw [hcard, ← hcos, hwt]
  · rw [Nat.card_ne_zero]
    refine ⟨⟨Quotient.mk _ (CountAb.toCell a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
      (gU M δ u u' w hA L U hL hU a hB) hD 1)⟩, ?_⟩
    have hcl := (Formalism.L2.SG.Pf.Coef.cellCos_finite_iff (M p) a (Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) Z0)
      (orbR_stable M Z0)).1 hfin
    have hrange := fC_range M a πa hker (gU M δ u u' w hA L U hL hU a hB)
    rw [hgW] at hrange
    rw [← hrange] at hcl
    have hinj : Function.Injective (Set.rangeFactorization (fC M a πa hker (gU M δ u u' w hA L U hL hU a hB))) :=
      fun x y h => fC_inj M a πa hker _ (congrArg Subtype.val h)
    exact @Finite.of_injective _ _ hcl.to_subtype _ hinj

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OrbitStabilizerIndexHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAsm

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolAct Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbitAction_holds : Formalism.L2.SG.Pf.ZsVolOrb.OrbActE M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  have hL : IsLoUni L := hH.2.2.2.2.2.2.2.1
  have hLd : IsUnit L.det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL]; exact isUnit_one
  set C := CZ M δ u u' (ZhatL (lf D F0) F') L with hC
  set S := (PairVal.stabAut D u u' F0 what₂ γ F' L).subgroupOf C with hS

  have hdat : ∀ g : C, ∃ (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V)
      (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)),
      ((g : GLR D) : MatR D) = L⁻¹ * (a' : MatR D) * L ∧ LiftData u u' F0 what₂ γ F' a' b ν m F₂ := by
    intro g
    have hg := (Formalism.L2.SG.Pf.ZsVolGrp.mem_CZ M δ u u' _ L hLd g).1 g.2
    obtain ⟨a', ha, hlo, b, hb, hZ, hsh⟩ := (Formalism.L2.SG.Pf.ZsVolShape.mem_stZSet_iff M δ u u' hH.1 _ L g).1 hg
    obtain ⟨ν, m, F₂, hd⟩ := Formalism.L2.SG.Pf.TupActB.moveCZ_holds M δ u u' F0 what₂ γ w F' L U hH a' b hlo hb hZ hsh
    exact ⟨a', b, ν, m, F₂, ha, hd⟩
  choose A Bm Nu Mu F2 hAL hD using hdat
  set Z := ZhatL (lf D F0) F' with hZdef
  let cls : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) → Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :=
    fun F => {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧ CntLocal.NilradicalFlagMoved F0 γ.lam F F''}
  have hmem : ∀ g : C, cls (F2 g) ∈ PairVal.orbT D u u' F0 what₂ γ Z := fun g =>
    ⟨F2 g, (hD g).2.2.2.2.2.2.2.2.1, (hD g).2.2.2.2.2.2.2.2.2.1, rfl⟩
  let ψ : C → PairVal.orbT D u u' F0 what₂ γ Z := fun g => ⟨cls (F2 g), hmem g⟩
  have hcls : ∀ F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E),
      F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z →
      (cls F₁ = cls F₂ ↔ CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂) := by
    intro F₁ F₂ h₂
    constructor
    · intro h
      have : F₂ ∈ cls F₂ := ⟨h₂, Formalism.L2.SG.Pf.TupOrb.n0rel_refl' γ.lam F₂⟩
      rw [← h] at this
      exact this.2
    · intro h
      ext F''
      constructor
      · rintro ⟨hE, h1⟩
        exact ⟨hE, Formalism.L2.SG.Pf.TupOrb.n0rel_trans (Formalism.L2.SG.Pf.TupOrb.n0rel_symm h) h1⟩
      · rintro ⟨hE, h2⟩
        exact ⟨hE, Formalism.L2.SG.Pf.TupOrb.n0rel_trans h h2⟩
  have hψ : ∀ g₁ g₂ : C, ψ g₁ = ψ g₂ ↔ g₁⁻¹ * g₂ ∈ S := by
    intro g₁ g₂
    rw [Subtype.ext_iff, hS, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show cls (F2 g₁) = cls (F2 g₂) ↔ _
    rw [hcls _ _ (hD g₂).2.2.2.2.2.2.2.2.1]
    exact fibreIndex_holds M δ u u' F0 what₂ γ w F' L U hH (A g₁) (Bm g₁) (Nu g₁) (Mu g₁) (F2 g₁) (A g₂) (Bm g₂)
      (Nu g₂) (Mu g₂) (F2 g₂) g₁ g₂ (hAL g₁) (hAL g₂) (hD g₁) (hD g₂)
  let φ : C ⧸ S → PairVal.orbT D u u' F0 what₂ γ Z :=
    Quotient.lift ψ (fun a b h => (hψ a b).2 (QuotientGroup.leftRel_apply.1 h))
  have hinj : Function.Injective φ := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    intro h
    exact QuotientGroup.eq.2 ((hψ a b).1 h)
  have hsurj : Function.Surjective φ := by
    rintro ⟨O, hO⟩
    obtain ⟨F'', hEZ, hRep, rfl⟩ := hO
    obtain ⟨a', b, ν, m, hd⟩ := Formalism.L2.SG.Pf.TupActB.ontoCZ_holds M δ u u' F0 what₂ γ w F' L U hH F'' hEZ hRep
    have ha'd : IsUnit (a' : MatR D).det := by rw [Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hd.1]; exact isUnit_one
    have hdet : IsUnit (L⁻¹ * (a' : MatR D) * L).det := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact ((Matrix.isUnit_nonsing_inv_det L hLd).mul ha'd).mul hLd
    let y : GLR D := Matrix.nonsingInvUnit (L⁻¹ * (a' : MatR D) * L) hdet
    have hy : ((y : GLR D) : MatR D) = L⁻¹ * (a' : MatR D) * L := rfl
    have hyC : y ∈ C := (Formalism.L2.SG.Pf.ZsVolGrp.mem_CZ M δ u u' _ L hLd y).2
      ((Formalism.L2.SG.Pf.ZsVolShape.mem_stZSet_iff M δ u u' hH.1 _ L y).2 ⟨a', hy, hd.1, b, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩)
    refine ⟨((⟨y, hyC⟩ : C) : C ⧸ S), ?_⟩
    show ψ ⟨y, hyC⟩ = _
    apply Subtype.ext
    show cls (F2 ⟨y, hyC⟩) = cls F''
    rw [hcls _ _ hEZ]
    refine (fibreIndex_holds M δ u u' F0 what₂ γ w F' L U hH (A ⟨y, hyC⟩) (Bm ⟨y, hyC⟩) (Nu ⟨y, hyC⟩) (Mu ⟨y, hyC⟩)
      (F2 ⟨y, hyC⟩) a' b ν m F'' y y (hAL ⟨y, hyC⟩) hy (hD ⟨y, hyC⟩) hd).2 ?_
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  refine ⟨C ⧸ S, inferInstance, ((1 : C) : C ⧸ S), MulAction.stabilizer_quotient S, ⟨?_⟩⟩
  exact (Set.equivOfEq (MulAction.orbit_eq_univ C ((1 : C) : C ⧸ S))).trans
    ((Equiv.Set.univ _).trans (Equiv.ofBijective φ ⟨hinj, hsurj⟩))

theorem orbitStabilizerIndex_holds : OrbStabE M δ u u' F0 what₂ (CZ M δ u u') :=
  Formalism.L2.SG.Pf.ZsVolOrb.orbStabE_of_act M δ u u' F0 what₂ (orbitAction_holds M δ u u' F0 what₂)

theorem volIdxProd_of_prodE (hP : PrimeHyp D u (Tu D u')) (h : ProdE M δ u u' F0 what₂ (CZ M δ u u')) :
    Formalism.L2.SG.Pf.Coef.VolIdxProd M δ u u' F0 what₂ :=
  volIdxProd_of M δ u u' F0 what₂ hP (CZ M δ u u') (orbitStabilizerIndex_holds M δ u u' F0 what₂) h

end Formalism.L2.SG.Pf.ZsVolAsm

end
end

