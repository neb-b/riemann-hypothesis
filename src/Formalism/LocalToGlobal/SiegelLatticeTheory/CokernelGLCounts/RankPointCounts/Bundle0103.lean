module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0102
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameShapeHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem conj_ddPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hLG := Formalism.L2.SG.Pf.StabIntSh.locGlob (D := D)
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (hLG _ hne _).1 fun p => Formalism.L2.SG.Pf.StabIntSh.locMem_conj δ M hA p hk ((hLG _ hne _).2 hx p)

theorem conj_qdPow (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) {k : ℕ} (hk : k ≤ D.R.rS) {x : D.host.E} (hx : x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k) :
    D.conjF x ∈ Formalism.L2.SG.Pf.StabIntSh.qdPow D k := by
  unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at *
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨D.conjF z, conj_ddPow δ M hA hk hz, ?_⟩
  rw [map_mul]
  congr 1
  simp

theorem bt_sgn (uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (j i : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.StabIntSh.bt D (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * uu' * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS) j i = uu' j i := by
  unfold Formalism.L2.SG.Pf.StabIntSh.bt Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : ((-1 : D.host.E) ^ (D.R.rS - j.val)) * (-1) ^ (D.R.rS - j.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have h2 : ((-1 : D.host.E) ^ (D.R.rS - i.val)) * (-1) ^ (D.R.rS - i.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (uu' j i * (-1) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val)) * h1 + uu' j i * h2

theorem star_conjF (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  exact Formalism.BasicNotions.Examples₂.star_eq_conj D.host x

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem frameShape_holds : Formalism.L2.SG.Pf.ZsVolIn.FrameShapeP M δ u u' F0 what₂ := by
  intro γ w F' L U hH s hs uu uu' huu huu' hfr hfr'
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨⟨⟨hLift', _, hFOK⟩, _⟩, hAdm, _, _, _⟩ := hN
  obtain ⟨_, ⟨_, _, hLift, hConv⟩, hXF⟩ := hR.1 γ.lam γ.mem
  have hsΛ : ∀ v ∈ γ.lam, s v ∈ γ.lam := fun v hv => by
    have h := hs.1.1.2
    rw [← h]
    exact Submodule.mem_map_of_mem hv
  have hadm : ∀ b, ModG (VS D) γ.lam (Lat.gS D) (F'.fl.fvec b - (lf D F0).fl.fvec b) := by
    intro b
    have h := hAdm.2.2 b
    convert h using 3
    simp [frameAct, Matrix.one_apply]
    rfl
  intro i j hji
  have hk : ((i : ℕ) - (j : ℕ)) ≤ D.R.rS := by have := i.2; omega
  have h1 := frame_entry (lf D F0) γ.lam hXF hLift.1 s hsΛ uu huu hfr j i hji
  have h2 := frame_entry F' γ.lam hFOK.2 hLift'.1 s hsΛ uu' huu' hfr' j i hji
  have h3 := cong_glob (lf D F0) F' γ.lam hConv hFOK.1 hXF hFOK.2 hLift.1 hLift'.1 hadm s hsΛ uu uu' huu huu' hfr hfr' j i hji
  rw [Matrix.conjTranspose_apply, bt_sgn, star_conjF]
  refine ⟨conj_ddPow δ M hA hk h1, h2, ?_⟩
  rw [← map_sub]
  exact conj_qdPow δ M hA hk h3

end Formalism.L2.SG.Pf.ZsVolLat

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GoodPlaces
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good3

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

set_option maxHeartbeats 1000000 in
theorem good_places (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ S : Finset (PlF D), (∀ p, p ∉ S → ProdE.AP M δ u u' w p = ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
          ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set X : Finset D.host.E := Finset.univ.image (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) with hX
  have hev := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA X
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, ?_⟩
  have key : ∀ p, p ∉ hfin.toFinset → (M p).split = none ∧
      (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
      ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
      (∀ t ∈ X, (D.s.atP p).ιE t ∈ (D.s.atP p).O) ∧ (∀ t ∈ X, t ≠ 0 → (D.s.atP p).ιE t⁻¹ ∈ (D.s.atP p).O) := by
    intro p hp
    have hp' : ¬ ¬ _ := fun h => hp (hfin.mem_toFinset.2 h)
    obtain ⟨h1, h2, h3, h4⟩ := not_not.1 hp'
    refine ⟨h1, h2, h3, fun t ht => ?_, fun t ht ht0 => ?_⟩
    · by_cases ht0 : t = 0
      · rw [ht0, map_zero]; exact (D.s.atP p).O.zero_mem
      · have := (h4 t ht 0 (by simpa using ht0)).1
        simpa using this
    · have := (h4 t ht 0 (by simpa using ht0)).2
      simpa using this
  have hpvX : ∀ a : Fin (D.R.rS + 1), Formalism.L2.SG.Pf.pv w.1 a ∈ X := fun a =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) (Finset.mem_univ a)))))
  have hLX : ∀ i j, L i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) (Finset.mem_univ (i, j))))))
  have hUX : ∀ i j, U i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) (Finset.mem_univ (i, j)))))
  have hLiX : ∀ i j, L⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j))))
  have hUiX : ∀ i j, U⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j)))
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  refine ⟨fun p hp => ?_, fun p hp g hg => ?_⟩
  · obtain ⟨hs, hδ, huP, hXi, -⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have i1 := lOf_ρOf_int M δ (hA p) hs hδ huP L U (fun i j => hXi _ (hLX i j)) (fun i j => hXi _ (hUX i j))
    have i2 := lOf_ρOf_int M δ (hA p) hs hδ huP L⁻¹ U⁻¹ (fun i j => hXi _ (hLiX i j)) (fun i j => hXi _ (hUiX i j))
    have hLp := ProdE.lOf_loUni M δ (hA p) L U hL hU
    have hLpi := ProdE.lOf_loUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have hUp := ProdE.ρOf_upUni M δ (hA p) L U hL hU
    have hUpi := ProdE.ρOf_upUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have iLp : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L U) :=
      ⟨fun a => (hLp a a).2 rfl, fun a b h => (hLp a b).1 h, fun a b => (hR _).2 (i1.1 a b)⟩
    have iLpi : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hLpi a a).2 rfl, fun a b h => (hLpi a b).1 h, fun a b => (hR _).2 (i2.1 a b)⟩
    have iUp : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L U) :=
      ⟨fun a => (hUp a a).2 rfl, fun a b h => (hUp a b).1 h, fun a b => (hR _).2 (i1.2 a b)⟩
    have iUpi : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hUpi a a).2 rfl, fun a b h => (hUpi a b).1 h, fun a b => (hR _).2 (i2.2 a b)⟩
    have hLL := ProdE.lp_inv M δ (hA p) L U hL hU
    have hUU := ProdE.up_inv M δ (hA p) L U hL hU
    ext k
    constructor
    · rintro ⟨hk1, hk2⟩
      exact ⟨ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLp hk1) iLpi,
        ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUpi hk2) iUp⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨?_, ?_⟩
      · have e : ((k.1.1 : ProdE.GLp p) : ProdE.MP p) = lOf δ M p L⁻¹ U⁻¹ *
            (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) * lOf δ M p L U := by
          rw [show lOf δ M p L⁻¹ U⁻¹ * (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) *
              lOf δ M p L U = (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) *
                (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) by simp only [Matrix.mul_assoc], hLL, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLpi hk1) iLp
      · have e : ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) = ρOf δ M p L U *
            (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) * ρOf δ M p L⁻¹ U⁻¹ := by
          rw [show ρOf δ M p L U * (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) *
              ρOf δ M p L⁻¹ U⁻¹ = (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) *
                (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUp hk2) iUpi
  · obtain ⟨hs, hδ, huP, hXi, hXinv⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have hb := bOf_int w g hg (fun a => ⟨hXi _ (hpvX a), hXinv _ (hpvX a) (Formalism.L2.SG.Pf.pv_ne' w a)⟩)
    have i0 := lOf_ρOf_int M δ (hA p) hs hδ huP _ _ hg hb
    obtain ⟨hπl, hπρ, -⟩ := (ProdE.πP M δ u u' w (hA p) g).2
    exact ⟨⟨fun a => (hπl a a).2 rfl, fun a b h => (hπl a b).1 h, fun a b => (hR _).2 (i0.1 a b)⟩,
      ⟨fun a => (hπρ a a).2 rfl, fun a b h => (hπρ a b).1 h, fun a b => (hR _).2 (i0.2 a b)⟩⟩

end Good3

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauKPIff
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

theorem tauU_inj : Function.Injective (tauU p) := fun x y h => by
  rw [← tauU_tauU p x, ← tauU_tauU p y, h]

theorem tau_KP_iff (x : GG p) : tau p x ∈ KP M p ↔ x ∈ KP M p :=
  ⟨fun h => by have := tau_mem_KP M p h; rwa [tau_tau] at this, fun h => tau_mem_KP M p h⟩

section Parts

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a)

def gU : UP p := tauU p ⟨g0 M δ hA L U hL hU, conjugator_mem_unipotent M δ hA L U hL hU⟩ * hB.choose

theorem gU_smul : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
    phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' w L U) := by
  rw [XP_eq M δ u u' w hA L U hL hU, phi_smul p δ _ _ w (conjugator_mem_unipotent M δ hA L U hL hU), hB.choose_spec.1]
  show ((tau p (g0 M δ hA L U hL hU) * (hB.choose : GG p)) : GG p) • a.mat = _
  rw [mul_smul]

theorem mem_H_iff (x : UP p) :
    (x : GG p) ∈ KP M p ⊓ StabX p (XP M δ u u' w L U) ↔
      tauU p x ∈ CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB) := by
  show (x : GG p) ∈ KP M p ∧ (x : GG p) • XP M δ u u' (p := p) w L U = XP M δ u u' (p := p) w L U ↔
    tau p x ∈ KP M p ∧ (tauU p x : UP p) • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) =
      (gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat
  rw [tau_KP_iff]
  apply and_congr Iff.rfl
  have e : ∀ y : UP p, (y • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) : MP p) =
      (y : GG p) • (((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p)) := fun y => rfl
  have e2 : ((gU M δ u u' w hA L U hL hU a hB : UP p) • (a.mat : MP p) : MP p) =
      ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p) := rfl
  rw [e2, gU_smul]
  constructor
  · intro h
    show tau p (x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U)
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

end Parts

end Formalism.L2.SG.Pf.CountAt
end
end

