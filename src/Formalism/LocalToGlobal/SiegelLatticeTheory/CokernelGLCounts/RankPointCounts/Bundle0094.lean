module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0093
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0089
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0088
public import Formalism.LocalRingCardinality.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ConjSecondFactor
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

theorem loUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) : IsLoUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

theorem upUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntUp (M p) l) : IsUpUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

section
variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)

theorem conj_first_factor (x : GG p) :
    (((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).1 : GLp p) : MP p) =
      lOf δ M p L U * ((x.1 : GLp p) : MP p) * lOf δ M p L⁻¹ U⁻¹ := by
  simp only [g0, Prod.fst_mul, Prod.fst_inv, Units.val_mul, Units.inv_mk]

theorem conj_second_factor (x : GG p) :
    ((((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).2).unop : GLp p) : MP p) =
      ρOf δ M p L⁻¹ U⁻¹ * ((x.2.unop : GLp p) : MP p) * ρOf δ M p L U := by
  simp only [g0, Prod.snd_mul, Prod.snd_inv, MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op,
    Units.val_mul, Units.inv_mk]
  rw [Matrix.mul_assoc]

theorem cShape (w : Point D.host.E (D.R.rS + 1)) : CShapeAt M δ u u' w hA L U hL hU := by
  have hLL : lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U = 1 := lp_inv M δ hA L U hL hU
  have hLL' : lOf δ M p L U * lOf δ M p L⁻¹ U⁻¹ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hLL
  have hUU : ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹ = 1 := up_inv M δ hA L U hL hU
  have hUU' : ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p L U = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hUU
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  set Y := Y0 M δ u u' w p
  have key : ∀ a b : MP p, (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * (a * Y * b) * Up := by
    intro a b
    calc (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * a * (Lpi * Lp) * Y * (Up * Upi) * b * Up := by
          simp only [Matrix.mul_assoc]
      _ = Lp * (a * Y * b) * Up := by rw [hLL, hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  ext x
  rw [mem_cj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨_, _, hy3⟩ := y.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) _
      rw [conj_first_factor]; exact hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) _
      rw [conj_second_factor]; exact hy2
    · show _ * XP M δ u u' w L U * _ = XP M δ u u' w L U
      rw [conj_first_factor, conj_second_factor]
      show (Lp * _ * Lpi) * (Lp * Y * Up) * (Upi * _ * Up) = Lp * Y * Up
      rw [key]
      exact congrArg (fun z => Lp * z * Up) hy3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h1' : Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1 : GLp p) : MP p) * Lpi) := by
      have := h1; rw [show Formalism.MainNotions.S.TieN.IntLow (M p) _ = _ from rfl, conj_first_factor] at this; exact this
    have h2' : Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((x.2.unop : GLp p) : MP p) * Up) := by
      have := h2; rw [show Formalism.MainNotions.S.TieN.IntUp (M p) _ = _ from rfl, conj_second_factor] at this; exact this
    have h3' : (Lp * ((x.1 : GLp p) : MP p) * Lpi) * (Lp * Y * Up) * (Upi * ((x.2.unop : GLp p) : MP p) * Up) =
        Lp * Y * Up := by
      have := h3
      change _ * XP M δ u u' w L U * _ = XP M δ u u' w L U at this
      rw [conj_first_factor, conj_second_factor] at this
      exact this
    rw [key] at h3'
    have hst : ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p) = Y := by
      have := congrArg (fun z => Lpi * z * Upi) h3'
      calc ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)
          = (Lpi * Lp) * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * (Up * Upi) := by
            rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
        _ = Lpi * (Lp * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * Up) * Upi := by
            simp only [Matrix.mul_assoc]
        _ = Lpi * (Lp * Y * Up) * Upi := this
        _ = Y := by
            calc Lpi * (Lp * Y * Up) * Upi = (Lpi * Lp) * Y * (Up * Upi) := by simp only [Matrix.mul_assoc]
              _ = Y := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
    have hlo : IsLoUni ((x.1 : GLp p) : MP p) := by
      have e : ((x.1 : GLp p) : MP p) = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by
        calc ((x.1 : GLp p) : MP p) = (Lpi * Lp) * ((x.1 : GLp p) : MP p) * (Lpi * Lp) := by
              rw [hLL, Matrix.one_mul, Matrix.mul_one]
          _ = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul
        (lOf_loUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1) (loUni_of_int M h1'))
        (lOf_loUni M δ hA _ _ hL hU)
    have hup : IsUpUni ((x.2.unop : GLp p) : MP p) := by
      have e : ((x.2.unop : GLp p) : MP p) = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by
        calc ((x.2.unop : GLp p) : MP p) = (Up * Upi) * ((x.2.unop : GLp p) : MP p) * (Up * Upi) := by
              rw [hUU, Matrix.one_mul, Matrix.mul_one]
          _ = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul (ρOf_upUni M δ hA _ _ hL hU) (upUni_of_int M h2'))
        (ρOf_upUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1)
    exact ⟨⟨x, hlo, hup, hst⟩, ⟨h1', h2'⟩, rfl⟩

end

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprClose
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lprPart_holds : LprPart Zd u u' F0 what₂ :=
  LprEx.lprPart_of_iota Zd Formalism.L2.SG.Pf.iotaStep_holds

theorem fStarC_of_beta (hC : CtxP u u' F0 what₂) (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    FStarC Zd u u' F0 what₂ :=
  fStarC_of_leaves' Zd hC (lprPart_holds Zd) hRat hInt

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LmatUp
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG3

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem lmat_up {l ρ : Formalism.L2.SG.LsDatumB.MatP D p} (hl0 : ∀ a b, a < b → l a b = 0) (hl1 : ∀ a, l a a = 1)
    (hρ0 : ∀ a b, b < a → ρ a b = 0) (hρ1 : ∀ a, ρ a a = 1) :
    (∀ a b, b < a → lmat Z p g ρ l a b = 0) ∧ ∀ a, lmat Z p g ρ l a a = 1 := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · simp only [lmat, Matrix.of_apply, hρ0 a b h, hl0 b a h, map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [show ((0 : (D.s.atP p).Fp), (0 : (D.s.atP p).Fp)) = 0 from rfl, map_zero]
  · simp only [lmat, Matrix.of_apply, hl1 a, hρ1 a, map_one, Prod.fst_one, Prod.snd_one]
    rw [show ((1 : (D.s.atP p).Fp), (1 : (D.s.atP p).Fp)) = 1 from rfl, map_one]

theorem modeG (hs : (Z.M p).split = some g) (u u' : D.what₂.Word)
    (N M Z₁ Z₂ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hNU : ∀ a b, b < a → N a b = 0) (hNd : ∀ a, N a a = 1) (hMU : ∀ a b, b < a → M a b = 0)
    (hMd : ∀ a, M a a = 1)
    (hNb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c)
    (hMb : ∀ c b, c < b → ∀ x ∈ aaF D b, x * M c b ∈ aaF D c) (hrel : Nᴴ * Z₂ = Z₁ * M)
    (hcong : Cq Z p g (locU Z p N * locU Z p M - 1)) :
    ∃ l ρ, Formalism.MainNotions.S.TieN.IntLow (Z.M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (Z.M p) ρ ∧
      Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ * Formalism.L2.SG.LsDatumB.sgnP p =
        l * (Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * Formalism.L2.SG.LsDatumB.sgnP p) * ρ := by
  obtain ⟨hN1, hN0, hNO⟩ := locU_int Z p N hNU hNd hNb
  obtain ⟨hM1, hM0, hMO⟩ := locU_int Z p M hMU hMd hMb
  set Nl := locU Z p N with hNl
  set Ml := locU Z p M with hMl
  set K := (Nl.map (Z.M p).L.cj)ᵀ with hKdef
  have hK0 : ∀ a b, a < b → K a b = 0 := fun a b h => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN0 b a h, map_zero]
  have hK1 : ∀ a, K a a = 1 := fun a => by
    simp only [hKdef, Matrix.transpose_apply, Matrix.map_apply, hN1 a, map_one]
  have hKO : IntM Z p K := fun i j => PI.LocCntLat.GC.cj_mem_O _ (hNO j i)
  have hKdet : K.det = 1 := det_lower p hK0 hK1
  have hKu : IsUnit K.det := by rw [hKdet]; exact isUnit_one
  have hNdet : Nl.det = 1 := det_upper p hN0 hN1
  have hNu : IsUnit Nl.det := by rw [hNdet]; exact isUnit_one
  have hl0O : IntM Z p K⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O K hKO hKdet
  have hNiO : IntM Z p Nl⁻¹ := Formalism.L2.SG.Pf.LocOrbCut.inv_int (Z.M p).L.O Nl hNO hNdet
  have hl0low : (∀ a b, a < b → K⁻¹ a b = 0) ∧ ∀ a, K⁻¹ a a = 1 := by
    have h := Formalism.L2.SG.TermLoc.inv_unitri Kᵀ (fun a b h => by rw [Matrix.transpose_apply]; exact hK0 b a h)
      (fun a => by rw [Matrix.transpose_apply]; exact hK1 a)
    rw [← Matrix.transpose_nonsing_inv] at h
    exact ⟨fun a b hab => by have := h.1 b a hab; rwa [Matrix.transpose_apply] at this,
      fun a => by have := h.2 a; rwa [Matrix.transpose_apply] at this⟩
  have hK := key_rel Z p N M Z₁ Z₂ hrel
  have hY : Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₂ =
      K⁻¹ * Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p Z₁ * Ml := by
    rw [Matrix.mul_assoc, ← hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul]

  set Cm : Formalism.L2.SG.LsDatumB.MatP D p := Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
      g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
        (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)) else 0 with hCm
  have hZZ : ∀ X, Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p X =
      emap Z p g (Formalism.L2.SG.CntLocal.ZhatLoc Z.M Z.δ p X) - Cm := by
    intro X
    ext a b
    simp only [Formalism.L2.SG.CntLocal.ZZP, Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, emap, hCm, Matrix.sub_apply,
      Matrix.of_apply]
  obtain ⟨hL0, hL1⟩ := lmat_low Z p g hl0low.1 hl0low.2 hM0 hM1
  obtain ⟨hR0, hR1⟩ := lmat_up Z p g hl0low.1 hl0low.2 hM0 hM1
  have hcorner := corner_fix p hL0 hL1 hR0 hR1 (C := Cm) (fun a b h => by
    simp only [hCm, Matrix.of_apply]; rw [if_neg h])
  have hmain : Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₂ =
      lmat Z p g K⁻¹ Ml * Formalism.L2.SG.CntLocal.ZZP (M := Z.M) Z.δ u u' p Z₁ * lmat Z p g Ml K⁻¹ := by
    rw [hZZ, hZZ, hY, emap_mul, Matrix.mul_sub, Matrix.sub_mul, hcorner]

  have hKc : K.map (Z.M p).L.cj = Nlᵀ := by
    ext i j
    simp [hKdef, (Z.M p).L.cj_cj]
  have hA : Cq Z p g (Ml - ((K⁻¹).map (Z.M p).L.cj)ᵀ) := by
    have e1 : ((K⁻¹).map (Z.M p).L.cj)ᵀ = Nl⁻¹ := by
      rw [map_cj_inv Z p K hKu, hKc, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    have e2 : Ml - Nl⁻¹ = Nl⁻¹ * (Nl * Ml - 1) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul, Matrix.mul_one]
    rw [e1, e2]
    exact cq_mul_left Z p g hNiO hcong
  have hB : Cq Z p g (K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ) := by
    have e1 : Ml * Nl - 1 = Nl⁻¹ * (Nl * Ml - 1) * Nl := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Nl hNu, Matrix.one_mul,
        Matrix.mul_one, Matrix.nonsing_inv_mul Nl hNu]
    have h1 : Cq Z p g (Ml * Nl - 1) := by
      rw [e1]; exact cq_mul_right Z p g (cq_mul_left Z p g hNiO hcong) hNO
    have e2 : ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ = K * (Ml.map (Z.M p).L.cj)ᵀ - 1 := by
      have m1 : (Ml * Nl - 1).map (Z.M p).L.cj = (Ml * Nl).map (Z.M p).L.cj - 1 := by
        ext i j
        rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
        congr 1
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      rw [m1, map_cj_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hKdef]
    have e3 : K⁻¹ - (Ml.map (Z.M p).L.cj)ᵀ = -(K⁻¹ * ((Ml * Nl - 1).map (Z.M p).L.cj)ᵀ) := by
      rw [e2, Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKu, Matrix.one_mul, Matrix.mul_one,
        neg_sub]
    rw [e3]
    exact cq_neg Z p g (cq_mul_left Z p g hl0O (cq_transpose Z p g (cq_map_cj Z p g h1)))
  have hLint : Formalism.MainNotions.S.TieN.IntLow (Z.M p) (lmat Z p g K⁻¹ Ml) := by
    refine ⟨hL1, hL0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hB a b
    exact lmat_mem_R Z p g hs (hl0O a b) (hMO b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  have hRint : Formalism.MainNotions.S.TieN.IntUp (Z.M p) (lmat Z p g Ml K⁻¹) := by
    refine ⟨hR1, hR0, fun a b => ?_⟩
    obtain ⟨o, ho, he⟩ := hA a b
    exact lmat_mem_R Z p g hs (hMO a b) (hl0O b a) ⟨o, ho, by
      rw [← he]; simp [Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply]⟩
  refine ⟨lmat Z p g K⁻¹ Ml, Formalism.L2.SG.LsDatumB.sgnP p * lmat Z p g Ml K⁻¹ * Formalism.L2.SG.LsDatumB.sgnP p,
    hLint, sgn_conj_intUp Z p hRint, ?_⟩
  rw [hmain]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), permSign_mul_self₂, Matrix.one_mul]

end ModeG3

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXFrameVol
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem three_dvd_cubic (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by

  obtain ⟨k, hk | hk | hk⟩ : ∃ k, r = 3 * k ∨ r = 3 * k + 1 ∨ r = 3 * k + 2 := ⟨r / 3, by omega⟩
  · subst hk
    exact ⟨(3 * k + 1) * (6 * k + 1) * (4 * k + 1), by ring⟩
  · subst hk
    exact ⟨(3 * k + 2) * (2 * k + 1) * (12 * k + 7), by ring⟩
  · subst hk
    exact ⟨(k + 1) * (8 * (3 * k + 2) ^ 2 + 10 * (3 * k + 2) + 3), by ring⟩

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem frameVolAt_of (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) (hP : ProdConv X u u' ψ) :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq := by
  have hMS := Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds X u u' ψ hψ hstd hP
  have hZZ : 0 < (locOf X u u' ψ).volZZ := hP.2.2.2.2.2.2.1
  unfold Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt
  show ((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) / (locOf X u u' ψ).volZZ = _
  unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.LemmaMS at hMS
  rw [hMS, mul_div_assoc, div_self hZZ.ne', mul_one]
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  have he : (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) =
      ((D.R.f * Formalism.L2.SG.Pf.Carrier.EnergyConst.e1 D : ℕ) : ℝ) := by
    unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.e1
    obtain ⟨c, hc⟩ := three_dvd_cubic D.R.rS
    rw [mul_assoc, hc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    push_cast
    ring
  have hg : (X.B.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by rw [X.g_eq]; simp [Formalism.MainNotions.S.Lat.gS]
  rw [hv, he, Real.rpow_natCast, hg, mul_assoc D.R.f]

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewHoldsGen
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem level_congr_mod_sq (D : D7) (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD Formalism.MainNotions.S.Lat.gS D ^ 2] := by
  have h : Formalism.MainNotions.S.Lat.gS D ^ 2 ∣ D.modT := by unfold Formalism.MainNotions.S.Lat.gS; exact D.gg_dvd_modT
  exact (D.T_modEq_of_dvd u h).trans (D.T_modEq_of_dvd u' h).symm

theorem prodConvNew_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConvNew X u u' ψ := by
  have hg : ∀ v, TypAt X v → 0 < gAt X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos X u u' ψ hψ hs (level_congr_mod_sq D u u') hg
  refine prodConvNew_gen X u u' ψ hb hψ hs hloc fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos X hg v⟩
  by_cases hv : TypAt X v
  · exact pp_pos_typ_gen X hb ψ hψ hs u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord X u u' ψ hψ hs hv l

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCong
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem one_mem_R {p : PlF D} (a b : Fin (D.R.rS + 1)) :
    (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (M p).R := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (M p).R.one_mem
  · exact (M p).R.zero_mem

theorem mem_R_of_sub_one {p : PlF D} (hA : Agree δ M p) {X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (h : EntIn (latS (D.s.atP p) (ellP p)) (X - 1)) (a b : Fin (D.R.rS + 1)) : X a b ∈ (M p).R := by
  have e : X a b = (X - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b := by
    rw [Matrix.sub_apply]; ring
  rw [e]
  exact (M p).R.add_mem (latS_R hA (h a b)) (one_mem_R M a b)

theorem cong_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ c : (D.s.atP p).Fp, c ≠ 0 ∧ c ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ k : ProdE.StP M δ u u' w p,
      EntIn (latS (D.s.atP p) c) ((k.1.1 : ProdE.MP p) - 1) → EntIn (latS (D.s.atP p) c) ((k.1.2.unop : ProdE.MP p) - 1) →
        k ∈ ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w hA L U hL hU := by
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by
    rw [← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hUU : Upi * Up = 1 := by
    rw [← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  have hLp := ProdE.lOf_loUni M δ hA L U hL hU
  have hLpi := ProdE.lOf_loUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  have hUp := ProdE.ρOf_upUni M δ hA L U hL hU
  have hUpi := ProdE.ρOf_upUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  refine ⟨ellP p * (s1 * s2 * s3 * s4),
    mul_ne_zero (ellP_ne p) (mul_ne_zero (mul_ne_zero (mul_ne_zero hs10 hs20) hs30) hs40),
    Subring.mul_mem _ (ellP_mem p) (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O),
    fun k h1 h2 => ?_⟩
  obtain ⟨hk1, hk2, -⟩ := k.2
  have hO12 : s1 * s2 * s3 * s4 ∈ 𝒪[(D.s.atP p).Fp] :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O
  have h1l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.1 : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h1
  have h2l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.2.unop : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h2
  have h1c : EntIn (latS (D.s.atP p) (ellP p)) (Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi) :=
    entIn_sandwich hs1 hs2 (entIn_latS_of_eq (t := s3 * s4) (by ring) (Subring.mul_mem _ hs3O hs4O) h1)
  have h2c : EntIn (latS (D.s.atP p) (ellP p)) (Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up) :=
    entIn_sandwich hs4 hs3 (entIn_latS_of_eq (t := s1 * s2) (by ring) (Subring.mul_mem _ hs1O hs2O) h2)
  have e1 : Lp * (k.1.1 : ProdE.MP p) * Lpi - 1 = Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLL]
  have e2 : Upi * (k.1.2.unop : ProdE.MP p) * Up - 1 = Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
  have hc1 := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLp hk1) hLpi
  have hc2 := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUpi hk2) hUp
  refine Subgroup.mem_inf.2 ⟨⟨⟨fun a => (hk1 a a).2 rfl, fun a b h => (hk1 a b).1 h,
    mem_R_of_sub_one M δ hA h1l⟩, ⟨fun a => (hk2 a a).2 rfl, fun a b h => (hk2 a b).1 h, mem_R_of_sub_one M δ hA h2l⟩⟩,
    ⟨⟨fun a => (hc1 a a).2 rfl, fun a b h => (hc1 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e1]; exact h1c)⟩,
    ⟨fun a => (hc2 a a).2 rfl, fun a b h => (hc2 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e2]; exact h2c)⟩⟩⟩

end Cong

end Formalism.L2.SG.Pf.ProdEApprox
end
end

