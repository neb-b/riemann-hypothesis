module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0099
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0092
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CongAt
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem cong_at {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hz' : F'.fl.z ∈ Λ) (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E,
      (t : D.host.E) * (uu j i - uu' j i) = ((Lat.gS D : ℕ) : D.host.E) * o := by
  have hP := P.isPrime
  set g : 𝓞 D.host.E := ((Lat.gS D : ℕ) : 𝓞 D.host.E) with hg
  set M := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {g} • Λ) with hM
  have hg0 : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by
    have h2 : (Lat.gS D : ℕ) ≠ 0 := by
      unfold Lat.gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast h2

  have hgs : ∀ x : (VS D).V, x ∈ Ideal.span {g} • Λ ↔ ∃ l ∈ Λ, g • l = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  have hd : ∀ c, F'.fl.fvec c - F.fl.fvec c ∈ M := fun c => hadm c P hgP
  have hsd : s (F'.fl.fvec i - F.fl.fvec i) ∈ M := by
    obtain ⟨t, ht, htd⟩ := (mem_locP P.asIdeal _ _).1 (hd i)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (mem_locP P.asIdeal _ _).2 ⟨t, ht, ?_⟩
    rw [← smul_O, ← hlg, smul_O]
    exact (hgs _).2 ⟨s l, hs l hl, rfl⟩
  have hud : ∀ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) ∈ M := by
    intro c
    obtain ⟨t1, ht1, o, ho⟩ := int_at F' Λ hc' hz' s hs uu' huu' hfr' P hgP c i
    obtain ⟨t2, ht2, htd⟩ := (mem_locP P.asIdeal _ _).1 (hd c)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (mem_locP P.asIdeal _ _).2 ⟨t1 * t2, fun h => (hP.mem_or_mem h).elim ht1 ht2, ?_⟩
    have e : (t1 * t2) • (uu' c i • (F'.fl.fvec c - F.fl.fvec c)) = o • (t2 • (F'.fl.fvec c - F.fl.fvec c)) := by
      rw [← algebraMap_smul D.host.E (t1 * t2), ← algebraMap_smul D.host.E o, ← algebraMap_smul D.host.E t2, smul_smul,
        smul_smul]
      have ho' : algebraMap (𝓞 D.host.E) D.host.E t1 * uu' c i = algebraMap (𝓞 D.host.E) D.host.E o := ho
      rw [map_mul, mul_right_comm, ho']
    rw [e, ← hlg]
    exact (hgs _).2 ⟨o • l, Λ.smul_mem o hl, smul_comm g o l⟩

  set y : Fin D.R.rS → D.host.E := fun a => uu' (Fin.castSucc a) i - uu (Fin.castSucc a) i with hy
  have hlast : uu' (Fin.last _) i - uu (Fin.last _) i = 0 := by
    by_cases h : i = Fin.last _
    · subst h
      rw [(huu' _ _).2 rfl, (huu _ _).2 rfl, sub_self]
    · have hlt : i < Fin.last _ := lt_of_le_of_ne (Fin.le_last i) h
      rw [(huu' _ _).1 hlt, (huu _ _).1 hlt, sub_self]
  have hw : ∑ a, y a • F.fl.e a = s (F'.fl.fvec i - F.fl.fvec i) - ∑ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) := by
    rw [map_sub, hfr i, hfr' i]
    simp only [smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ c, (uu' c i - uu c i) • F.fl.fvec c = ∑ a, y a • F.fl.e a := by
      rw [sum_fvec]
      simp only [hy, hlast, zero_smul, add_zero]
    rw [← h2]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  have hwM : ∑ a, y a • F.fl.e a ∈ M := by
    rw [hw]
    exact M.sub_mem hsd (M.sum_mem fun c _ => hud c)
  obtain ⟨t, ht, htw⟩ := (mem_locP P.asIdeal _ _).1 hwM
  obtain ⟨l, hl, hlg⟩ := (hgs _).1 htw

  have hl_eq : l = ∑ a, (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a)) • F.fl.e a := by
    have h1 : ((Lat.gS D : ℕ) : D.host.E) • l = t • ∑ a, y a • F.fl.e a := by
      rw [← hlg, ← algebraMap_smul D.host.E g]
      rfl
    have h2 := congrArg (fun v => ((Lat.gS D : ℕ) : D.host.E)⁻¹ • v) h1
    simp only [smul_smul, inv_mul_cancel₀ hg0, one_smul] at h2
    rw [h2, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t, smul_smul, smul_smul, mul_assoc]
  have hlX : l ∈ XLam Λ F := by
    refine Submodule.mem_inf.2 ⟨hl, ?_⟩
    show l ∈ F.fl.X
    rw [hl_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hloc : l ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
    rw [← conv_at F Λ hc P hgP]
    exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hlX⟩
  obtain ⟨t', ht', ht'l⟩ := (mem_locP P.asIdeal _ _).1 hloc
  have hv2 : t' • l = ∑ a, ((t' : D.host.E) * (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a))) • F.fl.e a := by
    rw [hl_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t', smul_smul]
  have hjr : (j : ℕ) < D.R.rS := lt_of_lt_of_le hji (Nat.lt_succ_iff.1 i.2)
  obtain ⟨o, ho⟩ := coef_spanO F.fl ht'l _ hv2 ⟨j, hjr⟩
  refine ⟨t' * t, fun h => (hP.mem_or_mem h).elim ht' ht, -o, ?_⟩
  have hyj : y ⟨j, hjr⟩ = uu' j i - uu j i := rfl
  rw [hyj] at ho
  have hgi : ((Lat.gS D : ℕ) : D.host.E) * ((Lat.gS D : ℕ) : D.host.E)⁻¹ = 1 := mul_inv_cancel₀ hg0
  push_cast
  linear_combination ((Lat.gS D : ℕ) : D.host.E) * ho + ((t' : D.host.E) * (t : D.host.E) * (uu' j i - uu j i)) * hgi

end Formalism.L2.SG.Pf.ZsVolLat

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountBaseT
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Corner

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLo_of_uni {L : Matrix (Fin n) (Fin n) R} (h : IsLoUni L) : IsLo L :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

theorem isUp_of_uni {U : Matrix (Fin n) (Fin n) R} (h : IsUpUni U) : IsUp U :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h b a).1 hab⟩

theorem uni_of_isLo {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) : IsLoUni L :=
  fun a b => ⟨fun hab => h.2 a b hab, fun e => by subst e; exact h.1 a⟩

theorem uni_of_isUp {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) : IsUpUni U :=
  fun a b => ⟨fun hab => h.2 b a hab, fun e => by subst e; exact h.1 a⟩

end Corner

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def glOfLo {L : MP p} (h : IsLo L) : GLp p :=
  ⟨L, L⁻¹, Matrix.mul_nonsing_inv L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1])⟩

def glOfUp {U : MP p} (h : IsUp U) : GLp p :=
  ⟨U, U⁻¹, Matrix.mul_nonsing_inv U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1])⟩

theorem glue_one_one {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ} :
    glue e (1 : Matrix (Fin n) (Fin n) Fp) 1 = 1 :=
  mat_eq e (by rw [glue_map_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [glue_map_snd, Matrix.map_one _ (map_zero _) (map_one _)])

theorem corner_fix {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ}
    {l ρ Δ : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hl : IsLoUni l) (hρ : IsUpUni ρ) (k1 k2 : Fp)
    (h1 : Δ.map (p1 e) = k1 • Ecorner n) (h2 : Δ.map (p2 e) = k2 • Ecorner n) : l * Δ * ρ = Δ := by
  apply mat_eq e
  · rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]
  · rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]


set_option maxHeartbeats 4000000 in
theorem baseAt_typed (hA : ∀ p, Agree δ M p) (g : Loc.SplitG (M p).L) (hM : (M p).split = some g)
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    BaseAt M δ u u' w p a := by
  have hAg := (hA p).2.2.2.2.2
  rw [hM] at hAg
  obtain ⟨sg, hR, hge, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hs] at hAg; exact hAg.elim
    · rw [hs] at hAg; exact ⟨sg, rfl, hAg.1, hAg.2⟩
  let Zd : LocDat D := ⟨δ, M, hA⟩
  have hzz := Formalism.L2.SG.Pf.PCountEx.zz_fact Zd p sg hR g hM hge hgq u u' w (L := 1) (B := 1)
    Formalism.L2.SG.Pf.PCountEx.isLo_one' Formalism.L2.SG.Pf.PCountEx.isUp_one'
  have e1 : Matrix.diagonal (cf Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e2 : Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e3 : Matrix.diagonal (cfi Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  have e4 : Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  rw [e1, e2, e3, e4, glue_one_one, Matrix.one_mul, Matrix.mul_one] at hzz
  have hz : ZhatOM (ptMat w) = ptMat w * Sg D.host.E D.R.rS := by
    have h := Formalism.L2.SG.Pf.CountBase.zhatOM_sg (ptMat w)
    calc ZhatOM (ptMat w) = ZhatOM (ptMat w) * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
      _ = ptMat w * Sg D.host.E D.R.rS := by rw [h]
  rw [Matrix.one_mul, Matrix.mul_one, ← hz] at hzz
  have hYg : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = _ := hzz
  obtain ⟨Gl, Gu, hGl, hGu, hT⟩ := Formalism.L2.SG.Pf.PCountEx.target_fact Zd p sg hR g hM hge hgq u u' w
  have hY0 : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = Gl * modMat δ (D.mem u).A.T (D.mem u').A.T p w * Gu :=
    hzz.trans hT
  have hshE : Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Formalism.MainNotions.S.LocalSplitGroups.cornerSh δ (D.mem u).A.T (D.mem u').A.T p w • Ecorner D.R.rS := by
    ext i j
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Ecorner, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hsh : Gl * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w * Gu =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [hshE, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hGl hGu]
  have hmod := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  refine ⟨⟨(glOfLo p hGl, MulOpposite.op (glOfUp p hGu)), uni_of_isLo hGl, uni_of_isUp hGu⟩, ?_, ?_⟩
  · show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Gl * a.mat * Gu
    rw [hmod, Matrix.mul_add, Matrix.add_mul, hsh, ← hY0]
  · intro x

    have hd1 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p1 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -((D.mem u).A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_fst, Formalism.L2.SG.Pf.PCount.mm1' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hd2 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p2 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then ((D.mem u').A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_snd, Formalism.L2.SG.Pf.PCount.mm2' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hfix := corner_fix sg.e x.2.1 x.2.2 _ _ hd1 hd2
    have hphi : phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat +
        (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w) := by
      show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
        _
      rw [hmod]; abel
    rw [hphi, smul_def, smul_def, Matrix.mul_add, Matrix.add_mul, hfix]
    constructor
    · intro h; exact add_right_cancel h
    · intro h; rw [h]

theorem baseAt_holds (hA : ∀ p, Agree δ M p) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) : BaseAt M δ u u' w p a := by
  rcases hM : (M p).split with _ | g
  · have h := Formalism.L2.SG.Pf.CountBase.baseConj_L hA u u' w p hM a ha
    refine ⟨1, ?_, fun x => ?_⟩
    · rw [OneMemClass.coe_one, one_smul]; exact h
    · show _ ↔ _
      rw [show phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat from h]
  · exact baseAt_typed M δ u u' w p hA g hM a ha

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FixesBaseIff
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def tauU : UP p →* UP p where
  toFun x := ⟨tau p x, tau_mem_UP p x.2⟩
  map_one' := by ext1; exact (tau p).map_one
  map_mul' x y := by ext1; exact (tau p).map_mul x y

theorem tauU_tauU (x : UP p) : tauU p (tauU p x) = x := by
  ext1; exact tau_tau p x

def piU (πa : UP p →* UP p) : UP p →* UP p := (tauU p).comp (πa.comp (tauU p))

def piG (πa : UP p →* UP p) (x : GG p) : GG p :=
  if h : x ∈ UP p then ((piU p πa ⟨x, h⟩ : UP p) : GG p) else 1

theorem piG_of (πa : UP p →* UP p) (x : UP p) : piG p πa x = ((piU p πa x : UP p) : GG p) := by
  unfold piG; rw [dite_eq_left x.2]

theorem mem_StP_iff (x : GG p) :
    x ∈ StP M δ u u' w p ↔ x ∈ UP p ∧ x • Y0 M δ u u' w p = Y0 M δ u u' w p :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem fixes_base_iff (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (x : UP p) :
    (x : GG p) • Y0 M δ u u' w p = Y0 M δ u u' w p ↔ ((tauU p x : UP p) : GG p) • a.mat = a.mat := by
  rw [← (hB.choose_spec.2 (tauU p x))]
  constructor
  · intro h
    show tau p x • _ = _
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

theorem retr_of (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
    (hD : CountAb.Data (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)
    (hB : BaseAt M δ u u' w p a) :
    Formalism.L2.SG.Pf.ProdEP2Core.Retr (StP M δ u u' w p) (UP p) (piG p πa) := by
  refine ⟨fun x hx => ((mem_StP_iff M δ u u' w p x).1 hx).1, fun x hx y hy => ?_, fun x hx => ?_, fun s hs => ?_⟩
  · have ex : piG p πa x = ((piU p πa ⟨x, hx⟩ : UP p) : GG p) := piG_of p πa ⟨x, hx⟩
    have ey : piG p πa y = ((piU p πa ⟨y, hy⟩ : UP p) : GG p) := piG_of p πa ⟨y, hy⟩
    have exy : piG p πa (x * y) = ((piU p πa (⟨x, hx⟩ * ⟨y, hy⟩) : UP p) : GG p) :=
      piG_of p πa (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [exy, ex, ey, map_mul]
    rfl
  · rw [show x = ((⟨x, hx⟩ : UP p) : GG p) from rfl, piG_of]
    refine (mem_StP_iff M δ u u' w p _).2 ⟨(piU p πa ⟨x, hx⟩).2, ?_⟩
    rw [fixes_base_iff M δ u u' w p a hB]
    have h1 : tauU p (piU p πa ⟨x, hx⟩) = πa (tauU p ⟨x, hx⟩) := by
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
    rw [h1]
    exact hD.mem _
  · obtain ⟨hsU, hsY⟩ := (mem_StP_iff M δ u u' w p s).1 hs
    rw [show s = ((⟨s, hsU⟩ : UP p) : GG p) from rfl, piG_of]
    have hfix : tauU p ⟨s, hsU⟩ ∈ MulAction.stabilizer (UP p) a.mat :=
      (fixes_base_iff M δ u u' w p a hB ⟨s, hsU⟩).1 hsY
    have h2 : piU p πa ⟨s, hsU⟩ = ⟨s, hsU⟩ := by
      simp only [piU, MonoidHom.comp_apply, hD.id _ hfix, tauU_tauU]
    rw [h2]

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem rep_at_pt (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    ∃ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), Gval (lf D (X.Fu u)) F' ≠ 0 ∧
      IsInCell (ZhatOM (Zhat (X.Fu u) F'.fl)) (Formalism.L2.SG.PairVal.ptOf t.toTerm) ∧
      ∃ n ∈ SRat (lf D (X.Fu u)), ∃ m ∈ SRat (lf D (X.Fu u')),
        ∀ a, F'.fl.fvec a = (n * t.lin * m) ((X.Fu u').fvec a) := by
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hcell⟩ := at_ptOf Y t hG
  refine ⟨F', hGv, hcell, ?_⟩
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨F', hP⟩ := hmk.symm
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hrow _ _).1 hmk'
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hrel
  refine ⟨n, NLam_SRat hn, t.lin⁻¹ * m * t.lin, NLam_transport Y t hm, fun a => ?_⟩
  have := hfr a
  show F'.fl.fvec a = n (t.lin (t.lin.symm (m (t.lin ((X.Fu u').fvec a)))))
  rw [LinearEquiv.apply_symm_apply]
  rw [← frame_fvec Y t a]
  exact this

theorem ptdc_core (t1 t2 : TauC Y u u') (hN1 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t1))
    (hp : ptPN t1 = ptPN t2) :
    ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s' := by
  have hN2 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t2) := by rw [← hp]; exact hN1
  obtain ⟨F1, hG1, hc1, n1, hn1, m1, hm1, hF1⟩ := rep_at_pt Y t1 hN1
  obtain ⟨F2, hG2, hc2, n2, hn2, m2, hm2, hF2⟩ := rep_at_pt Y t2 hN2
  have hw : Formalism.L2.SG.PairVal.ptOf t1.toTerm = Formalism.L2.SG.PairVal.ptOf t2.toTerm := toPts_inj _ _ hp
  rw [hw] at hc1
  obtain ⟨g, hg, ⟨M, hM, hgM⟩, U, hU, hgU⟩ := same_cell (X.Fu u) F1.fl F2.fl hG1 hG2 _ hc1 hc2

  have hgs : g.symm ∈ SRat (lf D (X.Fu u)) := by
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u) (g.symm : (VS D).V →ₗ[D.host.E] (VS D).V) M hM hgM
    exact ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hg, hf, hz⟩
  have hgS : g ∈ SRat (lf D (X.Fu u)) := by simpa using SRat_inv (lf D (X.Fu u)) hgs
  set ρ1 := n1 * t1.lin * m1 with hρ1
  set ρ2 := n2 * t2.lin * m2 with hρ2
  set s'' := ρ2⁻¹ * g * ρ1 with hs''
  have hs''v : ∀ b, s''.symm ((X.Fu u').fvec b) = ∑ c, U c b • (X.Fu u').fvec c := by
    intro b
    apply s''.injective
    rw [LinearEquiv.apply_symm_apply, hs'']
    show (X.Fu u').fvec b = ρ2.symm (g (ρ1 (∑ c, U c b • (X.Fu u').fvec c)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
    have e1 : ∀ c, ρ1 ((X.Fu u').fvec c) = F1.fl.fvec c := fun c => (hF1 c).symm
    simp only [e1]
    rw [hgU b, hF2 b]
    simp
  have hs''S : s'' ∈ SRat (lf D (X.Fu u')) := by
    have hs''i : s'' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
      refine (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem ?_) hg) ?_
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn2.1 t2.rep.2.2.1) hm2.1
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn1.1 t1.rep.2.2.1) hm1.1
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u') (s''.symm : (VS D).V →ₗ[D.host.E] (VS D).V) U hU hs''v
    have : s''.symm ∈ SRat (lf D (X.Fu u')) := ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hs''i, hf, hz⟩
    simpa using SRat_inv (lf D (X.Fu u')) this
  refine ⟨n2⁻¹ * g * n1, SRat_mul _ (SRat_mul _ (SRat_inv _ hn2) hgS) hn1,
    m1 * s''⁻¹ * m2⁻¹, SRat_mul _ (SRat_mul _ hm1 (SRat_inv _ hs''S)) (SRat_inv _ hm2), ?_⟩
  have e : ρ2 = g * ρ1 * s''⁻¹ := by rw [hs'']; group
  rw [hρ2, hρ1] at e
  calc t2.lin = n2⁻¹ * (n2 * t2.lin * m2) * m2⁻¹ := by group
    _ = n2⁻¹ * (g * (n1 * t1.lin * m1) * s''⁻¹) * m2⁻¹ := by rw [e]
    _ = n2⁻¹ * g * n1 * t1.lin * (m1 * s''⁻¹ * m2⁻¹) := by group

theorem NmlPtDC_holds : NmlPtDC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ γ hγ t1 t2 _ _ h1 h2 _ => ?_⟩
  subst h1
  exact ptdc_core Y t1 t2 hγ h2.symm

theorem NmlSep_holds : NmlSep := nmlSep_of NmlPtDC_holds normalsLemmaG3_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

