module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0593
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0595
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundary
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import GroundTheory.GlobalFields.TateThesis.AdelicChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmFonOfPoints
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HubFon

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

end GlobalTheory.HubFon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtGoodPointsOfCoefRingTakenAtLive
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem GlobalTheory.AdmissibleCore.main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  intro hC D X hT hA hX i π hπ
  intro hZ
  obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (X.r i π) (X.ρ i π) (D.nd.chi i) e := ⟨e, fun g u => he g u⟩
  have hHG : IsHeckeGalois D.nd i π (X.r i π) := hX.good i π
  have hpt : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (X.ρ i π) := ⟨hX.cont i π, X.r i π, hHG, e, fun g u => he g u⟩
  have hirr := hA i π hπ (X.ρ i π) hpt
  have hLive : GlobalTheory.CoefDuty.Live D.nd i := ⟨π, hZ, X.r i π, X.ρ i π, hHG, hdec, hirr⟩
  obtain ⟨r₀, ρ₀, hg₀, hw₀⟩ := hT i hLive
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hg₀ hw₀ (X.r i) (X.ρ i) (hX.good i) π hZ hdec
  exact ⟨S, hS⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

private theorem map_smul_ringHom' {n : Type} {α β : Type} [CommRing α] [CommRing β] (F : α →+* β) (c : α)
    (M : Matrix n n α) : (c • M).map F = F c • M.map F :=
  Matrix.map_smul' F c M (map_mul F)

private theorem smul_cancel' {n : Type} {D : Type} [CommRing D] {c : D} (hc : c ∈ nonZeroDivisors D)
    {M M' : Matrix n n D} (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 this

private theorem alg' {n : Type} [Fintype n] [DecidableEq n] {D : Type} [CommRing D] (Φ : D →+* D)
    (L pf pg fE gE : D) (a N : ℕ) (xf xg Af Ag ε Fm : Matrix n n D)
    (h1f : (L * pf ^ N) • (xf * Af) = fE ^ (a + 2 * N) • (Fm * xf.map Φ))
    (h1g : (L * pg ^ N) • (xg * Ag) = gE ^ (a + 2 * N) • (Fm * xg.map Φ))
    (hR : gE ^ N • (xf * ε) = fE ^ N • xg) (hpf : Φ fE = pf) (hpg : Φ gE = pg) :
    (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ))) =
      (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
  have hΦR : pg ^ N • (xf.map Φ * ε.map Φ) = pf ^ N • xg.map Φ := by
    have := congrArg (fun M => M.map Φ) hR
    simpa only [map_smul_ringHom', Matrix.map_mul, map_pow, hpf, hpg] using this
  calc (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ)))
      = (pg ^ N * gE ^ (a + 2 * N)) • (((L * pf ^ N) • (xf * Af)) * ε.map Φ) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (pg ^ N * gE ^ (a + 2 * N)) • ((fE ^ (a + 2 * N) • (Fm * xf.map Φ)) * ε.map Φ) := by rw [h1f]
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pg ^ N • (xf.map Φ * ε.map Φ))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pf ^ N • xg.map Φ)) := by rw [hΦR]
    _ = (fE ^ (a + 2 * N) * pf ^ N) • (gE ^ (a + 2 * N) • (Fm * xg.map Φ)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + 2 * N) * pf ^ N) • ((L * pg ^ N) • (xg * Ag)) := by rw [h1g]
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((fE ^ N • xg) * Ag) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((gE ^ N • (xf * ε)) * Ag) := by rw [hR]
    _ = (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring

theorem rel_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g : Hom bk.prism B) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → ∀ Φ : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ → toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ (ht.a + s.N) • ((ht.A.map (BK.hf f)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) * ε.map Φ) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E) ^ (ht.a + s.N) • (ε * (ht.A.map (BK.hf g)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
  intro l _ K bk d ρ τ s ht hτ B f₀ hE f g ε hR Φ hΦ

  have hρpos : 0 < bk.ρ₀ := by
    unfold BK.ρ₀; exact NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos)
  have hρle : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      (by have : (0 : ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
          linarith)

  have hnS : ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
    rw [frobS_X]
    refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l hρpos).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρle) (Fact.out : l.Prime).ne_zero
  have hΦS := isDiscMap_map (frobS l bk.a) hnS

  have key : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) Fh →
      (((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) ^ s.N) •
        (ht.bas.map Fh * (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) =
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) * (ht.bas.map Fh).map Φ)) := by
    intro h Fh hFh
    have hφ : ∀ x, BK.hf h (frobS l bk.a x) = B.D.φ (BK.hf h x) := fun x => h.f_φ x
    have c1 : IsDiscMap (l := _) (u := _) (ρ := _) (B.D.φ.comp (BK.hf h)) (Φ.comp Fh) :=
      ⟨fun x => by simp [hFh.ext, hΦ.ext], fun x => (hΦ.norm_le _).trans (hFh.norm_le _)⟩
    have c2 : IsDiscMap (l := _) (u := _) (ρ := _) (B.D.φ.comp (BK.hf h)) (Fh.comp (Disc.map (frobS l bk.a) hnS)) :=
      ⟨fun x => by simp [hFh.ext, hΦS.ext, hφ], fun x => (hFh.norm_le _).trans (hΦS.norm_le _)⟩
    have hc : Φ.comp Fh = Fh.comp (Disc.map (frobS l bk.a) hnS) := c1.unique c2
    have hP := congrArg (fun M => M.map Fh) (GlobalTheory.T.latticeBasis_frobenius_equation_disc l K bk d ρ τ s ht hτ _ hΦS)
    simp only [map_smul_ringHom', Matrix.map_mul, Matrix.map_map, map_mul, map_pow, map_natCast] at hP
    have eA : (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) = ht.A.map (Fh ∘ toDisc l (X : bk.S) bk.ρ₀) := by
      ext i j; exact (hFh.ext _).symm
    have eF : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) =
        s.F.map (Fh ∘ (toDisc l (X : bk.S) bk.ρ₀).comp C) := by
      ext i j; exact (hFh.ext _).symm
    have eB : (ht.bas.map Fh).map Φ = ht.bas.map (Fh ∘ Disc.map (frobS l bk.a) hnS) := by
      ext i j; exact RingHom.congr_fun hc _
    have e1 : toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) = Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) :=
      ((hFh.ext _).trans (congrArg _ (hφ _))).symm
    have e2 : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = Fh (toDisc l (X : bk.S) bk.ρ₀ bk.E) := (hFh.ext _).symm
    simp only [eA, eF, eB, e1, e2]
    exact hP

  have hn := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀
  have hFf := isDiscMap_map (BK.hf f) (hn f).1
  have hFg := isDiscMap_map (BK.hf g) (hn g).1
  have h1f := key f _ hFf
  have h1g := key g _ hFg
  have hFm : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf g).comp C)) = s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf f).comp C)) := by
    congr 1; funext w; simp [_root_.GlobalTheory.BSP.hf_C_eq_of_pair l K bk B f g w]
  simp only [hFm] at h1g

  have hreg : ∀ h : Hom bk.prism B, toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    intro h
    obtain ⟨v, hv⟩ := (_root_.GlobalTheory.BSP.hf_E_pair l K bk B f₀ h).2.1
    have e : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) * toDisc l (BK.hf f₀ X) bk.ρ₀ (v : B.A) :=
      (congrArg _ hv).symm.trans (map_mul _ _ _)
    exact (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) e).mpr
      (Submonoid.mul_mem _ hE ((v.isUnit.map (toDisc l (BK.hf f₀ X) bk.ρ₀)).mem_nonZeroDivisors))
  have hunit : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) Fh →
      IsUnit (toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E))) := by
    intro h Fh hFh
    have := (_root_.GlobalTheory.BSP.isUnit_toDisc_frobS_E l K bk).map Fh
    have e : Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) :=
      (hFh.ext _).trans (congrArg _ (h.f_φ _))
    exact (congrArg IsUnit e).mp this
  have hpf : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) := hΦ.ext _
  have hpg : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) := hΦ.ext _
  have hAlg := alg' Φ _ _ _ _ _ _ _ _ _ _ _ _ _ h1f h1g (hR _ _ hFf hFg) hpf hpg
  have hc : ((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) ^ s.N *
      toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) ^ s.N * toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ s.N) ∈ nonZeroDivisors _ := by
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) (pow_mem (hreg g) _)
    · exact ((isUnit_l_disc l (BK.hf f₀ X) bk.ρ₀).pow _).mem_nonZeroDivisors
    · exact ((hunit f _ hFf).pow _).mem_nonZeroDivisors
    · exact ((hunit g _ hFg).pow _).mem_nonZeroDivisors
  have hM := smul_cancel' hc hAlg
  have hF0 : Disc.map (BK.hf f) (hn f).1 (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors _ :=
    (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) (hFf.ext bk.E)).mpr (hreg f)
  have := _root_.GlobalTheory.BSP.Height.bas_map_cancel_left l K bk d ρ τ s ht _ _ hF0 _ _ hM
  exact this

end GlobalTheory.BSP.Height
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.WhitCont

open GroundTheory.Automorphic.FourierWhittaker

theorem continuous_whit : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), Continuous F →
    (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → Continuous (GlobalTheory.JSW.whit F) := by
  intro E _ _ a F hF ⟨C, hC⟩
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hψ : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hj : Continuous fun p : GA E a × (Pos a → Ad E) =>
      F (uGL p.2 * p.1) * (GroundTheory.Global.adelicChar E (-supSum 0 p.2) : ℂ) :=
    (hF.comp ((continuous_uGL.comp continuous_snd).mul continuous_fst)).mul (hψ.comp continuous_snd)
  have e : GlobalTheory.JSW.whit F = fun g => ∫ X, F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂μ := rfl
  rw [e]
  set_option synthInstance.maxHeartbeats 200000 in
  refine continuous_of_dominated (bound := fun _ => C) (fun g => ?_) (fun g => ?_) (integrable_const C) ?_
  · have h1 : Continuous fun X : Pos a → Ad E => (g, X) := continuous_const.prodMk continuous_id
    exact (hj.comp h1).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact hC _
  · refine Filter.Eventually.of_forall fun X => ?_
    exact (hF.comp (continuous_const.mul continuous_id)).mul continuous_const

end GlobalTheory.JSW.WhitCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousUnipotentColumnWhittakerTransform
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_colT_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  intro E _ _ a ψ hψ m f hf
  have hl : ∀ (c : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  have key := _root_.GlobalTheory.CuspGeneric.continuous_avg_of_periodic (UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E a)
    (fun p => ψ (-dot (eLast a (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · refine (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hf.cont.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast a (m + 1)) hf.cont hl g).2 γ hγ y

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariantsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  first | exact @GlobalTheory.CrisCoord.lattice_basis_span_invariants | exact GlobalTheory.CrisCoord.lattice_basis_span_invariants | (intros; apply GlobalTheory.CrisCoord.lattice_basis_span_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLocalCoefficients
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.DualTwistCrys

theorem crys_chi (D : D7) (i : D.nd.Loc) (hChi : GlobalTheory.PtCore.ChiOneE D i) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := hChi w hw C.LL C.le

theorem card_emb (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
  have := D.nd.lPrime i
  have := C.LL.2
  have := (D.nbr i w hw).Kw.2
  have h2 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw C.LL (fun τ y => C.le
    ((D.nbr i w hw).LL_split τ y)) inferInstance).2
  rw [Nat.card_eq_fintype_card, h2]

theorem twist_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) := by
  have := D.nd.lPrime i
  have := C.LL.2
  refine (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _)
    (D.nbr i w hw).Kw C.LL _ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) _
    (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹
    ⟨LinearEquiv.refl _ _, fun g v => ?_⟩ hchi hcC).1
  rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, GlobalTheory.TateDualCrys.matRep_apply,
    GlobalTheory.TateDualCrys.matRep_apply]
  exact Matrix.smul_mulVec _ _ _

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hcw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ hcw

theorem dual_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (htw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact (GlobalTheory.TateDualCrys.tateDual (D.locT _) (D.nbr i w hw).Kw C.LL (card_emb D i w hw C) _ _
    (GlobalTheory.TateDualCrys.loc_rDuO D i w hw C.LL C.le r x) htw).1

theorem tw_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  rw [← GlobalTheory.AmbientDual.twist_locC]
  exact twist_crys D i r w hw C x hchi hcC

end GlobalTheory.DualTwistCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundaryStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_product_finite_classes_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ finiteCocycles (P.PD K) A.ρ, ∀ b ∈ finiteCocycles (P.PD K) A'.ρ, CobL (P.PD K) (cupL A'.ρ m a b) := by
  first | exact @GlobalTheory.BKOrth.bk_orth | exact GlobalTheory.BKOrth.bk_orth | (intros; apply GlobalTheory.BKOrth.bk_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalBlockAverageLastColumnEqZero
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CuspGeneric

def cuspBlockIndexEquivLastColumnIndex (a r : ℕ) : BlockIx a r ≃ UnipotentBlockColumnIndex a r (a - 1) where
  toFun p := ⟨p.1, p.2.1, p.2.2, by have := p.1.2.isLt; omega⟩
  invFun q := ⟨q.1, q.2.1, q.2.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem posM_apply_of_blkIx {R : Type} [CommRing R] {a r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM Subtype.val x i j = if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  classical
  simp only [posM, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp [Matrix.single_apply]
    · intro t _ ht
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    have := t.2
    rw [h1, h2] at this
    exact h this

theorem blkU_eq_unip {R : Type} [CommRing R] {a r : ℕ} (x : UnipotentBlockColumnIndex a r (a - 1) → R) :
    (blkU x : GL (Fin a) R) = unip (fun p => x (cuspBlockIndexEquivLastColumnIndex a r p)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = (1 + nilM _ : Matrix (Fin a) (Fin a) R) i j
  rw [Matrix.add_apply, Matrix.add_apply, posM_apply_of_blkIx]
  simp only [nilM, Matrix.of_apply]
  congr 1
  have hj := j.2
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · rw [dite_eq_left h, dite_eq_left ⟨h.1, h.2, by omega⟩]
    rfl
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]

theorem avg_blk_last_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ),
    Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspRep.IsCuspidal F →
    ∀ r : ℕ, 0 < r → r ≤ a - 1 → ∀ g : GA E a,
      GlobalTheory.CuspGeneric.avg (GlobalTheory.CuspGeneric.ratV E (GlobalTheory.CuspGeneric.UnipotentBlockColumnIndex a r (a - 1)))
        (fun x => F ((GlobalTheory.CuspGeneric.blkU x : GA E a) * g)) = 0 := by
  intro E _ _ _ a F _ _ hF r hr0 hr g
  have hra : r < a := by omega
  letI : MeasurableSpace (UnipotentBlockColumnIndex a r (a - 1) → Ad E) := borel _
  haveI : BorelSpace (UnipotentBlockColumnIndex a r (a - 1) → Ad E) := ⟨rfl⟩
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  swap
  · rfl
  obtain ⟨hμ, h𝓕, -⟩ := h.choose_spec
  set μ := h.choose.1
  set 𝓕 := h.choose.2
  let e := cuspBlockIndexEquivLastColumnIndex a r
  let β : (UnipotentBlockColumnIndex a r (a - 1) → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := fun x p => x (e p)
      invFun := fun y q => y (e.symm q)
      left_inv := fun x => funext fun q => congrArg x (e.apply_symm_apply q)
      right_inv := fun y => funext fun p => congrArg y (e.symm_apply_apply p)
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply (e p)
      continuous_invFun := continuous_pi fun q => continuous_apply (e.symm q) }
  let q : ratN E a r ≃ ratV E (UnipotentBlockColumnIndex a r (a - 1)) :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨c, hc⟩ := y.2
        exact ⟨fun t => c (e.symm t), by rw [← hc]; rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨c, hc⟩ := x.2
        exact ⟨fun p => c (e p), by rw [← hc]; rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hF r hr0 hra (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (h𝓕.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving q fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply]) g
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  rw [blkU_eq_unip]
  rfl

end GlobalTheory.CuspGeneric
end
end

