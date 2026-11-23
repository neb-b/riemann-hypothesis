module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodCocycleFrobeniusRelationOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.KappaFrob

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ := by
  intro l hl K bk τ hτ d ρ _ s g G Φ hG hΦ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h

  have hfτ : WittVector.frobenius τ ≠ 0 := by
    obtain ⟨-, ε, η, ⟨-, hδ1⟩, h⟩ := hτ
    rw [h]
    intro h'
    rw [Units.mul_right_eq_zero, sub_eq_zero] at h'
    have h1' : ε = 1 := by simpa using congrArg (fun w : Ainf l => w.coeff 0) h'
    exact hδ1 (by rw [h1', map_one, map_one])
  have hEτ : bk.ev bk.E * τ ≠ 0 := hτ.1 ▸ hfτ
  have hτ0 : τ ≠ 0 := right_ne_zero_of_mul hEτ
  have hE0 : bk.ev bk.E ≠ 0 := left_ne_zero_of_mul hEτ
  have hσinj : Function.Injective (Per.σA (g : GQ l)) := fun x y hxy => by
    have := congrArg (Per.σA ((g : GQ l)⁻¹)) hxy
    rwa [← GlobalTheory.RingBasics.σA_mul, ← GlobalTheory.RingBasics.σA_mul, inv_mul_cancel, GlobalTheory.RingBasics.σA_one, GlobalTheory.RingBasics.σA_one] at this
  have ha : bk.iA (bk.ev bk.E * τ) ≠ 0 := fun h => hEτ (hi (h.trans (map_zero _).symm))
  have hb : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ≠ 0 := fun h =>
    hEτ (hσinj ((hi (h.trans (map_zero _).symm)).trans (map_zero _).symm))

  have hcomm : Φ.comp G = G.comp Φ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l)) =
        (Per.σA (g : GQ l)).comp WittVector.frobenius :=
      RingHom.ext fun x => (GlobalTheory.GalPhi.σA_frobenius _ x).symm
    have k1 : IsDiscMap (l := _) (u := _) (ρ := _) ((WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l))) (Φ.comp G) :=
      ⟨fun x => by rw [RingHom.comp_apply, hG.ext, hΦ.ext, RingHom.comp_apply],
        fun x => (hΦ.norm_le _).trans (hG.norm_le _)⟩
    have k2 : IsDiscMap (l := _) (u := _) (ρ := _) ((Per.σA (g : GQ l)).comp WittVector.frobenius) (G.comp Φ) :=
      ⟨fun x => by rw [RingHom.comp_apply, hΦ.ext, hG.ext, RingHom.comp_apply],
        fun x => (hG.norm_le _).trans (hΦ.norm_le _)⟩
    rw [e] at k1
    exact k1.unique k2
  have hΦa : Φ (bk.iA (bk.ev bk.E * τ)) = bk.iS (frobS l bk.a bk.E) * bk.iA (bk.ev bk.E * τ) := by
    rw [hΦ.ext, map_mul, hτ.1, ← bk.ev_frob, map_mul]; rfl
  have hΦb : Φ (bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ))) =
      G (bk.iS (frobS l bk.a bk.E)) * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by
    rw [hΦ.ext, ← GlobalTheory.GalPhi.σA_frobenius, map_mul, hτ.1, ← bk.ev_frob, map_mul, map_mul]
    rw [show bk.iS (frobS l bk.a bk.E) = bk.iA (bk.ev (frobS l bk.a bk.E)) from rfl, hG.ext]

  have hφ : ((l : bk.DA bk.ρ₀) ^ s.c₁) • (s.W * s.X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ s.N • (s.W * s.X'.map bk.iS * s.F.map (bk.iS.comp C)) := s.φ Φ hΦ
  have hgal := s.gal g G hG
  set P := s.W * s.X'.map bk.iS with hP
  set FD := s.F.map (bk.iS.comp C) with hFD'
  set R := (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) with hR'
  set κ := s.κ g with hκ
  set a := bk.iA (bk.ev bk.E * τ) with ha'
  set b := bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) with hb'
  set u := bk.iS (frobS l bk.a bk.E) with hu'
  set L := (l : bk.DA bk.ρ₀) ^ s.c₁ with hL'
  have hMG : ∀ (H : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (c • M).map H = H c • M.map H := fun H c M => Matrix.map_smul' _ _ _ (map_mul H)
  have hR : R.map Φ = R := Matrix.ext fun i j => by
    simp only [hR', Matrix.map_apply, RingHom.comp_apply]
    rw [hΦ.ext, GlobalTheory.GalPhi.frobenius_algebraMap]
  have hFD : FD.map G = FD := Matrix.ext fun i j => by
    simp only [hFD', Matrix.map_apply, RingHom.comp_apply]
    change G (bk.iA (bk.ev (C (s.F i j)))) = bk.iA (bk.ev (C (s.F i j)))
    rw [hG.ext, bk.ev_C, bk.gal_w]
  have hPG : (P.map G).map Φ = (P.map Φ).map G := Matrix.ext fun i j => by
    simp only [Matrix.map_apply]; exact RingHom.congr_fun hcomm _
  have hgalΦ : Φ a ^ s.N • (R * (P.map Φ).map G) = Φ b ^ s.N • (P.map Φ * κ.map Φ) := by
    have h := congrArg (fun M => M.map Φ) hgal
    have e1 : (R * P.map G).map Φ = R.map Φ * (P.map G).map Φ := Matrix.map_mul
    have e2 : (P * κ).map Φ = P.map Φ * κ.map Φ := Matrix.map_mul
    rwa [hMG, hMG, e1, e2, hR, hPG, map_pow, map_pow] at h
  have hL : G L = L := by simp [hL']
  have hA : L • (R * (P.map Φ).map G) = G (u ^ s.N) • (R * P.map G * FD) := by
    rw [← Matrix.mul_smul, ← hL, ← hMG, hφ, hMG, Matrix.map_mul, hFD, Matrix.mul_smul, Matrix.mul_assoc]
  have hB : L • (P.map Φ * κ.map Φ) = u ^ s.N • (P * FD * κ.map Φ) := by
    rw [← Matrix.smul_mul, hφ, Matrix.smul_mul]
  have step1 : (Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD) = (Φ b ^ s.N * u ^ s.N) • (P * FD * κ.map Φ) := by
    calc (Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD) = Φ a ^ s.N • (L • (R * (P.map Φ).map G)) := by
          rw [hA, smul_smul]
      _ = L • (Φ a ^ s.N • (R * (P.map Φ).map G)) := smul_comm _ _ _
      _ = L • (Φ b ^ s.N • (P.map Φ * κ.map Φ)) := by rw [hgalΦ]
      _ = Φ b ^ s.N • (L • (P.map Φ * κ.map Φ)) := smul_comm _ _ _
      _ = _ := by rw [hB, smul_smul]
  have hΦa' : Φ a ^ s.N = u ^ s.N * a ^ s.N := by rw [hΦa, mul_pow]
  have hΦb' : Φ b ^ s.N = G (u ^ s.N) * b ^ s.N := by rw [hΦb, mul_pow, map_pow]
  have key : (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * κ * FD) =
      (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * FD * κ.map Φ) := by
    calc (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * κ * FD)
        = (Φ a ^ s.N * G (u ^ s.N)) • ((b ^ s.N • (P * κ)) * FD) := by
          rw [Matrix.smul_mul, smul_smul, hΦa']; congr 1; ring
      _ = (Φ a ^ s.N * G (u ^ s.N)) • ((a ^ s.N • (R * P.map G)) * FD) := by rw [hgal]
      _ = a ^ s.N • ((Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD)) := by
          rw [Matrix.smul_mul, smul_comm]
      _ = a ^ s.N • ((Φ b ^ s.N * u ^ s.N) • (P * FD * κ.map Φ)) := by rw [step1]
      _ = _ := by rw [smul_smul, hΦb']; congr 1; ring
  have hc : u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hu.pow _).ne_zero ((hu.pow _).map G).ne_zero) (pow_ne_zero _ ha))
      (pow_ne_zero _ hb)
  have h3 : P * κ * FD = P * FD * κ.map Φ := Matrix.ext fun i j => by
    have := congrFun (congrFun key i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this

  have hτi : bk.iA τ ≠ 0 := fun h => hτ0 (hi (h.trans (map_zero _).symm))
  have hdW : s.W.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det s.W_mul
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, h, zero_mul] at this
    exact pow_ne_zero _ (pow_ne_zero _ hτi) this.symm
  have hEi : bk.iS bk.E ≠ 0 := fun h => hE0 (hi (h.trans (map_zero _).symm))
  have hl0 : (l : bk.DA bk.ρ₀) ≠ 0 := (isUnit_l_disc l _ _).ne_zero
  have hdX : (s.X'.map bk.iS).det ≠ 0 := by
    intro h
    have := congrArg (fun M => (M.map bk.iS).det) s.X_mul
    rw [Matrix.map_mul, Matrix.det_mul, h, mul_zero, Matrix.map_smul' _ _ _ (map_mul bk.iS), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.det_smul, Matrix.det_one, mul_one, map_mul, map_pow, map_pow, map_natCast] at this
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hEi)) this.symm
  have hdP : P.det ≠ 0 := by rw [hP, Matrix.det_mul]; exact mul_ne_zero hdW hdX
  have h4 : P.det • (κ * FD) = P.det • (FD * κ.map Φ) := by
    have e : ∀ M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), P.det • M = P.adjugate * (P * M) := fun M => by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [e, e, ← Matrix.mul_assoc P, ← Matrix.mul_assoc P, h3]
  exact Matrix.ext fun i j => by
    have := congrFun (congrFun h4 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hdP this

end GlobalTheory.BKLim.KappaFrob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameCocycleFrobeniusTwistOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.FrobTwistKappa

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  intro l _ K bk τ d ρ s g G Φ i Ψ V ε hG hΦ hi hΨ hκ h
  have hsmul : ∀ (f : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (c • M).map f = f c • M.map f := fun f c M => by ext a b; simp
  have hΦG : ∀ x, Φ (G x) = G (Φ x) := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l)) =
        (Per.σA (g : GQ l)).comp WittVector.frobenius :=
      RingHom.ext fun a => (GlobalTheory.Prism.PullGal.σA_frobenius (g : GQ l) a).symm
    have hc := (GlobalTheory.BSP.FrobRational.isDiscMap_comp hG hΦ).unique
      (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΦ hG)
    exact fun x => RingHom.congr_fun hc x
  have hΦi : Φ.comp i = i.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (GlobalTheory.BSP.FrobRational.isDiscMap_comp hi hΦ).unique (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΨ hi)
  have hΦiS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (toDisc l (bk.ev X) bk.ρ₀ (bk.ev x)) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have hFD : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C)).map i = s.F.map (bk.iS.comp C) := by
    ext a b
    exact hi.ext _
  have hGFD : (s.F.map (bk.iS.comp C)).map G = s.F.map (bk.iS.comp C) := by
    ext a b
    change G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))
    rw [hG.ext, bk.ev_C, bk.gal_w]
  have e1 : (V.map i).map Φ = (V.map Ψ).map i := by
    ext a b
    exact RingHom.congr_fun hΦi (V a b)
  have e2 : (ε.map bk.iA).map Φ = (ε.map WittVector.frobenius).map bk.iA := by
    ext a b
    exact hΦ.ext _
  have e3 : ((V.map i).map G).map Φ = ((V.map Ψ).map i).map G := by
    ext a b
    simp only [Matrix.map_apply]
    rw [hΦG]
    exact congrArg G (RingHom.congr_fun hΦi (V a b))
  have h1 := congrArg (fun M => M.map Φ) h
  simp only [hsmul, Matrix.map_mul] at h1
  rw [map_pow, map_pow, hΦG, hΦiS, e1, e2, e3] at h1
  have eL : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i =
      s.F.map (bk.iS.comp C) * (V.map Ψ).map i := by
    rw [Matrix.map_mul, hFD]
  rw [eL, Matrix.map_mul, hGFD, Matrix.mul_assoc (s.F.map (bk.iS.comp C)), ← Matrix.mul_assoc (s.κ g), hκ,
    Matrix.mul_assoc]
  have h2 := congrArg (fun M => s.F.map (bk.iS.comp C) * M) h1
  simp only [Matrix.mul_smul] at h2
  exact h2

end GlobalTheory.BKLim.FrobTwistKappa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusOfScaledInverse
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.wseed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (_root_.GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (_root_.GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (GlobalTheory.T.frobenius_matrix_relation_discrete l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusRationalOverKisinRing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.FrobRational

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  intro l hl K bk τ hτ d ρ hρ s Y1 Z1 hY hYZ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  haveI : IsDomain (Ainf l) := hi.isDomain _
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hcomm : Φ.comp j = j.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (GlobalTheory.BSP.FrobRational.isDiscMap_comp hj hΦ).unique (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΨ hj)
  have hlam : bk.iA (bk.ev ((l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N)) =
      (l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N := by
    simp only [map_mul, map_pow, map_natCast, RingHom.comp_apply]
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h
  have hne : (l : bk.S) ^ (s.c₁ + s.c₂) * frobS l bk.a bk.E ^ s.N ≠ 0 := fun h => by
    rw [h, map_zero, map_zero] at hlam
    exact (((isUnit_l_disc l _ _).pow _).mul (hu.pow _)).ne_zero hlam.symm
  exact GlobalTheory.BSP.FrobRational.core bk.ev (toDisc l (X : bk.S) bk.ρ₀) bk.iA j hi hj.ext WittVector.frobenius Φ Ψ hΦ.ext
    (fun x => RingHom.congr_fun hcomm x) (GlobalTheory.BSP.linDisjoint_disc l K bk _ bk.ev ι TB j hj) _ hne s.W _
    (by rw [hlam]; exact GlobalTheory.T.frobenius_matrix_relation_discrete l K bk τ hτ d ρ hρ s Φ hΦ) Y1 Z1 hY (hYZ j hj)

end GlobalTheory.BKLim.FrobRational
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodSpanFrobeniusStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem wseed_span_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) :=
  by
  intro l hl K bk τ hτ d ρ hρ s y ⟨x, hx⟩
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := _root_.GlobalTheory.BSP.flat_disc l K bk
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l bk.S bk.S (frobS l bk.a) X X bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hu : IsUnit (((l : ℕ) : bk.DS bk.ρ₀) ^ (s.c₁ + s.c₂) *
      toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) :=
    ((isUnit_l_disc l (X : bk.S) bk.ρ₀).pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  obtain ⟨c, hc⟩ := hu
  refine ⟨fun a => ((c⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) *
    ((s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map (toDisc l (X : bk.S) bk.ρ₀) *ᵥ
      fun b => Ψ (x b)) a, fun j hj => ?_⟩
  have hcomm : j.comp Ψ = Φ.comp j := by
    refine IsDiscMap.unique (DiscBasic.isDiscMap_comp l _ _ hΨ hj) ?_
    have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
      RingHom.ext bk.ev_frob
    rw [e]
    exact DiscBasic.isDiscMap_comp l _ _ hj hΦ
  have hW := GlobalTheory.T.frobenius_matrix_relation_discrete l K bk τ hτ d ρ hρ s Φ hΦ
  rw [GlobalTheory.BSP.mulVec_frob_of_unit j Φ Ψ (RingHom.congr_fun hcomm) c s.W _ ?_ x, hx j hj]
  · funext a
    exact hΦ.ext _
  · rw [hc, map_mul, map_pow, map_pow, map_natCast, hj.ext, Matrix.map_map]
    refine hW.trans ?_
    congr 2
    funext a
    exact (hj.ext a).symm

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedModuleLAdicClosed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem wseed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  intro l _ K bk τ hτ d ρ hρ s y hy _hcau z hz
  beta_reduce at hy ⊢
  obtain ⟨hρ0, hρ1⟩ := bk.ρ₀_mem_Ioo_zero_one
  have hX : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  set j₀ : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hX with hj₀
  have hj₀d : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j₀ := isDiscMap_map bk.ev hX
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨cD, hc_to, hc_mul, hc_norm, -⟩ := GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j₀ hj₀d
  obtain ⟨r, hr⟩ := GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB (2 * s.N * d)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hr

  set V : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := s.W'.det • adjugate s.W with hV
  have hVW : V * s.W = bk.iA (τ ^ (2 * s.N * d)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have hd : s.W.det * s.W'.det = bk.iA (τ ^ (2 * s.N * d)) := by
      rw [← det_mul, s.W_mul, det_smul, det_one, mul_one, Fintype.card_fin, map_pow]
      ring
    rw [hV, smul_mul, adjugate_mul, smul_smul, mul_comm, hd]

  let Φ : bk.DA bk.ρ₀ → bk.DS bk.ρ₀ := fun w => ∑ i ∈ f.support, toDisc l (X : bk.S) bk.ρ₀ (f i) * cD i w
  have key : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      (l : bk.DS bk.ρ₀) ^ r * x a = Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    have hsm : ∀ (c : bk.DA bk.ρ₀) (v : Fin d → bk.DA bk.ρ₀), (c • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) *ᵥ v = c • v := by
      intro c v; ext b; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [mulVec_mulVec, hVW, hsm]
    have h1 : ∀ i, cD i ((bk.iA (τ ^ (2 * s.N * d)) • fun b => j₀ (x b)) a) =
        x a * toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hc_mul, hc_to]
    simp only [Φ, h1]
    have h2 := congrArg (toDisc l (X : bk.S) bk.ρ₀) hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.sum, map_sum, map_pow, map_natCast] at h2
    rw [← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul]; ring
  obtain ⟨u, hu⟩ : IsUnit ((l : bk.DS bk.ρ₀) ^ r) := (isUnit_l_disc l (X : bk.S) bk.ρ₀).pow r
  have hsol : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      x a = ↑u⁻¹ * Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    rw [← key, ← hu, Units.inv_mul_cancel_left]

  have hcont : ∀ {F : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀}, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev F → Continuous F := fun hF =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hF.norm_le x).trans (one_mul _).ge
  have hcDc : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hc_norm i x).trans (one_mul _).ge
  let G : (Fin d → bk.DA bk.ρ₀) → (Fin d → bk.DA bk.ρ₀) := fun v =>
    s.W *ᵥ fun a => j₀ (↑u⁻¹ * Φ ((V *ᵥ v) a))
  have hGc : Continuous G := by
    refine continuous_const.matrix_mulVec (continuous_pi fun a => (hcont hj₀d).comp (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hcDc i).comp ((continuous_apply a).comp (continuous_const.matrix_mulVec continuous_id)))
  have hGy : ∀ n, G (fun a => bk.iA (y n a)) = fun a => bk.iA (y n a) := by
    intro n
    obtain ⟨x, hx⟩ := hy n
    have hxe := hx j₀ hj₀d
    have h3 : G (s.W *ᵥ fun b => j₀ (x b)) = s.W *ᵥ fun b => j₀ (x b) := by
      dsimp only [G]; congr 1; funext a; rw [← hsol x a]
    rwa [hxe] at h3

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n => fun a => bk.iA (y n a)) Filter.atTop (nhds fun a => bk.iA (z a)) := by
    rw [tendsto_pi_nhds]; intro a
    have h0 : Filter.Tendsto (fun n => bk.iA (z a - y n a)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1))
      obtain ⟨w, hw⟩ := hz n a
      rw [hw]; exact norm_toDisc_natPow_mul_le _ _ n w
    have h4 := (tendsto_const_nhds (x := bk.iA (z a))).sub h0
    simpa only [sub_zero, map_sub, sub_sub_cancel] using h4
  have hfix : G (fun a => bk.iA (z a)) = fun a => bk.iA (z a) :=
    (isClosed_eq hGc continuous_id).mem_of_tendsto ht (Filter.Eventually.of_forall hGy)
  refine ⟨fun a => ↑u⁻¹ * Φ ((V *ᵥ fun b => bk.iA (z b)) a), fun j hj => ?_⟩
  rw [hj.unique hj₀d]
  exact hfix

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) s F → Function.Injective F := by
  first | exact @GlobalTheory.BSP.topBasis_disc_regular | exact GlobalTheory.BSP.topBasis_disc_regular | (intros; apply GlobalTheory.BSP.topBasis_disc_regular <;> assumption)
end

