module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0581
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfExistsMulEqPowSmulOfModLPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfInvLim

theorem dvd_mul_entry {R : Type} [CommRing R] {d : ℕ} (c : R) (A B : Matrix (Fin d) (Fin d) R)
    (h : ∀ i j, c ∣ B i j) (i j : Fin d) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _

theorem exists_mul_eq_smul_one : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣
      (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) →
    ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ d M τ Y hY hQ
  have hinj : Function.Injective (inclW l) :=
    WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  set A := Y.map (inclW l) with hA
  set c := inclW l τ ^ M with hc
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hY)
  set Z := c • A⁻¹ with hZ
  have hZent : ∀ i j, ∃ a : Ainf l, Z i j = inclW l (1 * a) := by
    intro i j
    refine GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by rw [map_one]; exact isUnit_one) 0 (Z i j) fun n => ?_
    obtain ⟨Q, hQn⟩ := hQ n
    have h1 := dvd_mul_entry _ A⁻¹ _ hQn i j
    have h2 : A⁻¹ * (A * Q.map (inclW l) - c • (1 : Matrix (Fin d) (Fin d) (WCb l))) =
        Q.map (inclW l) - Z := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hinvA, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [h2] at h1
    refine ⟨Q i j, ?_⟩
    rw [pow_zero, one_mul, one_mul, dvd_sub_comm]
    simpa [Matrix.sub_apply] using h1
  choose Y' hY' using hZent
  refine ⟨Matrix.of fun i j => Y' i j, ?_⟩
  have hmap : (Matrix.of fun i j => Y' i j).map (inclW l) = Z := by
    ext i j; simp [hY' i j]
  have key : (Y * Matrix.of fun i j => Y' i j).map (inclW l) =
      (τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))).map (inclW l) := by
    rw [Matrix.map_mul, hmap, hZ, Matrix.mul_smul, ← hA, hAinv]
    ext i j
    simp [Matrix.one_apply, hc, Matrix.smul_apply]
    split_ifs <;> simp
  refine Matrix.ext fun i j => hinj ?_
  exact congrFun (congrFun (congrArg Matrix.of.symm key) i) j

end GlobalTheory.AinfInvLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfRightInverseUpToPowModLPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfRinv

theorem rinv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (d d' n M : ℕ) (τ : Ainf l) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d') (Ainf l)) (Q : Matrix (Fin d') (Fin d) (Ainf l)), IsUnit (inclW l τ) → IsUnit (Y.map (inclW l)) → Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (A * Q).map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∀ i j, (l : Ainf l) ^ n ∣ (A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j := by
  intro l _ d d' n M τ Y Y' A Q hτ hY hYY' hdiv
  set f : Ainf l →+* WCb l := inclW l with hf
  let I : Ideal (WCb l) := Ideal.span {((l : WCb l)) ^ n}
  let π : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  let fW := (f.mapMatrix : Matrix (Fin d) (Fin d) (Ainf l) →+* Matrix (Fin d) (Fin d) (WCb l))
  let πM := (π.mapMatrix : Matrix (Fin d) (Fin d) (WCb l) →+* Matrix (Fin d) (Fin d) (WCb l ⧸ I))
  have hsm : ∀ {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : R),
      (φ.mapMatrix : Matrix (Fin d) (Fin d) R →+* Matrix (Fin d) (Fin d) S) (c • 1) = φ c • 1 := by
    intro R S _ _ φ c; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  set t : WCb l := f τ ^ M with ht
  have hfτ : fW (τ ^ M • 1) = t • 1 := by rw [hsm, map_pow]

  have h1 : fW Y * fW Y' = t • 1 := by rw [← map_mul, hYY', hfτ]
  obtain ⟨u, hu⟩ := hY
  have hYw : fW Y = (u : Matrix (Fin d) (Fin d) (WCb l)) := hu.symm
  have h2 : fW Y' * fW Y = t • 1 := by
    have e : fW Y' = (↑u⁻¹ : Matrix (Fin d) (Fin d) (WCb l)) * (fW Y * fW Y') := by
      rw [← Matrix.mul_assoc, hYw, Units.inv_mul, Matrix.one_mul]
    rw [e, h1, hYw, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

  set s : WCb l ⧸ I := π t with hs
  have hsu : IsUnit s := (hτ.pow M).map π
  have hmod : πM (fW Y * fW (A * Q) - t • 1) = 0 := by
    ext i j
    simp only [πM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hdiv i j))
  rw [map_sub, map_mul, hsm] at hmod
  have hYZ := sub_eq_zero.mp hmod
  have h2b : πM (fW Y') * πM (fW Y) = s • 1 := by rw [← map_mul, h2, hsm]
  have hZ : πM (fW (A * Q)) = πM (fW Y') := by
    have : s • πM (fW (A * Q)) = s • πM (fW Y') := by
      calc s • πM (fW (A * Q)) = (πM (fW Y') * πM (fW Y)) * πM (fW (A * Q)) := by
              rw [h2b, Matrix.smul_mul, Matrix.one_mul]
        _ = πM (fW Y') * (s • 1) := by rw [Matrix.mul_assoc, hYZ]
        _ = s • πM (fW Y') := by rw [Matrix.mul_smul, Matrix.mul_one]
    exact (hsu.smul_left_cancel).mp this
  have hfin : πM (fW (A * (Q * Y) - τ ^ M • 1)) = 0 := by
    rw [← Matrix.mul_assoc, map_sub, map_sub, map_mul, map_mul, hZ, h2b, hfτ, hsm, sub_self]
  intro i j
  have hij : π (f ((A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j)) = 0 := by
    have := congrFun (congrFun hfin i) j
    simpa [πM, fW, RingHom.mapMatrix_apply, Matrix.map_apply] using this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hij)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by simp) n w (fun _ => ⟨(A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j, by rw [one_mul, ← hw, sub_self]; exact dvd_zero _⟩)
  refine ⟨a, GlobalTheory.Prism.inclW_injective ?_⟩
  rw [one_mul] at ha
  rw [map_mul, map_pow, map_natCast, ← ha]
  exact hw

end GlobalTheory.AinfRinv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecompStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  first | exact @GlobalTheory.AmbWT.main | exact GlobalTheory.AmbWT.main | (intros; apply GlobalTheory.AmbWT.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatingLatticesTransitionMatrixModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.TransLim

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∃ Y : ∀ n, Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S, ∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR
  have key : ∀ n, ∃ Y : Matrix (Fin (tw.d' n)) (Fin (tw.d' (n + 1))) bk.S,
      (F n).T * Y.map bk.evW = zW (tw.f n) * (F (n + 1)).T := fun n =>
    _root_.GlobalTheory.BKLim.EquivKisin.main l K bk τ hτ N N (tw.d' (n + 1)) (tw.d' n) (fun g => (tw.ρ' (n + 1) g).val)
      (fun g => (tw.ρ' n g).val) (F (n + 1)) (F n) (tw.f n) (tw.f_equi n)
  choose Y hY using key
  refine ⟨Y, fun n => ?_⟩
  let π : WCb l →+* WCb l ⧸ Ideal.span {(l : WCb l) ^ n} := Ideal.Quotient.mk _
  have hz : ∀ {a b : ℕ} (M M' : Matrix (Fin a) (Fin b) (WCb l)),
      (∀ i j, (l : WCb l) ^ n ∣ (M - M') i j) ↔ M.map π = M'.map π := by
    intro a b M M'
    constructor
    · intro h
      ext i j
      simp only [Matrix.map_apply]
      rw [← sub_eq_zero, ← map_sub]
      exact (Ideal.Quotient.eq_zero_iff_dvd _ _).2 (by simpa [Matrix.sub_apply] using h i j)
    · intro h i j
      rw [Matrix.sub_apply]
      refine (Ideal.Quotient.eq_zero_iff_dvd _ _).1 ?_
      rw [map_sub, sub_eq_zero]
      exact congrFun (congrFun h i) j
  have hA : (zW (tw.Pi n)).map π * (F n).T.map π = T0.map π * (R n).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]; exact (hz _ _).1 (hR n)
  have hD : (zW (tw.Pi (n + 1))).map π * (F (n + 1)).T.map π = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (hR (n + 1) i j)
  have hB : (F n).T.map π * ((Y n).map bk.evW).map π = (zW (tw.f n)).map π * (F (n + 1)).T.map π := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hY n]
  have hC : (zW (tw.Pi n)).map π * (zW (tw.f n)).map π = (zW (tw.Pi (n + 1))).map π := by
    rw [← Matrix.map_mul]
    refine (hz _ _).1 fun i j => ?_
    have h1 := map_dvd (algebraMap ℤ_[l] (WCb l)) (tw.f_Pi n i j)
    simp only [map_pow, map_natCast] at h1
    convert h1 using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [zW, Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sum, map_mul]
  obtain ⟨u, hu⟩ := hT0
  have hinv : ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * T0.map π = 1 := by
    rw [← Matrix.map_mul, ← hu, Units.inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]
  have hE : T0.map π * ((R n).map π * ((Y n).map bk.evW).map π) = T0.map π * (R (n + 1)).map π := by
    rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hC, hD]
  have hF : (R n).map π * ((Y n).map bk.evW).map π = (R (n + 1)).map π := by
    have := congrArg (fun M => ((u⁻¹ : (Matrix (Fin d) (Fin d) (WCb l))ˣ) : Matrix (Fin d) (Fin d) (WCb l)).map π * M) hE
    simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
  rw [← Matrix.map_mul] at hF
  exact (hz _ _).2 hF

end GlobalTheory.BKLim.TransLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC

namespace GlobalTheory.DefiniteBCFrozen

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

theorem isBC_of_isBaseChange {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {B : NBC A} {j : ℕ} {π : B.AU j} {Pa : List (Part A.CG)}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.IsBaseChange B j π Pa) : SphericalInertData.IsBC N A B j π Pa := by
  refine ⟨fun p hp => ⟨(h.discrete p hp).1, (h.discrete p hp).2, h.conjSelfDual p hp⟩, ?_, h.rank, h.split,
    h.inert, h.inf⟩
  refine h.distinct.map ?_
  rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ hh
  simp only [Prod.mk.injEq, Sigma.mk.injEq] at hh
  obtain ⟨⟨rfl, h2⟩, rfl⟩ := hh
  cases h2
  rfl

end GlobalTheory.DefiniteBCFrozen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  exact @GlobalTheory.BKGal.JumpDR.basis_images
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCocycle

variable {l : ℕ} {R : Type} [CommRing R]

theorem comp_assoc {P P' P'' P''' : Obj l R} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P') :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem comp_id {P P' : Obj l R} (f : Hom P P') : f.comp (Hom.id P) = f := Hom.ext' rfl

theorem map_comp {P P' P'' : Obj l R} {d : ℕ} (ε : Matrix (Fin d) (Fin d) P.A) (g : Hom P' P'') (f : Hom P P') :
    ε.map (g.comp f).f = (ε.map f.f).map g.f := by
  rw [Matrix.map_map]; rfl

theorem unit_of_codiag {P Q B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (h1 : ∀ Δ : Hom Q P, Δ.comp inl = Δ.comp inr → ε.map Δ.f = 1)
    (k : Hom Q B) (hk : k.comp inl = k.comp inr) : ε.map k.f = 1 := by
  obtain ⟨Δ, ⟨hΔl, hΔr⟩, -⟩ := univ P (Hom.id _) (Hom.id _)
  have hk' : k = (k.comp inl).comp Δ := by
    refine (univ B (k.comp inl) (k.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔl).trans (comp_id _))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔr).trans ((comp_id _).trans hk))
  calc ε.map k.f = ε.map ((k.comp inl).comp Δ).f := congrArg (fun k : Hom Q B => ε.map k.f) hk'
    _ = (ε.map Δ.f).map (k.comp inl).f := map_comp ε _ Δ
    _ = (1 : Matrix (Fin d) (Fin d) P.A).map (k.comp inl).f :=
        congrArg (fun M : Matrix (Fin d) (Fin d) P.A => M.map (k.comp inl).f) (h1 Δ (hΔl.trans hΔr.symm))
    _ = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cocycle_of_triple {P Q Q₂ B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (i₁ : Hom Q Q₂) (j : Hom P Q₂)
    (univ₂ : ∀ (C : Obj l R) (f : Hom Q C) (g : Hom P C), ∃! h : Hom Q₂ C, h.comp i₁ = f ∧ h.comp j = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (hc : ∀ k₂₃ k₁₃ : Hom Q Q₂, i₁.comp inr = k₂₃.comp inl → i₁.comp inl = k₁₃.comp inl →
      k₂₃.comp inr = k₁₃.comp inr → ε.map i₁.f * ε.map k₂₃.f = ε.map k₁₃.f)
    (k₁ k₂ k₃ : Hom Q B) (h12 : k₁.comp inr = k₂.comp inl) (h13 : k₁.comp inl = k₃.comp inl)
    (h23 : k₂.comp inr = k₃.comp inr) : ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  obtain ⟨k₂₃, ⟨h₂₃l, h₂₃r⟩, -⟩ := univ Q₂ (i₁.comp inr) j
  obtain ⟨k₁₃, ⟨h₁₃l, h₁₃r⟩, -⟩ := univ Q₂ (i₁.comp inl) j
  have hc' := hc k₂₃ k₁₃ h₂₃l.symm h₁₃l.symm (h₂₃r.trans h₁₃r.symm)
  obtain ⟨m, ⟨hml, hmr⟩, -⟩ := univ₂ B k₁ (k₂.comp inr)
  have e₂ : k₂ = m.comp k₂₃ := by
    refine (univ B (k₂.comp inl) (k₂.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inr) hml).trans h12)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃r).trans hmr)
  have e₃ : k₃ = m.comp k₁₃ := by
    refine (univ B (k₃.comp inl) (k₃.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inl) hml).trans h13)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃r).trans (hmr.trans h23))
  subst e₂ e₃ hml
  rw [map_comp ε m i₁, map_comp ε m k₂₃, map_comp ε m k₁₃, ← Matrix.map_mul, hc']

theorem unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
      ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
        k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hrel B
  have cocB := _root_.GlobalTheory.BSP.height_rel_unit_cocycle l K bk d ρ τ s ht En ε hrel
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  refine ⟨unit_of_codiag En.inl En.inr En.univ ε
    (fun Δ h => (cocB bk.prism (Hom.id _) Unit (TopBasis.self bk.J)).1 Δ h), fun k₁ k₂ k₃ h12 h13 h23 => ?_⟩
  exact (_root_.GlobalTheory.BSP.nonempty_env l K bk En.Q _ _ (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)).elim fun En₂ =>
    (_root_.GlobalTheory.BSP.envelopes_topBasis l K bk En En₂).2.elim fun ι htb => htb.elim fun tb =>
      cocycle_of_triple En.inl En.inr En.univ En₂.inl En₂.inr En₂.univ ε
        (fun k₂₃ k₁₃ a b c => (cocB En₂.Q (En₂.inl.comp En.inl) ι tb).2 En₂.inl k₂₃ k₁₃ a b c)
        k₁ k₂ k₃ h12 h13 h23

end GlobalTheory.BSP.StratCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLawStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnWhittakerTransform_keeps_later_law : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ k, m + 1 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a k) y) * colT ψ (m + 1) f g := by
  first | exact @GlobalTheory.CuspGeneric.colT_law_of_good | exact GlobalTheory.CuspGeneric.colT_law_of_good | (intros; apply GlobalTheory.CuspGeneric.colT_law_of_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamily
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_avg_of_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ (X : Type) [TopologicalSpace X] (F : X × G → ℂ), Continuous F →
      (∀ x, ∀ γ ∈ Γ, ∀ y, F (x, γ + y) = F (x, y)) → Continuous fun x => avg Γ (fun y => F (x, y)) := by
  intro G _ _ _ _ _ _ Γ hΓ X _ F hF hper
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩

  obtain ⟨μ, D, hμ, hD, hD1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one G Γ hΓ
  have hsec : ∀ x : X, Continuous fun y : G => F (x, y) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hfacts : ∀ x : X, μ D ≠ 0 ∧ μ D ≠ ⊤ ∧ IntegrableOn (fun y => F (x, y)) D μ ∧
      ∫ y in D, F (x, y) ∂μ = ((μ D).toReal : ℂ) * avg Γ (fun y => F (x, y)) := fun x =>
    _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg G Γ hΓ μ D hμ hD (fun y => F (x, y)) ⟨hsec x, fun γ hγ y => hper x γ hγ y⟩

  have hrepr : (fun x => avg Γ (fun y => F (x, y))) = fun x => ∫ y in D, F (x, y) ∂μ := by
    funext x
    rw [(hfacts x).2.2.2, hD1]
    simp
  rw [hrepr]
  obtain ⟨-, K, hK, hcov⟩ := hΓ
  rw [Metric.continuous_iff']
  intro x₀ ε hε

  have hnear : ∀ᶠ x in nhds x₀, ∀ k ∈ K, dist (F (x, k)) (F (x₀, k)) < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    have h1 : ∀ᶠ z : X × G in nhds (x₀, k), dist (F z) (F (x₀, k)) < ε / 4 :=
      Metric.tendsto_nhds.mp (hF.tendsto (x₀, k)) _ (by positivity)
    have h2 : ∀ᶠ z : X × G in nhds (x₀, k), dist (F (x₀, z.2)) (F (x₀, k)) < ε / 4 :=
      Metric.tendsto_nhds.mp (((hsec x₀).comp continuous_snd).tendsto (x₀, k)) _ (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F (z.1, z.2)) (F (x₀, z.2))
        ≤ dist (F (z.1, z.2)) (F (x₀, k)) + dist (F (x₀, z.2)) (F (x₀, k)) :=
          dist_triangle_right _ _ _
      _ < ε / 4 + ε / 4 := add_lt_add hz1 hz2
      _ = ε / 2 := by ring
  filter_upwards [hnear] with x hx

  have hall : ∀ y : G, ‖F (x, y) - F (x₀, y)‖ ≤ ε / 2 := by
    intro y
    obtain ⟨γ, hγ, hγK⟩ := hcov y
    rw [← hper x γ hγ y, ← hper x₀ γ hγ y, ← dist_eq_norm]
    exact (hx _ hγK).le
  rw [dist_eq_norm, ← integral_sub (hfacts x).2.2.1 (hfacts x₀).2.2.1]
  calc ‖∫ y in D, (F (x, y) - F (x₀, y)) ∂μ‖ ≤ ε / 2 * μ.real D :=
        norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr (hfacts x).2.1)
          fun y _ => hall y
    _ = ε / 2 := by simp [Measure.real, hD1]
    _ < ε := half_lt_self hε

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameHeightOfJumpsLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N N₀ d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ), F.IsDR → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → ∃ F₀ : Frame bk N₀ d ρ, F₀.T = F.T ∧ F₀.ε = F.ε := by
  first | (exact @GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (exact GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le) | (intros; apply GlobalTheory.BKLim.Lower.exists_frame_of_jumps_le  <;> assumption)
end

