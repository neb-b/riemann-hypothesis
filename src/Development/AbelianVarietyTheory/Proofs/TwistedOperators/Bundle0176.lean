module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.LocalFromCover

theorem trace_conj {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ
  have hJ := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  have h2 := congrArg (fun A => (A * Jm p q).trace) h
  simp only [add_mul, Matrix.trace_add, zero_mul, Matrix.trace_zero] at h2
  rw [mul_assoc, hJ, mul_one, Matrix.trace_mul_comm, ← mul_assoc, hJ, one_mul, Matrix.trace_conjTranspose] at h2
  exact eq_neg_of_add_eq_zero_left h2

theorem trace_reindex' {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) : (Matrix.reindex e e Z).trace = Z.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp fun a => Z a a

theorem exp_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • plainMat e Z) = plainMat e (NormedSpace.exp (t • Z)) := by
  have h : t • plainMat e Z = Matrix.reindex e e (t • Z) := by
    ext a b; simp [plainMat]
  rw [h]
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) (t • Z)).symm

theorem exp_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • barMat e Z) = barMat e (NormedSpace.exp (t • Z)) := by
  have h0 : ∀ A : Mat p q, A.map (starRingEnd ℂ) = Aᴴᵀ := fun A => by ext a b; simp
  have h1 := exp_plainMat e (Z.map (starRingEnd ℂ)) t
  have h2 : t • Z.map (starRingEnd ℂ) = (t • Z)ᴴᵀ := by ext a b; simp
  rw [h2, Matrix.exp_transpose, Matrix.exp_conjTranspose, ← h0] at h1
  exact h1

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

theorem fr_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : M.fr τ * toFrame M τ Y * (M.fr τ)⁻¹ = Y := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc,
    Matrix.mul_nonsing_inv _ hd, mul_one]

theorem trace_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (toFrame M τ Y).trace = Y.trace := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]

theorem rep_exp (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    M.rep τ (NormedSpace.exp (t • toFrame M τ Y)) = M.σ τ (NormedSpace.exp (t • Y)) := by
  rw [DSModel.rep, ← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul, fr_toFrame]

variable {M τ}

theorem matches_exp {p q : ℕ} {T : GrpData p q} {R : DSRep T}
    {φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ} {m : ℤ} {U : M.H τ → R.U.H} (h : Matches R M τ φ m U)
    (hφ : ∀ (Z : Mat p q) (t : ℝ), NormedSpace.exp (t • φ Z) = φ (NormedSpace.exp (t • Z)))
    {Z : Mat p q} (hZ : Z ∈ upq p q) (t : ℝ) (x : M.H τ) :
    U (M.rep τ (NormedSpace.exp (t • toFrame M τ (φ Z))) x) =
      ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m • R.U.π (T.expt (t • Z)) (U x) := by
  rw [rep_exp, hφ, h.grp, T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), smul_smul,
    ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]

theorem hasDerivAt_sq_zpow {p q : ℕ} (T : GrpData p q) (m : ℤ) {Z : Mat p q} (hZ : Z ∈ upq p q) :
    HasDerivAt (fun t : ℝ => ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m) (m * (Z.trace / 2)) 0 := by
  have h3 := (hasDerivAt_zpow m _ (.inl (Units.ne_zero _))).comp (0 : ℝ)
    (GlobalTheory.RealPar.Cover.hasDerivAt_sq (T := T) hZ)
  refine h3.congr_deriv ?_
  simp [T.expt_zero]

theorem exists_locIt (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) (hm : (m : ℚ) = 2 * aT) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hN : Nontrivial R₂.HK.V) (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (hB : IsCoverIt R₁ R₂ B) :
    ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  let A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ :=
    LinearMap.mk₂ ℂ (fun P y => U.symm (B (κ P) (U' y)))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [LinearIsometryEquiv.map_smulₛₗ, LinearMap.map_smulₛₗ])
  have hA : ∀ P y, A P y = U.symm (B (κ P) (U' y)) := fun _ _ => rfl
  have hmC : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  refine ⟨A, fun P y => ?_, ?_, fun P w => ?_, ?_, ?_⟩
  · refine Submodule.subset_span (h₁.smooth _ ?_)
    rw [hA, U.apply_symm_apply]
    exact hB.kfin _ _
  · obtain ⟨v, hv⟩ := exists_ne (0 : R₂.HK.V)
    obtain ⟨P, hP⟩ := hB.ne (R₂.ι v) fun h0 => hv (R₂.ι_inj (by rw [h0, map_zero]))
    refine ⟨κ.symm P, U'.symm (R₂.ι v), Submodule.subset_span (h₂.smooth _ ?_), ?_⟩
    · rw [U'.apply_symm_apply]; exact ⟨v, rfl⟩
    · rw [hA, U'.apply_symm_apply, κ.apply_symm_apply]
      intro h0
      exact hP (U.symm.injective (by rw [h0, map_zero]))
  · haveI : CompleteSpace (M'.H τ) := U'.toIsometryEquiv.completeSpace
    obtain ⟨c, hc⟩ := hB.bdd (κ P)
    let L : M'.H τ →L[ℂ] M.H τ := (A P).mkContinuous c fun y => by
      rw [hA, U.symm.norm_map, ← U'.norm_map y]; exact hc _
    refine ⟨(InnerProductSpace.toDual ℂ (M'.H τ)).symm ((innerSL ℂ w).comp L), fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  · intro X hX P y
    rw [← h₁.lie] at hX
    obtain ⟨Z, hZ, rfl⟩ := hX
    have h1 := (hasDerivAt_sq_zpow T₁ m hZ).fun_smul (hB.src Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h3 : (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by ext a b; simp [barMat]
    have h4 : (barMat e Z).trace = -Z.trace := by
      rw [barMat, trace_reindex', ← trace_conj hZ]
      simp [Matrix.trace]
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      apply U.injective
      rw [matches_exp h₁ (exp_barMat e) hZ, hA]
      simp
    · rw [hA, fr_toFrame, trace_toFrame, h3, h4, map_sub, map_smul, hκ.1, hmC,
        show 2 * (aT : ℂ) * (Z.trace / 2) = aT * Z.trace by ring]
      simp [T₁.expt_zero]
  · intro Y hY P y
    rw [← h₂.lie] at hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    have h1 := (hasDerivAt_sq_zpow T₂ m' hZ).star.fun_smul (hB.tgt Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h4 : (plainMat e' Z).trace = Z.trace := trace_reindex' e' Z
    have h5 : star ((m' : ℂ) * (Z.trace / 2)) = -((aS : ℂ) * Z.trace) := by
      rw [Complex.star_def, map_mul, map_intCast, map_div₀, trace_conj hZ, map_ofNat, hmC']
      ring
    convert (preTransparency := .reducible) h2 using 1
    · funext t
      rw [hA, matches_exp h₂ (exp_plainMat e') hZ, LinearMap.map_smulₛₗ]
      rfl
    · rw [h5, hA, fr_toFrame, trace_toFrame, h4, map_add (f := _), map_smul, plainMat, hκ.2]
      simp [T₂.expt_zero]
      abel

end GlobalTheory.Chain.RealIt.LocalFromCover

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryRep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.RowsPosRed

theorem exists_unitary_rep {K G V H E : Type} [Field K] [StarRing K] [Group G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup E] [Module ℂ E] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    {ι : Type} (b : Module.Basis ι K V) (hli : LinearIndependent ℂ fun k => j (b k))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hiso : ∀ x y, ⟪j x, j y⟫_ℂ = σ (h x y)) (r : Representation K G V) (hr : ∀ g x y, h (r g x) (r g y) = h x y)
    (Θ : H →ₗ[ℂ] E) (π : Representation ℂ G E) (hΘ : ∀ g z, Θ (j (r g z)) = π g (Θ (j z))) :
    ∃ ρ : Representation ℂ G H, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, Θ (ρ g y) = π g (Θ y) := by
  let B : Module.Basis ι ℂ H := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = j (b k) := fun k => Module.Basis.mk_apply hli hsp.ge k
  let f : G → Module.End ℂ H := fun g => B.constr ℂ fun k => j (r g (b k))
  have hf : ∀ g z, f g (j z) = j (r g z) := by
    intro g z
    have : (f g).comp j = j.comp (r g) := b.ext fun k => by
      show f g (j (b k)) = j (r g (b k))
      rw [← hB]
      exact B.constr_basis ℂ _ k
    exact LinearMap.congr_fun this z
  let ρ : Representation ℂ G H :=
    { toFun := f
      map_one' := B.ext fun k => by
        show f 1 (B k) = B k
        rw [hB, hf, map_one, Module.End.one_apply]
      map_mul' := fun g g' => B.ext fun k => by
        show f (g * g') (B k) = f g (f g' (B k))
        rw [hB, hf, hf, hf, map_mul, Module.End.mul_apply] }
  have hρ : ∀ g z, ρ g (j z) = j (r g z) := hf
  have hin : ∀ g y y', ⟪ρ g y, ρ g y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
    intro g
    have h1 : ∀ k y', ⟪ρ g (B k), ρ g y'⟫_ℂ = ⟪B k, y'⟫_ℂ := by
      intro k
      have : (innerₛₗ ℂ (ρ g (B k))).comp (ρ g) = innerₛₗ ℂ (B k) := B.ext fun l => by
        show ⟪ρ g (B k), ρ g (B l)⟫_ℂ = ⟪B k, B l⟫_ℂ
        rw [hB, hB, hρ, hρ, hiso, hiso, hr]
      exact fun y' => LinearMap.congr_fun this y'
    intro y y'
    have : (innerₛₗ ℂ (ρ g y)).comp (ρ g) = innerₛₗ ℂ y := B.ext fun l => by
      show ⟪ρ g y, ρ g (B l)⟫_ℂ = ⟪y, B l⟫_ℂ
      rw [← inner_conj_symm, h1, inner_conj_symm]
    exact LinearMap.congr_fun this y'
  refine ⟨ρ, fun g z => (hρ g z).symm, fun g y => ?_, fun g => ?_⟩
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  · have : Θ.comp (ρ g) = (π g).comp Θ := B.ext fun k => by
      show Θ (ρ g (B k)) = π g (Θ (B k))
      rw [hB, hρ, hΘ]
    exact fun y => LinearMap.congr_fun this y

end GlobalTheory.RowsPosRed

namespace GlobalTheory.RowsPosRed

open Formalism.IndefR.Cx.CxData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_idem_gEx (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) (x : (R.toCx3 F).EE) :
    ∑ g, A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x = x := by
  have h := GlobalTheory.AdjGood.proj_rows_core hC (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)
  have e : ∀ g, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
      (A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x) =
      D.what₂.embLL ((idemOf A3.A.X).coeff g) • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
    intro g
    have hc : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) =
        D.what₂.embLL ((idemOf A3.A.X).coeff g) := by
      rw [R.emb0, cj_cj]
    exact congrArg (fun z : ℂ => z • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)) hc
  exact (Finset.sum_congr rfl fun g _ => e g).trans h

theorem range_le_span_rat {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    (X : CxData A) (cv : CrdV A) (hK : X.KFormR) (hJ : X.JIsoR cv) (hT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) :
    LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤
      Submodule.span ℂ (X.jR t '' {z | X.jR t z ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))}) := by
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  exact (Formalism.IndefR.Rat.range_adjoint_rat _ (X.jR t) (cv.hR t) (bR t) (hK t).1 (hK t).2 (hJ t) (X.Θ t) ψ hψ
    (fun i x => hr t i x)).ge

theorem exists_rho (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hM : R.toRealDat.IsModels)
    (hGE : R.PGEquiv F) :
    ∃ ρ : Representation ℂ G ((R.toCx3 F).FC A3.A.fam.μ0),
      (∀ g z, (R.toCx3 F).jR A3.A.fam.μ0 ((A3.A.fam.R A3.A.fam.μ0).r g z) = ρ g ((R.toCx3 F).jR A3.A.fam.μ0 z)) ∧
      (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, (R.toCx3 F).Θ A3.A.fam.μ0 (ρ g y) = R.gEx F g ((R.toCx3 F).Θ A3.A.fam.μ0 y) := by
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hM
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hM
  exact exists_unitary_rep (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (H := (R.toCx3 F).FC A3.A.fam.μ0)
    ((R.toCx3 F).jR A3.A.fam.μ0) (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (hKR A3.A.fam.μ0).1
    (hKR A3.A.fam.μ0).2 (F.cv.hR A3.A.fam.μ0) (hJR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r
    (fun g x y => (hOk.ok2.what₂ A3.A.fam.μ0).act.unitary g x y) ((R.toCx3 F).Θ A3.A.fam.μ0) (R.gEx F)
    (fun g z => hGE.1 A3.A.fam.μ0 g z)

theorem exists_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hM : R.toRealDat.IsModels) (hN : RowsNe R.toRealDat F.lv2)
    (b : Bool) : ∃ u : (R.toCx3 F).EE, u ≠ 0 ∧ u ∈ (R.toCx3 F).EEl b := by
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 (hN b)
  have hT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R.toRealDat _ hU
  obtain ⟨y, rfl⟩ : U ∈ LinearMap.range R.HE.e := hM.HE.2.1 ▸ hT
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) y, fun h0 => hU0 ?_, hU⟩
  have : y = 0 := h0
  rw [this, map_zero]


omit [Fintype G] in
theorem tw_eq_zero {s : Bool} {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (f : E →ₗ[ℂ] E')
    (hf : Function.Injective (LinearMap.adjoint f)) (v : Tw s E') (h1 : ∀ y : Tw s E, ⟪Tw.map s f y, v⟫_ℂ = 0) : v = 0 := by
  have h5 : LinearMap.adjoint f (Tw.out v) = 0 := by
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    have h3 : cj s ⟪f y, Tw.out v⟫_ℂ = 0 := h1 (Tw.mk s y)
    have h4 := congrArg (cj s) h3
    rwa [cj_cj, map_zero] at h4
  exact hf (h5.trans (map_zero _).symm)

theorem surj_of_upInj (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hUp : UpInj R.toRealDat) (x : (R.toCx3 F).EE) :
    ∃ u, (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u) = x := by
  have hinj : ∀ v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v = 0 → v = 0 := by
    intro v hv
    have h1 : ∀ y : (R.toCx3 F).FC A3.A.fam.μ0, ⟪(R.toCx3 F).Θ A3.A.fam.μ0 y, v⟫_ℂ = 0 := fun y => by
      rw [← LinearMap.adjoint_inner_right, hv, inner_zero_right]
    exact tw_eq_zero (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.fam.μ0) (hUp A3.A.fam.μ0) v h1
  have h2 : Function.Injective ((R.toCx3 F).Θ A3.A.fam.μ0 ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h3 : ⟪LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      rw [LinearMap.comp_apply] at hv
      rw [hv, inner_zero_right]
    exact hinj v (inner_self_eq_zero.1 h3)
  exact LinearMap.injective_iff_surjective.1 h2 x

theorem dZ_pos_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hUp : UpInj R.toRealDat) (hGE : R.PGEquiv F) (hRT : Formalism.IndefR.Rat.RowTest (R.toCx3 F))
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (u : (R.toCx3 F).EE) (hu0 : u ≠ 0)
    (hu : u ∈ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) :
    0 < (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) := by
  have hM : R.toRealDat.IsModels := hC.base.models
  have hrat := range_le_span_rat (R.toCx3 F) F.cv (RealDat3.kFormR_of hM) (RealDat3.jIsoR_of hM) hRT A3.A.fam.μ0
  obtain ⟨ρ, hj, hρ, hΘ⟩ := exists_rho R F hOk hM hGE
  have hCore := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  have htype : ∀ h : P, R.gEx F (h : G) u = A3.A.fam.v0.embedding ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • u := by
    intro h
    have := (Submodule.mem_iInf _).1 hu h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨w, hw⟩ := surj_of_upInj R F hUp u
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.RowsNonzero.exists_rational ((R.toCx3 F).jR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r ρ
    (R.gEx F) ((R.toCx3 F).Θ A3.A.fam.μ0) hj hρ hΘ hrat (fun g => (idemOf A3.A.X).coeff g)
    (fun g => (lvlIdem P ψ).coeff g) hu0 hw (sum_idem_gEx R F hCore u)
    (GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) P ψ htype)
  exact GlobalTheory.RowsNonzero.dZ_pos (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) hz0 hz

end GlobalTheory.RowsPosRed

theorem GlobalTheory.RowsPosRed.pos_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInj R.toRealDat → RowsNe R.toRealDat F.lv2 → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp hNe hGE _ hRT b
  have hel := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.RowsPosRed.exists_row R F hC.base.models hNe b
  cases b
  · rw [hel.1] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P0 F.ψ0 u hu0 hu
  · rw [hel.2] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P1 F.ψ1 u hu0 hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightBruhatFundamentalDomainCentralizer
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.WeightUnfold

theorem exists_weight (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H) (hcomm : IsMulCommutative (cent γ)) (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)) (hfd : IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt) :
    ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  have hTcl : IsClosed ((cent γ : Subgroup H) : Set H) := Set.isClosed_centralizer _
  have hc : ∀ a b : cent γ, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  haveI : LocallyCompactSpace (cent γ) := hTcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent γ => x * g) = (fun x => g * x) := funext fun x => hc x g
    rw [this]; exact map_mul_left_eq_self dt g⟩
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat (T := cent γ) hTcl dt
  have hprod : Measurable fun p : H × cent γ => β (((p.2 : cent γ) : H) * p.1) :=
    hβm.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
  have hsec : ∀ x : H, Measurable fun t : cent γ => β ((t : H) * x) := fun x =>
    hβm.comp (measurable_subtype_coe.mul_const x)
  refine ⟨fun y => ∫⁻ t in 𝓣, β ((t : H) * y) ∂dt, ?_, ?_, ?_⟩
  · exact hprod.lintegral_prod_right'
  · intro y
    haveI : Countable Γ := by
      haveI : TopologicalSpace.SeparableSpace Γ := inferInstance
      exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance
    haveI : Countable (Γ.subgroupOf (cent γ)) := by
      refine Function.Injective.countable (f := fun h : Γ.subgroupOf (cent γ) => (⟨((h : cent γ) : H), h.2⟩ : Γ)) ?_
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hab
    rw [← hβ y, hfd.lintegral_eq_tsum'' (fun t : cent γ => β ((t : H) * y))]
    refine tsum_congr fun h => lintegral_congr fun t => ?_
    congr 1
    have e : ((h • t : cent γ) : H) = ((h : cent γ) : H) * (t : H) := rfl
    rw [e, ← mul_assoc, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]
  · intro ψ hψm hψ
    haveI : dt.IsMulLeftInvariant := inferInstance
    have hq := isQuotMeasure_quotMeas (T := cent γ) dt μ hTcl

    have hinner : ∀ t : cent γ, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ = ∫⁻ y, β y * ψ y ∂μ := by
      intro t
      have : (fun y => β ((t : H) * y) * ψ y) = fun y => (fun z => β z * ψ z) ((t : H) * y) := by
        funext y; show _ = β _ * ψ _; rw [hψ (t : H) t.2 y]
      rw [this]; exact lintegral_mul_left_eq_self (fun z => β z * ψ z) (t : H)
    have hC : ∫⁻ y, β y * ψ y ∂μ = ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
      rw [hq (fun y => β y * ψ y) (hβm.mul hψm)]
      refine lintegral_congr fun q => ?_
      have : (fun t : cent γ => β ((t : H) * Quotient.out q) * ψ ((t : H) * Quotient.out q)) = fun t : cent γ => β ((t : H) * Quotient.out q) * ψ (Quotient.out q) := by
        funext t; rw [hψ (t : H) t.2]
      rw [this, lintegral_mul_const _ (hsec _), hβ, one_mul]
      rfl
    calc ∫⁻ y, (∫⁻ t in 𝓣, β ((t : H) * y) ∂dt) * ψ y ∂μ
        = ∫⁻ y, ∫⁻ t in 𝓣, β ((t : H) * y) * ψ y ∂dt ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_mul_const _ (hsec y)]
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ ∂dt := by
          refine lintegral_lintegral_swap ?_
          exact (hprod.mul (hψm.comp measurable_fst)).aemeasurable
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β y * ψ y ∂μ ∂dt := by
          refine lintegral_congr fun t => hinner t
      _ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
          rw [lintegral_const, Measure.restrict_apply_univ, hC, mul_comm]

end GlobalTheory.WeightUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdjAct

variable {D : D7}

theorem mt_mul_mt_inv (T : HSp D) (g : GA D T) : Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹ = 1 := by
  show (matHom T g).1 * (matHom T g⁻¹).1 = 1
  rw [map_inv]; exact (matHom T g).mul_inv

theorem mt_one_inv (S : HSp D) : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by
  show (matHom S 1⁻¹).1 = 1
  simp

theorem cT_mt_gram (T : HSp D) (g : GA D T) : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) =
    T.gram.map (incA D) * Formalism.L2.Theta.mt T g⁻¹ := by
  have hU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) * Formalism.L2.Theta.mt T g =
      T.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  calc _ = Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) *
        (Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹) := by rw [mt_mul_mt_inv, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hU]

theorem finE_inv_val (T : HSp D) (g : GA D T) :
    ((Formalism.IndefR.Lev.finE T g)⁻¹).1 = (Formalism.L2.Theta.mt T g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val {n : ℕ} (β y : GL (Fin n) (EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem conj_transpose_mul (S T : HSp D) (g : GA D T) (x : WO S T) :
    ((HMul.hMul (Formalism.L2.Theta.mt T g) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
        Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      HMul.hMul ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ
        (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g)) := by
  rw [Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem assoc_swap {R : Type} [CommRing R] {s t : ℕ} (A : Matrix (Fin s) (Fin s) R) (X : Matrix (Fin s) (Fin t) R)
    (C G N : Matrix (Fin t) (Fin t) R) (h : C * G = G * N) : A * (X * C) * G = A * X * G * N := by
  simp only [Matrix.mul_assoc]
  rw [h]

theorem frame_assoc {R : Type} [CommRing R] {s t : ℕ} (bS : Matrix (Fin s) (Fin s) R) (Y : Matrix (Fin s) (Fin t) R)
    (N bT bTi : Matrix (Fin t) (Fin t) R) (hb : bT * bTi = 1) :
    bS * (Y * N) * bT = bS * Y * bT * (bTi * N * bT) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc bT, hb, Matrix.one_mul]

theorem frMapAdj_actO : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D T) (x : WO S T), frMapAdj S T βS βT (actO S T 1 g x) = HMul.hMul (frMapAdj S T βS βT x) ((βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT)⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  intro D S T βS βT g x
  rw [frMapAdj, frMapAdj, actO, mt_one_inv, Matrix.mul_one, conj_transpose_mul, conj_inv_val, finE_inv_val,
    assoc_swap _ _ _ _ _ (cT_mt_gram T g), Matrix.map_mul]
  exact frame_assoc _ _ _ _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

end GlobalTheory.AdjAct
end
end

