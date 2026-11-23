module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderTangentPointSmooth
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.TangentOrigin
open scoped CategoryTheory.Obj

namespace GlobalTheory.TanPt

theorem exists_coords_derivs' {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ (x : Fin D → A) (d : Fin D → A →+ A),
      (∀ c a b, d c (a * b) = a * d c b + b * d c a) ∧
      (∀ a c, d c (x a) = if a = c then 1 else 0) ∧ ∀ c r, d c (α r) = 0 := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ιv, σv, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ιv
  letI := Fintype.ofFinite σv
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ιv) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  let B := P.basisKaehler.reindex e
  have hB : ∀ i, KaehlerDifferential.D k A (P.val (e.symm i)) = B i := fun i => by
    simp [B]
  refine ⟨fun i => P.val (e.symm i), fun c =>
    { toFun := fun s => B.coord c (KaehlerDifferential.D k A s)
      map_zero' := by simp
      map_add' := fun s t => by simp }, fun c a b => ?_, fun a c => ?_, fun c r => ?_⟩
  · change B.coord c (KaehlerDifferential.D k A (a * b)) =
      a * B.coord c (KaehlerDifferential.D k A b) + b * B.coord c (KaehlerDifferential.D k A a)
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · change B.coord c (KaehlerDifferential.D k A (P.val (e.symm a))) = _
    rw [hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  · change B.coord c (KaehlerDifferential.D k A (algebraMap k A r)) = 0
    rw [Derivation.map_algebraMap, map_zero]

def jetVec {A K : Type} [CommRing A] [Field K] {D : ℕ} (φ : A →+* K) (d : Fin D → A →+ A)
    (hd : ∀ c a b, d c (a * b) = a * d c b + b * d c a) : A →+* TrivSqZeroExt K (Fin D → K) where
  toFun s := (φ s, fun c => φ (d c s))
  map_one' := by
    refine TrivSqZeroExt.ext (map_one φ) ?_
    funext c
    have h1 : d c 1 = 0 := by simpa using hd c 1 1
    change φ (d c 1) = 0
    rw [h1, map_zero]
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero φ) ?_
    funext c
    change φ (d c 0) = 0
    rw [map_zero, map_zero]
  map_add' s t := by
    refine TrivSqZeroExt.ext (map_add φ s t) ?_
    funext c
    change φ (d c (s + t)) = φ (d c s) + φ (d c t)
    rw [map_add (f := _), map_add (f := _)]
  map_mul' s t := by
    refine TrivSqZeroExt.ext (map_mul φ s t) ?_
    refine Eq.trans ?_ (TrivSqZeroExt.snd_mul _ _).symm
    funext c
    show φ (d c (s * t)) = (φ s • (fun c => φ (d c t)) + MulOpposite.op (φ t) • (fun c => φ (d c s))) c
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, hd c, map_add, map_mul, map_mul, mul_comm (φ (d c s))]

theorem evalPt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {x y : Sp R ⟶ X} (e : x = y) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) : evalPt x U hx f = evalPt y U hy f := by
  subst e; rfl

end GlobalTheory.TanPt

namespace GlobalTheory.TanPt

theorem exists_tangent_point : ∀ {o : Type} [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (K : Type) [Field K] (β : o →+* K) (x₀ : Sp K ⟶ X), x₀ ≫ s = spMap β → ∃ y : Sp (TrivSqZeroExt K (Fin D → K)) ⟶ X, spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ y = x₀ ∧ y ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin D → K))).comp β) ∧ ∀ mu : (Fin D → K) →ₗ[K] K, spMap (dirMap mu) ≫ y = constPt (spMap (dirMap mu) ≫ y) → mu = 0 := by
  intro o _ Y p D hsm K _ β z hz
  haveI := hsm
  obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (GlobalTheory.Adelic.ptOf z))
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨S, hS, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (S : Set Γ(Y, V)), GlobalTheory.Adelic.ptOf z ∈ Y.basicOpen (t : Γ(Y, V)) :=
    TopologicalSpace.Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hS).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← GlobalTheory.TopForm.resG_comp_algX (p := p) (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨x, d, hl, hd, h0⟩ := exists_coords_derivs' h₂
  have hO : IsAffineOpen (Y.basicOpen (t : Γ(Y, V))) := IsAffineOpen.basicOpen hV _
  have hzO : ⊤ ≤ z ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := (GlobalTheory.Adelic.le_iff_ptOf_mem z _).2 hxt
  obtain ⟨w, hw, he⟩ := exists_evalPt_eq hO (jetVec (evalPt z _ hzO) d hl)
  refine ⟨w, ?_, ?_, fun mu hmu => ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    refine ext_evalPt hO h' hzO (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ w _ hw h' f).trans ?_
    rw [he]
    rfl
  · refine eq_spMap_of_evalPt _ _ fun a => ?_
    rw [← evalPt_constFn p w _ hw a, he]
    have hza : evalPt z _ hzO (constFn p (Y.basicOpen (t : Γ(Y, V))) a) = β a := by
      rw [evalPt_constFn]
      exact (evalPt_congr hz (⊤ : (Sp o).Opens) _ le_rfl _).trans (evalPt_spMap β a)
    refine TrivSqZeroExt.ext ?_ ?_
    · exact hza
    · funext c
      change evalPt z _ hzO (d c (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p _ a)) = _
      rw [h0 c a, map_zero]
      rfl
  · refine (Pi.basisFun K (Fin D)).ext fun a => ?_
    have h1 : ⊤ ≤ (spMap (dirMap mu) ≫ w) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have h2 : ⊤ ≤ (constPt (spMap (dirMap mu) ≫ w)) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) :=
      fun q _ => hw (Set.mem_univ _)
    have h3 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have e := congrArg TrivSqZeroExt.snd (evalPt_congr hmu _ h1 h2 (x a))
    have e2 : (evalPt (constPt (spMap (dirMap mu) ≫ w)) _ h2 (x a)).snd = 0 := by
      rw [evalPt_congr (show constPt (spMap (dirMap mu) ≫ w) = spMap (algebraMap K (DualNumber K)) ≫
        (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) from rfl) _ h2 h2,
        evalPt_spMap_comp _ _ _ h3 h2]
      rfl
    rw [e2, evalPt_spMap_comp _ w _ hw h1, he] at e
    have hv : (fun c => evalPt z _ hzO (d c (x a))) = Pi.basisFun K (Fin D) a := by
      funext c
      rw [hd, Pi.basisFun_apply]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Pi.single_apply, Ne.symm hac]
    rw [LinearMap.zero_apply, ← hv]
    rw [dirMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.snd_map] at e
    exact e

end GlobalTheory.TanPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp

theorem fdgram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [RCLike.star_def]
  ring

theorem permM_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) :
    (permM e)ᴴ * M * permM e = M.submatrix e.symm e.symm := by
  ext a b
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← e.symm.sum_comp]
  simp

theorem jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)) := by
  rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, ← Matrix.diagonal_neg]
  rfl

theorem sumElim_sgn {p q r : ℕ} (hcard : r = q + p) (a : Fin r) :
    Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)
        (((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a) =
      -(((sgn q (a : ℕ) : ℝ)) : ℂ) := by
  by_cases h : (a : ℕ) < q
  · have ha : finCongr hcard a = Fin.castAdd p ⟨a, h⟩ := Fin.ext rfl
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inr ⟨a, h⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [hv]
    simp [sgn, h]
  · have hlt := a.isLt
    have ha : finCongr hcard a = Fin.natAdd q ⟨(a : ℕ) - q, by omega⟩ := Fin.ext (by simp; omega)
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inl ⟨(a : ℕ) - q, by omega⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [hv]
    simp [sgn, h]

theorem exists_frame_of_sig {n p q : ℕ} {Gc : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature Gc p q)
    {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq p q * A = Gc) :
    ∃ (e : Fin p ⊕ Fin q ≃ Fin n) (x : Matrix (Fin n) (Fin n) ℂ), x.det ≠ 0 ∧ A * x = permM e ∧
      (-(xᴴ * Gc * x))ᵀ = Matrix.diagonal fun a : Fin n => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨L, hl, hr⟩ := GlobalTheory.DecompCompare.frame_inv h hA
  obtain ⟨e0, -⟩ := h
  have hcard : n = q + p := by
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  set π : Fin n ≃ Fin p ⊕ Fin q :=
    (finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p))) with hπ
  have hAx : A * (L * permM π.symm) = permM π.symm := by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  refine ⟨π.symm, L * permM π.symm, ?_, hAx, ?_⟩
  · have h1 : (L * permM π.symm) * ((permM π.symm)ᵀ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permM π.symm), permM_mul_transpose, Matrix.one_mul, hl]
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  · have key : ∀ y : Matrix (Fin n) (Fin n) ℂ, yᴴ * Gc * y = (A * y)ᴴ * Formalism.UG.Jpq p q * (A * y) := fun y => by
      rw [← hA, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [key, hAx, permM_conj, Equiv.symm_symm, jpq_eq_diagonal, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_neg, Matrix.diagonal_transpose]
    congr 1
    funext a
    rw [Function.comp_apply, hπ, sumElim_sgn hcard a, neg_neg]

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem exists_ident_frame : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) →
    ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank)
      (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank),
      X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧
        IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  intro D V P Q hV hs A hA
  choose e x hdet hAx hg using fun ρ => exists_frame_of_sig (hV (tauE D ρ)) (hA ρ)
  have hrk : V.rank = Q + P := by
    have h := hV D.host.φ₀
    rw [hs] at h
    obtain ⟨e0, -⟩ := h
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  have hmapT : ∀ ρ, ((-(V.gram)ᵀ).map (tauE D ρ))ᵀ = -(gramAt D V ρ) := fun ρ => by
    ext a b
    simp [gramAt]
  have hgr : ∀ ρ, ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(V.gram)ᵀ) (x ρ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn Q (a : ℕ) : ℝ) : ℂ) := fun ρ => by
    have h1 := hg ρ
    simp only [hs] at h1
    rw [fdgram_eq, hmapT, Matrix.mul_neg, Matrix.neg_mul]
    exact h1
  have hin : ∀ ρ, tauE D ρ ∈ Formalism.L2.Pj.cmTypeOfSqrt D := fun ρ => by
    rw [Formalism.L2.Pj.mem_cm_type_iff, Formalism.L2.Theta.tauE_sqrtMinusD]
    exact (D.host.φ₀_mem).symm
  have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ Formalism.L2.Pj.cmTypeOfSqrt D ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, hρ⟩ => hρ ▸ hin ρ⟩
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h' | h'
    · exact ⟨ρ, h'.symm⟩
    · exact absurd (h' ▸ h) ((Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D _).1 (hin ρ))
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).1 (by simp only [h])
  obtain ⟨hh, hd, hfg, hsp, -⟩ := GlobalTheory.Member.selfDualLat_neg_gram_transpose D V
  obtain ⟨n, hn, hnint⟩ := GlobalTheory.PrincData.exists_nat_herm_int (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hfg
  obtain ⟨k, hk, hkint⟩ := GlobalTheory.PrincData.exists_nat_int (-(2 * D.host.xi0))
  obtain ⟨X, hΨ, hG, hp, -, -, -, -, -, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E V.rank Q 3
    (3 * n * k) (Formalism.L2.Pj.cmTypeOfSqrt D) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) D.host.xi0 (-(2 * D.host.xi0))
    (Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D) hh hd (by omega)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      exact ⟨x ρ, hdet ρ, hgr ρ⟩)
    hfg hsp le_rfl (Formalism.L2.Pj.conj_xi0_alt D)
    (by
      obtain ⟨ρ, -⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk D.host.φ₀)
      intro h
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      rw [h] at h1
      simp at h1)
    (Or.inr rfl)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      simp [map_ofNat]
      linarith)
    (by positivity)
    (fun u hu v hv => by
      have e1 : ((3 * n * k : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) * (-(2 * D.host.xi0)) *
          ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v =
          ((k : D.host.E) * (-(2 * D.host.xi0))) * ((n : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v) := by
        push_cast
        field_simp
      rw [e1]
      exact hkint.mul (hnint u hu v hv))
  let σ : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, by rw [hΨ]; exact hin ρ⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hmem τ.1).1 (hΨ ▸ τ.2)
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  refine ⟨X, σ, fun τ => x (σ.symm τ), e, hG, fun ρ => rfl, fun τ => ?_, fun ρ => ⟨?_, ?_⟩⟩
  · have hτ : τ.1 = tauE D (σ.symm τ) := (congrArg Subtype.val (σ.apply_symm_apply τ)).symm
    show ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (x (σ.symm τ)) = _
    rw [hG, hp, hτ]
    exact hgr _
  · rw [hA ρ, hG]
    show gramAt D V ρ = -((-(V.gram)ᵀ).map (tauE D ρ))ᵀ
    rw [hmapT, neg_neg]
  · show A ρ * x (σ.symm (σ ρ)) = permM (e ρ)
    rw [σ.symm_apply_apply]
    exact hAx ρ

end GlobalTheory.CovTop.VolUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameChangeEigenframeExponentialsHolArc
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.ShFam.BdArc

open GlobalTheory.HolHom GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections LatSec

theorem exists_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), IsArc Z σ φ x ψ r → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ h : ℂ → (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), ∀ u ∈ Metric.ball (0 : ℂ) ρ, (h u).IsInvertible ∧ ContinuousAt (fun u => (h u).inverse) u ∧ ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = e' u (h u z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  have hA : ∀ u ∈ Metric.ball (0 : ℂ) ρ, HolAt (fun z => (e' u z).left) 0 := fun u hu =>
    holAt_of_isHolTo (hexp u hu).2.2.1 trivial
  have hh : ∀ u, ∃ h : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), u ∈ Metric.ball (0 : ℂ) ρ → h.IsInvertible ∧
      ∀ j, IsDerivAt (fun z => (e' u z).left) 0 (h (Pi.single j 1))
        (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2) := fun u => by
    by_cases hu : u ∈ Metric.ball (0 : ℂ) ρ
    · obtain ⟨D, hD⟩ := exists_lieEquiv Z.t (hexp u hu).1 (hA u hu) (hexp u hu).2.2.2.2
      have ex : ∃ f : EigFrame Z ((ψ u).comp φ) (spMap (ψ u) ≫ (x ≫ genι Z)), ∀ τ i, f.v τ i = spMap (dualMap (ψ u)) ≫ fr.v τ i := by
        open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
        have h : GlobalTheory.LocM.IsFrame Z.t ((ψ u).comp φ) (spMap (ψ u) ≫ (x ≫ genι Z)) ((fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i)) := by
          letI : Algebra c.F A := φ.toAlgebra
          letI : Algebra c.F ℂ := ((ψ u).comp φ).toAlgebra
          let v : ∀ τ, Fin (Dw.mult τ) → TanM (x ≫ genι Z) Z.t.G := fun τ i => tanOf (fr.tan τ i)
          have eps_dual (a : A) : spMap (dualMap (ψ u)) ≫ spMap (epsMul a) = spMap (epsMul ((ψ u) a)) ≫ spMap (dualMap (ψ u)) := by
            rw [spMap_comp_spMap, spMap_comp_spMap]
            congr 1
            refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]
          have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
              spMap (epsMul (((ψ u).comp φ) (embK c τ a))) ≫ (fun τ i => spMap (dualMap (ψ u)) ≫ fr.v τ i) τ i := fun τ i a => by
            show (spMap (dualMap (ψ u)) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (dualMap (ψ u)) ≫ fr.v τ i
            rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
          have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
            exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
          have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM (ψ u) (v k.1 k.2) := by
            have h := full_equiv (eB Dw).symm (full_bc (ψ u) (full_equiv (eB Dw) h1))
            exact (funext fun k => congrArg (fun j : IxB Dw => resM (ψ u) (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
          refine ⟨fun τ i => ⟨isTan_map (ψ u) rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
          have h3 := eig_of_full c (fun τ i => resM (ψ u) (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
            ((eig_iff c τ _).1 hwe)
          exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM (ψ u) (v τ i)) a (tanOf hw)).2 h3
        exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
      let f := Classical.choose ex
      have hf := Classical.choose_spec ex
      obtain ⟨b, hb⟩ := exists_basis f
      refine ⟨((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv, fun _ => ⟨⟨_, rfl⟩, fun j => ?_⟩⟩
      have h1 := hD (D.symm (f.vec (e j).1 (e j).2))
      rw [D.apply_symm_apply] at h1
      have h2 : ((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv (Pi.single j 1) =
          D.symm (f.vec (e j).1 (e j).2) := by simp [hb, Pi.single_apply]
      rw [← hf, ContinuousLinearEquiv.coe_coe, h2]
      exact h1
    · exact ⟨0, fun h => absurd h hu⟩
  choose h hh using hh
  refine ⟨h, fun u hu => ⟨(hh u hu).1, ?_, fun ex hadd hex hd z => ?_⟩⟩
  · refine ((hh u hu).1.contDiffAt_map_inverse (n := 1)).continuousAt.comp (continuousAt_clm_apply.2 fun z => ?_)
    have : ∀ u, h u z = ∑ j, z j • h u (Pi.single j 1) := fun u => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_smul, ← map_sum]
      exact congrArg _ (pi_eq_sum_univ' z)
    simp only [this]
    refine tendsto_finsetSum _ fun j _ => ContinuousAt.const_smul ?_ (z j)
    exact continuousAt_dir (e := e') (w := fun b => h b (Pi.single j 1))
      (v := fun b => spMap (dualMap (ψ b)) ≫ fr.v (e j).1 (e j).2) hol hu (hexp u hu).2.2.2.2 (fun b hb => (hh b hb).2 j) (continuousAt_snd (fun a =>
      ((harc.1.2 a).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρr hu))).continuousAt) _)
  · obtain ⟨hu1, -, hu2, -, hu3⟩ := hexp u hu
    obtain ⟨k, hk, -⟩ := existsUnique_linear hadd hu1 hex hu2 hu3
    have hkh : k = (h u).toLinearMap := (Pi.basisFun ℂ (Fin g)).ext fun i => by
      have h1 := (isDerivAt0_iff _ _ _).1 (hd i)
      simp only [hk] at h1
      have h2 := (isDerivAt_comp_iff (hA u hu) (LinearMap.toContinuousLinearMap k) _ _).1 h1
      rw [Pi.basisFun_apply]
      exact (hu3 (Over.homMk _ h2.over) h2.1).unique ((isDerivAt0_iff _ _ _).2 h2)
        ((isDerivAt0_iff _ _ _).2 ((hh u hu).2 i))
    rw [hk, hkh, ContinuousLinearMap.coe_coe]

end GlobalTheory.ShFam.BdArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM

theorem exists_isGaloisCover_of_isQProjOver_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ _ X s Ga _ _ ρ hs h1 hm hρ hfree
  let τ := autOfRightAction ρ h1 hm
  have horbits : GlobalTheory.OrbitsInAffineOpens τ :=
    GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hs τ
  have hτg : ∀ g : Ga, (τ g).asIso.hom = ρ g⁻¹ := fun _ ↦ rfl
  have hτs : ∀ g : Ga, (τ g).asIso.hom ≫ s = s := fun g ↦ hρ g⁻¹
  have hfreeτ : GlobalTheory.IsFreeAction τ := by
    refine GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)
    exact inv_eq_one.mp (hfree k x g⁻¹ hx)
  obtain ⟨Y, π, hQ⟩ := (GlobalTheory.exists_isAffineQuotient_iff τ).mpr horbits
  let sY := hQ.desc s hτs
  have hπs : π ≫ sY = s := hQ.comp_desc s hτs
  obtain ⟨hsep, hlft, hqc⟩ := isSeparated_finiteType_of_isQProjOver hs
  refine ⟨Y, π, sY, hπs, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, h1, hm, fun a ↦ ?_,
      hQ.isFinite_of_isFreeAction hfreeτ, hQ.etale_of_isFreeAction hfreeτ, hQ.surjective, ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [hτg, inv_inv] at this
    · intro k _ _ y y' hyy
      obtain ⟨g, hg⟩ := (hQ.comp_eq_comp_iff y y').mp hyy
      refine ⟨g⁻¹, hg, fun b hb ↦ ?_⟩
      have key : y ≫ ρ (b * g) = y := by
        rw [hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfree k y _ key)
  · haveI : IsSeparated (π ≫ sY) := by
      rw [hπs]; exact hsep
    exact hQ.isSeparated sY
  · haveI : LocallyOfFiniteType (π ≫ sY) := by
      rw [hπs]; exact hlft
    haveI : IsLocallyNoetherian (Sp K) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
    exact hQ.locallyOfFiniteType sY
  · haveI : QuasiCompact (π ≫ sY) := by
      rw [hπs]; exact hqc
    exact hQ.quasiCompact sY

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevelTer
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_definiteUnitary_rational_inf_conj_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite (ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom : Subgroup (finU (E := E) (n := n))) := by
  first | exact @GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev_anyRank | exact GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev_anyRank | (intros; apply GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev_anyRank <;> assumption)
end

