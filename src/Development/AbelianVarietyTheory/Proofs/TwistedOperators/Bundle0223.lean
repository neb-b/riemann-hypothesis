module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0208
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelParamShiftedWeightOfCoverDisc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.Direct

def barRev {n : ℕ} (g : Mn n) : Mn n := (g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev

theorem barRev_barRev {n : ℕ} (g : Mn n) : barRev (barRev g) = g := by
  ext i j
  simp [barRev]

theorem barRev_mul {n : ℕ} (g h : Mn n) : barRev (g * h) = barRev g * barRev h := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [barRev, Matrix.submatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  exact (Fintype.sum_equiv Fin.revPerm _ _ (fun x => by simp [Fin.revPerm_apply])).symm

theorem barRev_one {n : ℕ} : barRev (1 : Mn n) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [barRev]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Matrix.one_apply, h, h']

theorem barRev_conjTranspose {n : ℕ} (g : Mn n) : barRev gᴴ = (barRev g)ᴴ := by
  ext i j
  simp [barRev, Matrix.conjTranspose_apply]

theorem barRev_Jm {n : ℕ} (ε : Fin n → Bool) : barRev (Formalism.REAL.Jm ε) = Formalism.REAL.Jm (fun a => ε a.rev) := by
  ext i j
  by_cases h : i = j
  · subst h
    by_cases hε : ε i.rev <;> simp [barRev, Formalism.REAL.Jm, hε]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

theorem barRev_mem_K {n : ℕ} {ε : Fin n → Bool} {g : Mn n} (hg : g ∈ Formalism.REAL.Kset ε) :
    barRev g ∈ Formalism.REAL.Kset (fun a => ε a.rev) := by
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose, ← barRev_conjTranspose, ← barRev_mul, ← Matrix.star_eq_conjTranspose, hu,
      barRev_one]
  · rw [← barRev_Jm, ← barRev_mul, hc, barRev_mul]

theorem isKFin_barRev {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Mn n → (H →L[ℂ] H)) (x : H) :
    IsKFin (fun a => ε a.rev) (fun g => σ (barRev g)) x ↔ IsKFin ε σ x := by
  have hK : ∀ g ∈ Formalism.REAL.Kset (fun a => ε a.rev), barRev g ∈ Formalism.REAL.Kset ε := by
    intro g hg
    simpa only [Fin.rev_rev] using barRev_mem_K hg
  simp only [IsKFin, IsKStableOn]
  constructor
  · rintro ⟨S, hS, hx, hst⟩
    refine ⟨S, hS, hx, fun g hg v hv => ?_⟩
    simpa only [barRev_barRev] using hst (barRev g) (barRev_mem_K hg) v hv
  · rintro ⟨S, hS, hx, hst⟩
    exact ⟨S, hS, hx, fun g hg v hv => hst (barRev g) (hK g hg) v hv⟩

theorem isEnum_rev {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam a.rev) (fun a => ε a.rev) := by
  obtain ⟨hanti, r, hr, hS⟩ := h
  refine ⟨fun a b hab => ?_, fun a => -r a.rev, fun a => by simp [hr], ?_⟩
  · have hba : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
    simpa using hanti hba
  · rw [show dualPar S = S.image fun x => (-x.1, x.2) from rfl, hS, Finset.image_image]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, rfl⟩

theorem Jm_rev {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm (fun a => ε a.rev) = (Formalism.REAL.Jm ε).submatrix Fin.revPerm Fin.revPerm := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.REAL.Jm]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

def barModel {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g))) :
    DSModel V (fun τ => dualPar (S τ)) where
  H := M.H
  nacg := M.nacg
  ips := M.ips
  σ τ g := M.σ τ (barRev g)
  lam τ a := -M.lam τ a.rev
  ε τ a := M.ε τ a.rev
  fr τ := (M.fr τ).submatrix Fin.revPerm (Equiv.refl _)
  enum τ := isEnum_rev (M.enum τ)
  ds := hds
  fr_unit τ := (Matrix.isUnit_submatrix_equiv _ _).2 (M.fr_unit τ)
  fr_gram τ := by
    rw [Jm_rev, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, M.fr_gram]
    rfl

theorem barRev_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (barMat (e.trans Fin.revPerm) g) = plainMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem barRev_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (plainMat (e.trans Fin.revPerm) g) = barMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem directBridge : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D → DirectBridge D := by
  intro D hB X V S M τ p q l₁ l₂ c hpq h₁ h₂ hpar hhas hS
  obtain ⟨hsrc, htgt⟩ := hB
  have hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g)) :=
    fun τ => _root_.GlobalTheory.ArchRec.isDS_conj_rev _ _ _ _ _ (M.ds τ)
  have hset : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.HidaSetting X p q l₁ l₂ c (fun τ => dualPar (S τ)) τ := by
    refine ⟨hpq, h₁, h₂, hpar, hhas, ?_⟩
    show dualPar (S τ) = _
    rw [hS]
  obtain ⟨-, m, hm, hU⟩ := hsrc X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain ⟨-, m', hm', hU'⟩ := htgt X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
  refine ⟨m', hm', fun e he b => ?_⟩
  have he' : SignCompat ((barModel M hds).ε τ) (e.trans Fin.revPerm) := by
    intro a
    change M.ε τ ((e.trans Fin.revPerm) a).rev = a.isLeft
    simp [he a]
  cases b
  · obtain ⟨U, hUm⟩ := hU _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smul z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (barMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_barMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)
  · obtain ⟨U, hUm⟩ := hU' _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smulₛₗ z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (plainMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_plainMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)

end GlobalTheory.ArchRec.Direct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitClassRealizedByLatticeIsometry
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat
theorem alpha_mem_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, diagH (star' P) (one₁ P) (Fv F v) (alphaRat P) ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ r P
  filter_upwards [eventually_one_tmul_mem_intLoc (F := F) (alpha P),
    eventually_one_tmul_mem_intLoc (F := F) (alpha P)⁻¹] with v h1 h2
  have e0 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 *ᵥ Y ∈
        latLoc F (stdLattice (Fld P) 1) v ↔ (1 : Fv F v) ⊗ₜ[F] alpha P * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    have e : (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 0 0 =
        (1 : Fv F v) ⊗ₜ[F] alpha P := rfl
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, ← e]
    simp [Matrix.mulVec, dotProduct]
  have hinv : (1 : Fv F v) ⊗ₜ[F] (alpha P)⁻¹ * (1 : Fv F v) ⊗ₜ[F] alpha P = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (alpha_ne_zero P), Algebra.TensorProduct.one_def]
  refine mem_stabLoc.2 fun Y => ?_
  rw [e0, mem_latLoc_stdLattice, Fin.forall_fin_one]
  refine ⟨mul_mem h1, fun hY => ?_⟩
  have := mul_mem h2 hY
  rwa [← mul_assoc, hinv, one_mul] at this

theorem stab_torEmb_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r n : ℕ) (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J x φ), (∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v) → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ σ r n P v J L x φ h hφ t
  have e1 : (matHom _ σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl
  have e0 : (torUnit t).1 = t.1.1 0 0 := Matrix.det_fin_one _
  have e2 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) t).1 *ᵥ Y ∈ latLoc F (stdLattice (Fld P) 1) v ↔
        (torUnit t).1 * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, e0]
    simp [Matrix.mulVec, dotProduct, matHom]
    exact Iff.rfl
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H Y
    rw [e2, mem_latLoc_stdLattice, Fin.forall_fin_one]
    have := H (φ (Y 0))
    rwa [e1, mulMat_mulVec, ← hφ, ← hφ] at this
  · intro H Y
    obtain ⟨y, rfl⟩ := φ.surjective Y
    rw [e1, mulMat_mulVec, ← hφ, ← hφ]
    have := H (fun _ => y)
    rwa [e2, mem_latLoc_stdLattice, Fin.forall_fin_one] at this

end GlobalTheory.TrUnitLat

namespace GlobalTheory.TrUnitLat

theorem hform_mulVec' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform s J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform s (Formalism.UG.cT s k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform s J a b = (s ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : s ∘ (k *ᵥ a) = (s ∘ a) ᵥ* Formalism.UG.cT s k := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem eventually_unitClass_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ), gam h ∈ stabLoc σ J L v ∧ ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _
  have := isLattice_stdLattice (E := E) (n := r)
  filter_upwards [_root_.GlobalTheory.TrUnitLat.gramOne_herm_nd F E σ hcm r P |> fun hH => _root_.GlobalTheory.HermCongAlmostAll.eventually_congr_int F E σ hcm r J (gramOne P) hJ hH,
    eventually_latLoc_eq F L (stdLattice E r), _root_.GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all F E σ r P, GlobalTheory.TrUnitLat.alpha_mem_stab F E σ r P] with v hu hL h3 h4
  obtain ⟨u, hu, hul⟩ := hu
  let φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E) :=
    (coordEquiv P (Fv F v)).trans (Matrix.toLinearEquiv' u.1 (Units.invertible u))
  have eφ : ∀ y, φ y = u.1 *ᵥ coordEquiv P (Fv F v) y := fun y => rfl
  have hφ : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ := fun y y' => by
    rw [eφ, eφ, hform_mulVec', hu]
    exact _root_.GlobalTheory.TrUnitLat.isIsom_coordEquiv F E σ r P (Fv F v) y y'
  have h5 : ∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v := fun y => by
    rw [eφ, hL, hul, h3]
  exact ⟨φ, hφ, (GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5 _).2 h4, GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5⟩

end GlobalTheory.TrUnitLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecomposition
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDecomp

variable {D : D7}

theorem adj_eq' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := rfl

theorem frame_relations {V V' : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    adj D C' * V.gram * C = 1 ∧ (V'.gram⁻¹ * adj D B * V.gram) * C = 0 ∧
    (V'.gram⁻¹ * adj D B * V.gram) * C' = 0 ∧ (V'.gram⁻¹ * adj D B * V.gram) * B = 1 ∧
    adj D C * V.gram * C = 0 ∧
    C * (adj D C' * V.gram) + (B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram)) = 1 := by
  have hG : V.gramᴴ = V.gram := GlobalTheory.MixModel.gram_conjTranspose V
  have hC : Cᴴ * V.gram * C = 0 := by
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C = Cᴴ := adj_eq' C
    have := hs.frame.2.2
    rwa [e] at this
  have hB := hs.isom
  have hCB := hs.orth
  simp only [adj_eq'] at hB hCB h1 h2 h3 ⊢

  have hC'C : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose hCB
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hG' : V'.gram⁻¹ * V'.gram = 1 := Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V')
  have hPC : V'.gram⁻¹ * Bᴴ * V.gram * C = 0 := by
    simp only [Matrix.mul_assoc] at hBC ⊢; rw [hBC, Matrix.mul_zero]
  have hPC' : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0 := by
    simp only [Matrix.mul_assoc] at hBC' ⊢; rw [hBC', Matrix.mul_zero]
  have hPB : V'.gram⁻¹ * Bᴴ * V.gram * B = 1 := by
    simp only [Matrix.mul_assoc] at hB ⊢; rw [hB, hG']
  refine ⟨hC'C, hPC, hPC', hPB, hC, ?_⟩

  set P := V'.gram⁻¹ * Bᴴ * V.gram with hP
  let M : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E := Matrix.fromCols C (Matrix.fromCols B C')
  let N : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows (C'ᴴ * V.gram) (Matrix.fromRows P (Cᴴ * V.gram))
  have hNM : N * M = 1 := by
    simp only [N, M, Matrix.fromRows_mul, Matrix.mul_fromCols]
    ext (i | i | i) (j | j | j) <;>
      simp [hC'C, hPC, hPC', hPB, hC, h1, h2, h3, hCB, Matrix.one_apply]
  have hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have := hs.rank
    omega
  have hMN : M * N = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hNM
  simpa [M, N, Matrix.fromCols_mul_fromRows] using hMN


set_option maxHeartbeats 1000000 in
theorem decomp_exists : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  intro D V V' W r C B hs C' h1 h2 h3
  obtain ⟨hC'C, hPC, hPC', hPB, hCC, hid⟩ := frame_relations hs h1 h2 h3
  have hV'r := GlobalTheory.MixModel.ratL_eq W V'
  have hVr := GlobalTheory.MixModel.ratL_eq W V

  set f := incA D with hf
  set a := (adj D C' * V.gram).map f with ha
  set c := (adj D C * V.gram).map f with hc
  set p := (V'.gram⁻¹ * adj D B * V.gram).map f with hp
  set u := C.map f with hu
  set u' := C'.map f with hu'
  set b := B.map f with hb
  have m1 : ∀ {k l m : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E) (Y : Matrix (Fin l) (Fin m) D.host.E),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul).symm
  have z0 : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) D.host.E).map f = 0 := Matrix.map_zero _ (map_zero f)
  have o1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) D.host.E).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have au : a * u = 1 := by rw [ha, hu, m1, hC'C, o1]
  have cu : c * u = 0 := by rw [hc, hu, m1, hCC, z0]
  have pu : p * u = 0 := by rw [hp, hu, m1, hPC, z0]
  have au' : a * u' = 0 := by rw [ha, hu', m1, h2, z0]
  have cu' : c * u' = 1 := by rw [hc, hu', m1, h1, o1]
  have pu' : p * u' = 0 := by rw [hp, hu', m1, hPC', z0]
  have ab : a * b = 0 := by rw [ha, hb, m1, h3, z0]
  have cb : c * b = 0 := by rw [hc, hb, m1, hs.orth, z0]
  have pb : p * b = 1 := by rw [hp, hb, m1, hPB, o1]
  have key : u * a + (b * p + u' * c) = 1 := by
    rw [ha, hc, hp, hu, hu', hb, m1, m1, m1, ← Matrix.map_add f (map_add f), ← Matrix.map_add f (map_add f), hid, o1]

  have fwd : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      isoPart V W C' t + isoPart V W C y + midPart V V' W B x = t * a + y * c + x * p := fun _ _ _ => rfl
  have back : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      (t * a + y * c + x * p) * u = t ∧ (t * a + y * c + x * p) * u' = y ∧
        (t * a + y * c + x * p) * b = x := by
    intro t y x
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Matrix.add_mul, Matrix.mul_assoc, au, cu, pu, au', cu', pu', ab, cb, pb, Matrix.mul_one,
        Matrix.mul_zero, add_zero, zero_add]
  have cont : ∀ {k l m : ℕ} (Q : Mx D l m), Continuous fun z : Mx D k l => z * Q := by
    intro k l m Q
    exact continuous_id.matrix_mul continuous_const
  haveI := (GlobalTheory.MixModel.lattice_Mx D W.rank V.rank).1
  let e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W :=
    { toFun := fun q => isoPart V W C' q.1 + isoPart V W C q.2.1 + midPart V V' W B q.2.2
      invFun := fun w => (w * u, w * u', w * b)
      left_inv := by
        rintro ⟨t, y, x⟩
        simp only [fwd]
        rw [(back t y x).1, (back t y x).2.1, (back t y x).2.2]
      right_inv := by
        intro w
        simp only [fwd]
        calc w * u * a + w * u' * c + w * b * p = w * (u * a + (b * p + u' * c)) := by
              simp only [Matrix.mul_add, Matrix.mul_assoc]; abel
          _ = w := by rw [key, Matrix.mul_one]
      map_add' := by
        rintro ⟨t, y, x⟩ ⟨t', y', x'⟩
        simp only [fwd, Prod.mk_add_mk, Matrix.add_mul]
        abel
      continuous_toFun := by
        simp only [fwd]
        exact (((cont a).comp continuous_fst).add ((cont c).comp (continuous_fst.comp continuous_snd))).add
          ((cont p).comp (continuous_snd.comp continuous_snd))
      continuous_invFun := ((cont u).prodMk ((cont u').prodMk (cont b))) }
  refine ⟨e, fun t y x => rfl, fun t y x => ?_⟩
  change isoPart V W C' t + isoPart V W C y + midPart V V' W B x ∈ ratL W V ↔ _
  rw [fwd, hVr, hV'r]
  have hr : ∀ {k l : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E), X.map f ∈ GlobalTheory.MixModel.ratMx D k l :=
    fun X => GlobalTheory.MixModel.rat_mem X
  have hmul : ∀ {k l m : ℕ} {X : Mx D k l} {Y : Mx D l m},
      X ∈ GlobalTheory.MixModel.ratMx D k l → Y ∈ GlobalTheory.MixModel.ratMx D l m →
      X * Y ∈ GlobalTheory.MixModel.ratMx D k m := by
    intro k l m X Y hX hY
    obtain ⟨A, rfl⟩ := hX
    obtain ⟨B, rfl⟩ := hY
    change A.map f * B.map f ∈ GlobalTheory.MixModel.ratMx D k m
    rw [m1]
    exact hr (A * B)
  constructor
  · intro h
    obtain ⟨b1, b2, b3⟩ := back t y x
    refine ⟨?_, ?_, ?_⟩
    · rw [← b1]; exact hmul h (hr C)
    · rw [← b2]; exact hmul h (hr C')
    · rw [← b3]; exact hmul h (hr B)
  · rintro ⟨ht, hy, hx⟩
    exact add_mem (add_mem (hmul ht (hr _)) (hmul hy (hr _)))
      (hmul hx (hr _))

end GlobalTheory.TwistDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SW.Lev

theorem exists_bar_mk_eq_at_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  intro D P b
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := P) (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal) (fun _ => 1)
    (fun PP _ => PP.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun PP => Classical.choose (Ideal.Quotient.mk_surjective (b PP.1)))
  refine ⟨GlobalTheory.SW.Lev.bar y, fun PP hPP => ?_⟩
  rw [GlobalTheory.SW.Lev.bar_bar]
  have h := hy PP hPP
  rw [pow_one] at h
  have hc := Classical.choose_spec (Ideal.Quotient.mk_surjective (b PP))
  rw [← hc]
  exact Ideal.Quotient.eq.2 h

end GlobalTheory.SW.Lev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitarySpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_module_onto_span_of_intertwining : ∀ (r s : ℕ) (W U I : Type) [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U] [InnerProductSpace ℂ U] (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U), IsGK a → IsUAct b → (∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)) → ∃ (MM : UGKMod r s) (inc : MM.M.V →ₗ[ℂ] U), Function.Injective inc ∧ LinearMap.range inc = Submodule.span ℂ {y | ∃ i P, y = j i P} ∧ ∀ Z ∈ upq r s, ∀ y, inc (MM.M.act Z y) = b Z (inc y) := by
  first | exact @GlobalTheory.ArchRec.SpanMod.exists_unitary_span | exact GlobalTheory.ArchRec.SpanMod.exists_unitary_span | (intros; apply GlobalTheory.ArchRec.SpanMod.exists_unitary_span <;> assumption)
end

