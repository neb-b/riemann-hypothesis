module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanDarbouxCoordsOneParamOrbitSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanDarbouxCoordsOneParamOrbitSmoothStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | exact GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | (intros; apply GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def actUni (B : BesL D σ) : Subgroup (GA D B.V) where
  carrier := {g | ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt B.V a⁻¹ ⬝ (xLast B.d (vecB B.o B.ζ) ⬝ u.1) ⬝ (u⁻¹).1 = xLast B.d (vecB B.o B.ζ) ⬝ (u⁻¹).1 := by
      rw [← ha, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
    rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem mem_actUni_iff (B : BesL D σ) (g : GA D B.V) : g ∈ actUni B ↔ ∃ u ∈ UX D σ, ∃ v : Fin σ → AE D,
    mt B.V g ⬝ B.d.jX = B.d.jX ⬝ u.1 ∧
      mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) + B.d.jX *ᵥ v :=
  FB.snocCols_uni_iff (AE D) B.V.rank σ B.d.jX _ (mt B.V g)

theorem flagN_le_actUni (B : BesL D σ) : flagN B.d ≤ actUni B := by
  intro n hn
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).1 n).1 hn
  rw [mem_actUni_iff]
  have hm : mt B.V (B.d.levi u * (B.d.nB b * B.d.nC c)) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (u.1 ⬝ b) := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_j0, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic,
      ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc]
  refine ⟨u, hu, (u.1 ⬝ b) *ᵥ ratV (vecB B.o B.ζ), ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, B.d.nC_jX, B.d.nB_jX, B.d.levi_jX]
  · rw [Matrix.mulVec_mulVec, hm, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem embA_mem_actUni (B : BesL D σ) (h : GA D B.A) : embA B.d B.o h ∈ actUni B := by
  rw [mem_actUni_iff]
  refine ⟨1, one_mem _, 0, ?_, ?_⟩
  · rw [embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]
  · rw [Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec,
      vecB, FB.ratV_mulVec_rat]
    change B.d.j0 *ᵥ (mt B.V₀ (B.o.emb (h, 1)) *ᵥ (B.o.jB *ᵥ ratV B.ζ)) = B.d.j0 *ᵥ (B.o.jB *ᵥ ratV B.ζ)
    congr 1
    rw [Matrix.mulVec_mulVec, B.o.emb_jB, mt_one, Matrix.mul_one]

theorem besGrp_le_actUni (B : BesL D σ) : besGrp B.d B.o ≤ actUni B :=
  sup_le (flagN_le_actUni B) (by rintro _ ⟨h, rfl⟩; exact embA_mem_actUni B h)

theorem mem_besGrp_of_actUni (B : BesL D σ) (g : GA D B.V) (hg : g ∈ actUni B) : g ∈ besGrp B.d B.o := by
  obtain ⟨u, hu, v, hX, h0⟩ := (mem_actUni_iff B g).1 hg
  have hst : B.d.levi u⁻¹ * g ∈ stabX B.d := by
    show mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.jX = B.d.jX
    rw [mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, B.d.levi_jX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, k, hk⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.2.1 _).1 hst
  obtain ⟨b, c, rfl⟩ := ((flag_jacobi_structure D B.V B.V₀ σ B.d).2.1 n).1 hn
  have hp : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) ⬝ B.d.j0 = mt B.V₀ k := by
    rw [hk, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_unipotentMixed, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_unipotentSkew,
      Matrix.mul_assoc _ B.d.pY, B.d.pY_nC, Matrix.sub_mul, B.d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc _ B.d.pY, B.d.wittDecomp_projY_anisotropicEmbedding,
      Matrix.sub_mul, Matrix.mul_assoc, B.d.p0_j0, Matrix.mul_one, Matrix.mul_assoc _ B.d.pY, B.d.pY_j0,
      Matrix.mul_zero, sub_zero]
  have hz : mt B.V₀ k *ᵥ ratV (B.o.iB *ᵥ B.ζ) = ratV (B.o.iB *ᵥ B.ζ) := by
    have e1 : B.d.p0 ⬝ mt B.V (B.d.levi u⁻¹ * g) = B.d.p0 ⬝ mt B.V g := by
      rw [mt_mul, ← Matrix.mul_assoc, B.d.wittDecomp_projAnisotropic_levi]
    rw [← hp, e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change B.d.p0 *ᵥ (mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) = _
    rw [h0, Matrix.mulVec_add, Matrix.mulVec_mulVec, B.d.p0_j0, Matrix.one_mulVec, Matrix.mulVec_mulVec, B.d.p0_jX,
      Matrix.zero_mulVec, add_zero]
    rfl
  obtain ⟨h, rfl⟩ := FB.fix_lineVec_emb D B.V₀ B.A B.L B.o B.ζ B.line k hz
  have hg' : g = (B.d.levi u * (B.d.nB b * B.d.nC c)) * embA B.d B.o h := by
    rw [embA_apply, mul_assoc, ← hk, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_left (((flag_jacobi_structure D B.V B.V₀ σ B.d).1 _).2 ⟨u, hu, b, c, rfl⟩))
    (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem besGrp_act_xLast : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), xLast B.d (vecB B.o B.ζ) ⬝ a = xLast B.d (vecB B.o B.ζ) ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1.1 → u ∈ UXQ D (σ + 1) := by
  intro D σ B
  obtain ⟨⟨P, hP, hPx⟩, hx⟩ := xLast_rat_leftInv D σ B
  refine ⟨fun g => ⟨fun hg => besGrp_le_actUni B hg, fun hg => mem_besGrp_of_actUni B g hg⟩, ?_, ?_⟩
  · intro a a' h
    rw [← Matrix.one_mul a, ← Matrix.one_mul a', ← hPx, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro g hg u hgu
    have hinv : mt B.V g⁻¹ ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ (u.1⁻¹).1 := by
      have h1 : mt B.V g⁻¹ ⬝ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) ⬝ (u.1⁻¹).1 = xLast B.d (vecB B.o B.ζ) ⬝ (u.1⁻¹).1 := by
        rw [← hgu, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
      rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · have e : u.1.1 = P ⬝ mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) := by
        rw [Matrix.mul_assoc, hgu, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 hg)) hx
    · have e : (u.1⁻¹).1 = P ⬝ mt B.V g⁻¹ ⬝ xLast B.d (vecB B.o B.ζ) := by
        rw [Matrix.mul_assoc, hinv, ← Matrix.mul_assoc, hPx, Matrix.one_mul]
      rw [e]; exact ratMx_mul (ratMx_mul hP ((mem_GQ_iff _ _).1 (inv_mem hg))) hx

end GlobalTheory.Asc.FBL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF.DiagCoord

variable {D : D7}

theorem auxiliaryCoordinate_mem_staircaseIdeal {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {t : Fin B.rank → D.host.E} (ht : t ∈ d.lat Λ 𝔟) (r : Fin c) (hr : r.1 + r.1 + 1 ≠ c) :
    ((d.aᴴ * B.gram) *ᵥ t) r ∈ 𝔟 r.rev := by
  obtain ⟨y, -, v, hv, rfl⟩ := ht
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => (B.herm.eq (B.frame j) (B.frame i) : star (B.gram j i) = B.gram i j)
  have hperp : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg Matrix.conjTranspose d.perp
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) = (frameMat B A d.ι)ᴴ := rfl
    rw [e, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero] at h1
    rw [← h1, Matrix.mul_assoc]
  have hgram : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hperp, hgram, zero_mulVec, zero_add]
  rw [mulVec, dotProduct, Finset.sum_eq_single r.rev]
  · have : antiDiagonalSignGramMatrix c ε r r.rev = 1 := by
      have := r.2
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
      rw [if_pos (by omega), if_neg (fun h => hr (by rw [Fin.ext_iff, Fin.val_rev] at h; omega))]
    rw [this, one_mul]; exact hv _
  · intro q _ hq
    have : antiDiagonalSignGramMatrix c ε r q = 0 := by
      have := r.2; have := q.2
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg (fun h => hq (by rw [Fin.ext_iff, Fin.val_rev]; omega))]
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem negPair_colsOf {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (hG : ∀ i j, star (G j i) = G i j)
    (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (w : Fin k → D.host.E) (s : Fin n → D.host.E) (p : Fin k) :
    ∑ j, (∑ l, star (s l) * (-G) l j) * colsOf a f w j p = -(w p * star (((aᴴ * G) *ᵥ s) (f p))) := by
  simp only [colsOf, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, hG,
    Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_rankOne {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (e : Matrix (Fin n) (Fin l) D.host.E) (a : D.host.E)
    (t : Fin m → D.host.E) (g : Fin n → D.host.E) (p : Fin k) (p' : Fin l) :
    (q * Matrix.of (fun i j => a * t i * g j) * e) p p' = a * (q *ᵥ t) p * ∑ j, g j * e j p' := by
  simp only [Matrix.mul_apply, Matrix.of_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem rat_tmul_entry {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (C : Matrix (Fin m) (Fin n) D.host.E)
    (e : Matrix (Fin n) (Fin l) D.host.E) (X : AF D.host.F) (p : Fin k) (p' : Fin l) :
    (rat q ⬝ (Matrix.of fun i j => X ⊗ₜ[D.host.F] C i j : Mx D m n) ⬝ rat e) p p' = X ⊗ₜ[D.host.F] (q * C * e) p p' := by
  have hinc : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun _ => rfl
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, hinc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, ← TensorProduct.tmul_sum]

theorem stairId_mul_inv_succ (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) {c₁ c₂ : ℕ}
    (q₁ : Fin c₁) (q₂ : Fin c₂) (hc : c₂ = c₁ + 1) (hq : q₂.1 = q₁.1 + 1) :
    stairId 𝔞 𝔞' c₁ q₁ * (stairId 𝔞 𝔞' c₂ q₂)⁻¹ = 𝔞' := by
  unfold stairId
  rw [show c₂ - q₂.1 = c₁ - q₁.1 by omega, hq, pow_succ 𝔞' (q₁.1 + 1)]
  have h1 : 𝔞 ^ (c₁ - q₁.1) ≠ 0 := pow_ne_zero _ h𝔞
  have h2 : 𝔞' ^ (q₁.1 + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  field_simp

theorem colsOf_gram {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E) (f g : Fin k → Fin c)
    (w w' : Fin k → D.host.E) (p q : Fin k) :
    ((colsOf a f w)ᴴ * G * colsOf a g w') p q = star (w p) * w' q * (aᴴ * G * a) (f p) (g q) := by
  simp only [colsOf, Matrix.mul_apply, conjTranspose_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring


set_option maxHeartbeats 1000000 in
theorem diag_mem_complId : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))),
    u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) →
    ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  intro D T L sc G F hF ρ h u hu p
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  obtain ⟨hcB, heB, sB, he'B⟩ := hF.hB ρ h
  set aJ := G.colDec (2 * ρ + 1) (by omega) (by omega) with haJ
  set aB := G.colDec (2 * ρ + 2) (by omega) h with haB
  obtain ⟨hAA, -⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : G.pl.stAbar sc ≠ 0 := by
    intro h0
    apply hA
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h1 : star y ∈ G.pl.stAbar sc := (hconj _).2 (by rwa [star_star])
    have h2 := h0 _ h1
    rwa [star_eq_zero] at h2

  have hJ : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).qY *ᵥ t) p =
      star ((-D.host.xi0) ^ (p.1 + 1)) * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) := by
    intro t _
    simp only [HypDec.qY, heJ, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have hJmem : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p).rev := by
    intro t ht
    have ht' : t ∈ aJ.lat (G.sp.P (2 * ρ + 1)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := by
      rw [haJ, ← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)]; exact ht
    exact auxiliaryCoordinate_mem_staircaseIdeal aJ _ _ ht' _ (by simp only [Fin.val_castLE]; omega)

  have hBmem : ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0),
      star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) ∈
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)⁻¹ := by
    intro s hs
    have hs' : s ∈ aB.lat (G.sp.P (2 * ρ + 2)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := by
      rw [haB, ← G.sp.colLat (2 * ρ + 2) (by omega) h]; exact hs
    have h1 := auxiliaryCoordinate_mem_staircaseIdeal aB _ _ hs' (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
      (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    exact ((GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ _).2 _).1 h1

  have hsc : star ((-D.host.xi0) ^ (p.1 + 1)) * sB p = 1 := by
    have h1 := congrFun (congrFun (F.dB ρ h).e'e p) p
    rw [he'B, heB, colsOf_gram, Matrix.one_apply_eq] at h1
    have h2 : (aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
        (Fin.castLE (by omega) p) = 1 := by
      rw [show aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a = antiDiagonalSignGramMatrix (2 * ρ + 2 - 1) (-1) from aB.gram]
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE]
      rw [if_pos (by omega), if_neg (fun e => by rw [Fin.ext_iff, Fin.val_rev, Fin.val_castLE] at e; omega)]
    rw [h2, mul_one] at h1
    have h3 := congrArg star h1
    rw [star_mul', star_star, star_one] at h3
    rw [mul_comm]; exact h3
  have hGB : ∀ i j, star ((G.V (.grid (2 * ρ + 2) 0)).gram j i) = (G.V (.grid (2 * ρ + 2) 0)).gram i j := fun i j =>
    (G.V (.grid (2 * ρ + 2) 0)).herm.eq ((G.V (.grid (2 * ρ + 2) 0)).frame j) ((G.V (.grid (2 * ρ + 2) 0)).frame i)

  have keyE : ∀ a ∈ D.host.AA, ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0),
      ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) *
        (F.dB ρ h).e') p p ∈ D.host.AA * G.pl.stAbar sc := by
    intro a ha s hs t ht
    rw [entry_rankOne _ _ a t (fun j => ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j), hJ t ht, he'B,
      negSp_gram, negPair_colsOf _ hGB]
    have e : a * (star ((-D.host.xi0) ^ (p.1 + 1)) *
          ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p)) *
        -(sB p * star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)) =
        -(a * (((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) := by
      linear_combination (-(a * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) * hsc
    rw [e]
    refine Submodule.neg_mem _ (FractionalIdeal.mul_mem_mul ha ?_)
    rw [← stairId_mul_inv_succ (G.pl.stA sc) (G.pl.stAbar sc) hA hAb (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev
      (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev (by omega) (by simp only [Fin.val_rev, Fin.val_castLE]; omega)]
    exact FractionalIdeal.mul_mem_mul (hJmem t ht) (hBmem s hs)
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ((F.dJ ρ h).pY ⬝ (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j)) ⬝ (F.dB ρ h).jY) p p =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) *
          (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) * (F.dB ρ h).e') p p :=
      rat_tmul_entry _ _ _ _ _ _
    rw [key]
    exact tmul_mem_complId hα (keyE a ha s hs t ht)
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem hx

end GlobalTheory.XCharBF.DiagCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedSectionTendstoConstantTermImaginaryFlow
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.HeckeEx

theorem bddSec_tendsto_constTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, (∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom) ∧ Filter.Tendsto (fun t : ℝ => P (X.flow ξ (fun _ => Complex.I * t) x)) Filter.atTop (nhds (X.fj la ξ 0 P x)) := by
  intro E _ _ _ r X la P hP ξ hξ x hx
  have hdom : ∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom := fun t ht =>
    GlobalTheory.FjCauchy.flow_mem_dom X hξ hx _ fun τ => by
      have := GlobalTheory.FjCauchy.tt_pos X hξ hx τ
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add]
      linarith
  refine ⟨hdom, ?_⟩
  have hexp := m3bExp_holds (E := E) r X la P hP.1 ξ hξ x hx

  have hfac : ∀ (ν : X.Ψ → ℝ) (t : ℝ),
      Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ) =
        ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro ν t
    rw [Complex.ofReal_exp]
    congr 1
    have hs : ∑ τ, (ν τ : ℂ) * (Complex.I * (t : ℂ)) = (∑ τ, (ν τ : ℂ)) * (Complex.I * t) := by
      rw [Finset.sum_mul]
    simp only [hs]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  set F : ℝ → (X.Ψ → ℝ) → ℂ := fun t ν =>
    X.fj la ξ ν P x * Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ)
    with hF
  have hF' : ∀ t ν, F t ν = X.fj la ξ ν P x * ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro t ν; rw [hF]; dsimp only; rw [hfac]

  have hsum0 : Summable fun ν : X.Ψ → ℝ => X.fj la ξ ν P x := by
    have h := (hexp _ (hdom 0 le_rfl)).summable
    refine h.congr fun ν => ?_
    have := hF' 0 ν
    rw [hF] at this
    simp only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, _root_.mul_one] at this
    exact this
  have hbound : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr hsum0
  have hsign : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ := fun ν h =>
    BoundedSectionAlgebra.sign_of_bdd X moderateCoefficientPositivity_holds hP hξ ν hx h
  have hlim : Filter.Tendsto (fun t => ∑' ν, F t ν) Filter.atTop
      (nhds (∑' ν : X.Ψ → ℝ, if ν = 0 then X.fj la ξ 0 P x else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun ν => ?_) ?_
    · by_cases h0 : X.fj la ξ ν P x = 0
      · have : (if ν = 0 then X.fj la ξ 0 P x else 0) = 0 := by
          split_ifs with h; · subst h; exact h0
          · rfl
        rw [this]
        simp only [hF', h0, zero_mul]
        exact tendsto_const_nhds
      by_cases hν : ν = 0
      · subst hν
        simp only [hF', if_true, Finset.sum_const_zero, Pi.zero_apply, mul_zero, zero_mul, neg_zero,
          Real.exp_zero, Complex.ofReal_one, _root_.mul_one]
        exact tendsto_const_nhds
      · rw [if_neg hν]
        have hnn := hsign ν h0
        obtain ⟨τ0, hτ0⟩ : ∃ τ0, ν τ0 ≠ 0 := by
          by_contra hc; push_neg at hc; exact hν (funext hc)
        have hS : 0 < ∑ τ, ν τ :=
          Finset.sum_pos' (fun τ _ => hnn τ) ⟨τ0, Finset.mem_univ _, lt_of_le_of_ne (hnn τ0) (Ne.symm hτ0)⟩
        have hk : 0 < 4 * Real.pi * ∑ τ, ν τ := by positivity
        have he : Filter.Tendsto (fun t : ℝ => Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)))
            Filter.atTop (nhds 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hk)
        have := ((Complex.continuous_ofReal.tendsto 0).comp he).const_mul (X.fj la ξ ν P x)
        simp only [Complex.ofReal_zero, mul_zero] at this
        simp only [hF']
        exact this
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht ν
      rw [hF', norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      by_cases h0 : X.fj la ξ ν P x = 0
      · simp [h0]
      have hS : 0 ≤ ∑ τ, ν τ := Finset.sum_nonneg fun τ _ => hsign ν h0 τ
      have : Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 4 * Real.pi * (∑ τ, ν τ) * t := by positivity
        linarith
      calc ‖X.fj la ξ ν P x‖ * Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t))
          ≤ ‖X.fj la ξ ν P x‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖X.fj la ξ ν P x‖ := _root_.mul_one _
  rw [tsum_ite_eq] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [hF]
  exact (hexp _ (hdom t ht)).tsum_eq

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIntertwinerMapValuesIsCuspFunStatement
section
public alias GlobalTheory.T.conjIntertwinerMap_values_isCuspFun :=
  GlobalTheory.ConjCusp.conjMap_isCuspFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumLatticeStabilizerBlocksKeepLatticeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_blocks_keep_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  first | exact @GlobalTheory.DblVac.KD_blocks_keep | exact GlobalTheory.DblVac.KD_blocks_keep | (intros; apply GlobalTheory.DblVac.KD_blocks_keep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleLiftSplitPlaceConjugatePairStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_lift_splitPlaceConjugatePair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
  ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → (∀ z, π₂ (cA σ z) = π₁ z) → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  S.map (fun x => (x : Fv F v)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∀ X₁ X₂ : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), X₁ᵀ * S + S * X₂ = 0 →
  ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
    Y.map π₁ = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) * X₁.map (fun x => (x : Fv F v)) * ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Y.map π₂ = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) * X₂.map (fun x => (x : Fv F v)) * ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 := by
  first | exact @GlobalTheory.AdmLift.exists_admissible_lift | exact GlobalTheory.AdmLift.exists_admissible_lift | (intros; apply GlobalTheory.AdmLift.exists_admissible_lift <;> assumption)
end

