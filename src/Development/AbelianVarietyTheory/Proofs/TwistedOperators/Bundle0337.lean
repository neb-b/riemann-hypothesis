module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationIntertwinesRealGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCoreComponentMemDepthLatticeGridCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LatSandwich

variable {D : D7}

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem rat_mul_tmul_mul {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (X : Matrix (Fin l) (Fin m) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (p : AF D.host.F) :
    rat A ⬝ (Matrix.of fun i j => p ⊗ₜ[D.host.F] X i j : Mx D l m) ⬝ rat B =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (A * X * B) i j := by
  ext i j
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, incA_eq, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← TensorProduct.tmul_sum]

theorem sandwich_hatMx {k l m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin l) (Fin m) D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (h : ∀ x ∈ M, A * x * B ∈ M') {z : Mx D l m} (hz : z ∈ hatMx M) :
    rat A ⬝ z ⬝ rat B ∈ hatMx M' := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    rw [rat_mul_tmul_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, _, h x hx, rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem sandwich_homLat {k l m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin l → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₂' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ₂') (hB : ∀ y ∈ Λ₂, B *ᵥ y ∈ Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) : ∀ x ∈ 𝔪 • homLat Λ Λ', A * x * B ∈ 𝔪 • homLat Λ₂ Λ₂' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr x hx => ?_) (fun x y hx hy => ?_)
  · have e : A * (r • x) * B = r • (A * x * B) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e]
    refine Submodule.smul_mem_smul hr fun y hy => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hA _ (hx _ (hB y hy))
  · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy

theorem sandwich_entry {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E)
    (a : D.host.E) (t : Fin l → D.host.E) (r : Fin m → D.host.E) (i : Fin k) (j : Fin n) :
    (A * Matrix.of (fun i j => a * t i * r j) * B) i j = a * (A *ᵥ t) i * ∑ m, r m * B m j := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sandwich_latO {S T S' T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)} (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (B : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT')
    (hB : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ k, star (s' k) * S'.gram k j = ∑ m, (∑ k, star (s k) * S.gram k m) * B m j)
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {w : WO S T} (hw : w ∈ latO S T LS LT P) :
    (rat A ⬝ w ⬝ rat B : WO S' T') ∈ latO S' T' LS' LT' P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', e⟩ := hB s hs
    have e1 : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
          (Matrix.of (fun i j => a * t i * ∑ k, star (s k) * S.gram k j) : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j := rfl
    rw [e1, rat_mul_tmul_mul]
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s', hs', A *ᵥ t, hA t ht, ?_⟩
    ext i j
    simp only [Matrix.of_apply]
    rw [sandwich_entry, e j]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) {y : Fin A.rank → D.host.E} (hy : y ∈ Λ) :
    M *ᵥ y ∈ d.lat Λ 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).val.zero_mem, by rw [hM, Matrix.mulVec_zero, add_zero]⟩

theorem orthogonalSumAuxiliaryVectors_projection_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) (hiso : Mᴴ * B.gram * M = A.gram)
    {x : Fin B.rank → D.host.E} (hx : x ∈ d.lat Λ 𝔟) : (A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ x ∈ Λ := by
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  have h1 : A.gram⁻¹ * (Mᴴ * B.gram) * M = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * (Mᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig, ← hM] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [← hM, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]
  exact hy

theorem proj_form {A B : HSp D} (M : Matrix (Fin B.rank) (Fin A.rank) D.host.E) (s : Fin B.rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j = ∑ m, (∑ k, star (s k) * B.gram k m) * M m j := by
  have e1 : (A.gram⁻¹ * (Mᴴ * B.gram))ᴴ * A.gram = B.gram * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det A),
      Matrix.mul_one]
  have e2 : (fun j => ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j) =
      star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have e3 : (fun j => ∑ m, (∑ k, star (s k) * B.gram k m) * M m j) = (star s ᵥ* B.gram) ᵥ* M := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have key : star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram = (star s ᵥ* B.gram) ᵥ* M := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul]
  exact congrFun (e2.trans (key.trans e3.symm)) j

end GlobalTheory.LatSandwich

namespace GlobalTheory.AscFin

open GlobalTheory.LatSandwich

theorem pcBF_core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h u hu
  simp only [pcBF, piecesOf, AddSubgroup.mem_comap, AddMonoidHom.coe_comp, Function.comp_apply] at hu
  rw [OrthDec.resS_apply]

  have key : rat (F.dJ ρ h).q0 ⬝ (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ⬝ rat ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      u ⬝ (F.oB ρ h).jA := by
    rw [rat_mul, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
    change (F.dJ ρ h).p0 ⬝ ((F.dJ ρ h).j0 ⬝ u ⬝ (F.dB ρ h).p0) ⬝ ((F.dB ρ h).j0 ⬝ (F.oB ρ h).jA) = _
    simp only [← Matrix.mul_assoc]
    rw [HypDec.p0_j0, Matrix.one_mul, Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← key]

  have lat1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have iso2 : ((F.dB ρ h).i₀ * (F.oB ρ h).iA)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      (G.V (.core (2 * ρ + 2))).gram := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (F.oB ρ h).iAᴴ * ((F.dB ρ h).i₀ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * (F.dB ρ h).i₀) * (F.oB ρ h).iA := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(F.dB ρ h).iso, (F.oB ρ h).isoA]

  have hA : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) := fun t ht =>
    orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aJ ρ h) (F.dJ ρ h).iso (lat1 ▸ ht)

  have hB1 : ∀ y ∈ G.Λ (.core (2 * ρ + 2)), ((F.dB ρ h).i₀ * (F.oB ρ h).iA) *ᵥ y ∈ G.Λ (.grid (2 * ρ + 2) 0) :=
    fun y hy => lat2 ▸ orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice _ _ _ (hF.aB ρ h) hy

  have hB : ∀ s ∈ (G.Λ (.grid (2 * ρ + 2) 0) : Set (Fin (negSp (G.V (.grid (2 * ρ + 2) 0))).rank → D.host.E)),
      ∃ s' ∈ (G.Λ (.core (2 * ρ + 2)) : Set (Fin (negSp (G.V (.core (2 * ρ + 2)))).rank → D.host.E)), ∀ j,
        ∑ k, star (s' k) * (negSp (G.V (.core (2 * ρ + 2)))).gram k j =
          ∑ m, (∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k m) * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) m j := by
    intro s hs
    rw [SetLike.mem_coe, lat2] at hs
    refine ⟨_, orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aB ρ h) iso2 hs, fun j => ?_⟩
    simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_mul]
    rw [proj_form]
  have hu1 : (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈ latO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := hu.1
  have hu2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈
      hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) := hu.2
  refine ⟨?_, fun e he => ?_⟩
  · have h1 := sandwich_latO (S' := negSp (G.V (.core (2 * ρ + 2)))) (T' := G.V (.core (2 * ρ + 1)))
      (LS' := (G.Λ (.core (2 * ρ + 2)) : Set _)) (LT' := (G.Λ (.core (2 * ρ + 1)) : Set _)) _ _ hA hB _ hu1
    exact h1
  · have h2 := sandwich_hatMx _ _ (sandwich_homLat _ _ hA hB1 G.modul) (hu2 e he)
    rw [Matrix.mul_smul, Matrix.smul_mul] at h2
    exact h2

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIntertwinerMapValuesIsCuspFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCusp

theorem isCuspFun_iota (D : D7) (I : AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] [SigmaFinite μf] (ψ : I.GA → ℂ) (hc : Continuous ψ)
    (hi : ∀ γ ∈ I.GFset, ∀ y, ψ (γ * y) = ψ y) (hcusp : I.IsCuspFn (I.muA μf) ψ) :
    IsCuspFun (D.sp.Y 0) (fun g => ψ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) g)) := by
  subst h
  intro r C hC μ 𝓕 hμ h𝓕 g
  have : BorelSpace (GA D (D.sp.Y 0)) := ⟨rfl⟩
  have hW : (Formalism.IndefR.RationalEmbedding.inst D).IsIsot (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff _ _).2 ⟨r, C, hC, rfl⟩
  have key := (GlobalTheory.CuspCompare.constTerm_iff_inst (Formalism.IndefR.RationalEmbedding.inst D) μf
    (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ⟨(Formalism.IndefR.RationalEmbedding.iota D).continuous,
      (Formalism.IndefR.RationalEmbedding.iota D).symm.continuous⟩ (GQ (D.sp.Y 0)) (NI (D.sp.Y 0) C)
    (Formalism.IndefR.RationalEmbedding.iota_rat D) _ hW (_root_.GlobalTheory.SeeOntoCusp.mem_NI_iff_iota D C hC) ψ hc hi).2 (hcusp _ hW) μ 𝓕 hμ h𝓕 g
  exact key

theorem conjMap_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c ht hConj hInt Φ hΦ hRep u
  change IsCuspFun (D.sp.Y 0) _
  obtain ⟨-, -, -, -, -, -, hSL⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hDS
  obtain ⟨hd, hl, hb, hh, hph, -⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨-, -, ⟨T0, hT0⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds X.B X.dv hd hph
  have hw := GlobalTheory.RowCusp.row_isCuspFn hSL X.B X.dv _ hd hg hh hl hb T0 hT0 Φ hΦ
  have hcH := GlobalTheory.RowLev.isCuspHom_of_cusp_lowest X.B X.ds (fun v => (X.low v).1) Φ hΦ hw
  obtain ⟨ψ, hψ⟩ := hRep u
  have he := (GlobalTheory.ExtContRep.ext_ae_eq_contRep X.B _ ψ hψ).1
  have hcψ : X.B.I.IsCuspFn (X.B.I.muA X.B.μf) ψ :=
    (GlobalTheory.IntertwMult.contRep_facts X.B.I X.B.μf X.B.fund X.B.R X.B.fund_spec X.B.R_spec _ ψ hψ.1 hψ.2.1
      (he.mono fun x hx => hx.symm)).2.1 (hcH _)
  have hY := isCuspFun_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hcψ
  set t' : GA D (D.sp.Y 0) := t with ht'
  have hfun : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u = fun y => star (ψ (iotaX X h (y * t'⁻¹))) := by
    funext y
    exact congrArg star (congrFun (GlobalTheory.ConjRowMult.contRepL_spec X hψ) _)
  rw [hfun]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have key := hY r C hC μ 𝓕 hμ h𝓕 (g * t'⁻¹)
  have e : ∀ n : NI (D.sp.Y 0) C, ((n : GA D (D.sp.Y 0)) * g * t'⁻¹) = (n : GA D (D.sp.Y 0)) * (g * t'⁻¹) :=
    fun n => mul_assoc _ _ _
  have hs : ∀ z : ℂ, star z = starRingEnd ℂ z := fun _ => rfl
  simp only [e, hs]
  rw [integral_conj]
  exact (congrArg (starRingEnd ℂ) key).trans (map_zero _)

end GlobalTheory.ConjCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

section Pure

variable {ι : Type} [Fintype ι] {a b : ℕ}

def gq (c : ι → ℝ) (z : VCx ι a b) : ℝ := ∑ τ, ∑ i, ∑ j, c τ * ‖z τ i j‖ ^ 2

def bk (c : ι → ℝ) (z₀ z : VCx ι a b) : ℂ := ∑ τ, ∑ i, ∑ j, (c τ : ℂ) * z₀ τ i j * conj (z τ i j)

def conjMono (m : DVar ι a b →₀ ℕ) (z : VCx ι a b) : ℂ := m.prod fun k n => conj (z k.1 k.2.1 k.2.2) ^ n

end Pure

variable {D : D7}

def fw (D : D7) (τ : D.what₂.Tau) : ℝ := 2 * Real.pi * ‖tauE D τ D.host.xi0‖

def fockMat {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  ∑ i, ∑ j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
    ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j))

def fockPt (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (z : VCx D.what₂.Tau S.rank T.rank) : WO S T :=
  GlobalTheory.FockCompare.iotaW σ T S fun τ => fockMat A B τ (z τ)

def rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ) (x : WO S T) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x

theorem fw_pos (D : D7) (τ : D.what₂.Tau) : 0 < fw D τ := by
  unfold fw
  have h : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  positivity

end GlobalTheory.FockTransl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEvaluationTranslateMemRowSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.RowEvalHH in
theorem GlobalTheory.RowEvalHH.conj_eval_mem_HH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c v₀ ht hLM hc hv S hS φ hφ
  classical
  obtain ⟨hDS, -, -, -, -, hloc⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  obtain ⟨hinj, hran⟩ := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec
    X.B.e X.B.Re X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => (hDS v).2.2.2) (fun v => (X.low v).1) hloc X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens X.B.tens_spec

  let u : (∀ τ, ↥(Wsub R X c τ)) → X.B.Hs := fun y => tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))
  obtain ⟨f, K, hfe, hfn⟩ := _root_.GlobalTheory.RowEvalHHNorm.evF_multilinear_norm R F X h hLev hGrp hMod t c ht S hS
  have hfi := GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner f K hfn
  have hgram : ∀ a b, ⟪evF R X h t c S a, evF R X h t c S b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ := by
    intro a b
    rw [← hfe a, ← hfe b, hfi a b, tensT_inner]
    rfl
  have hdense : Dense (Submodule.span ℂ (Set.range u) : Set X.B.Hs) :=
    GlobalTheory.T.dense_span_tensor_of_dense_subspaces' (tensT X) (Wsub R X c) (tensT_inner X) (tensT_dense X) (Wsub_dense R X c)
  obtain ⟨Aop, hA⟩ := GlobalTheory.T.exists_clm_of_gram_eq_smul' u (evF R X h t c S) K hgram hdense
  have hHom : Aop ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    intro g
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy1, hy2⟩ := _root_.GlobalTheory.RowEvalHH.evF_equiv R F X h hLev hGrp hMod hHost hιE t c ht hc S hS g y
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    change Aop (X.B.σs g (u y)) = X.B.R (g, 1) (Aop (u y))
    rw [← hy1]
    change Aop (u y') = _
    rw [hA, hA, hy2]
  have hRe : X.B.Re.comp Aop = Aop := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hA]
    exact _root_.GlobalTheory.RowEvalHH.Re_evF R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  have heHom : Aop ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re :=
    Submodule.mem_map.2 ⟨Aop, hHom, hRe⟩

  let y₀ : ∀ τ, ↥(Wsub R X c τ) := fun τ => ⟨c τ (v₀ τ), Submodule.mem_map_of_mem (v₀ τ).2⟩
  have hu0 : u y₀ = X.B.tens X.B.w := by
    have : (fun τ => ((y₀ τ : ↥(Wsub R X c τ)) : X.B.H (X.pl.symm τ))) = fun τ => X.B.w (X.pl.symm τ) := by
      funext τ
      exact hv τ
    change tensT X _ = _
    rw [this, tensT_w]
  have hvec : vecOf R X c y₀ = v₀ := by
    funext τ
    apply Subtype.ext
    exact (c τ).symm_apply_apply (v₀ τ)
  obtain ⟨c', -, hnorm⟩ := _root_.GlobalTheory.EvalNormTransfer.evalTranslate_norm R F X h hLev hGrp hMod t ht
  have hunit : ∀ τ, ‖((v₀ τ : (MP R).H τ))‖ = 1 := by
    intro τ
    rw [← (c τ).norm_map, hv τ]
    exact (X.low _).1
  obtain ⟨hmem, -, -⟩ := hnorm v₀ hunit S hS
  have hval : Aop (X.B.tens X.B.w) = star φ := by
    rw [← hu0, hA]
    delta evF
    rw [hvec, dite_eq_left hmem]
    congr 1
    exact (Lp.ext (hφ.trans hmem.coeFn_toLp.symm)).symm
  have hmemHH : star φ ∈ Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund X.B.Re X.Rph := by
    rw [← hran]
    exact ⟨⟨Aop, heHom⟩, hval⟩
  exact hmemHH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffHeisenbergTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.MatCoefCont

theorem continuous_thPair_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Continuous (fun w : WO S T => thPair μ 𝓕 f (heisO ψ S T w f₀)) := by
  intro D ψ hψ S T μ 𝓕 h𝓕 f f₀ hf hf₀
  haveI hAE : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI hM : SecondCountableTopology (WO S T) :=
    inferInstanceAs (SecondCountableTopology (Fin T.rank → Fin S.rank → AE D))
  haveI : FirstCountableTopology (WO S T) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := (GlobalTheory.ThetaSquare.squareIntegrable hψ f hf).2.1
  obtain ⟨C₀, hC₀⟩ := (GlobalTheory.ThetaSquare.squareIntegrable hψ f₀ hf₀).2.1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓕.2.2]; exact ENNReal.one_lt_top⟩
  have hsc := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.1
  have hF : Continuous (fun p : WO S T × WO S T =>
      f p.2 * star (ψ (symplOH S T p.2 p.1) * f₀ (p.2 + p.1))) :=
    (hf.cont.comp continuous_snd).mul
      (((hψ.1.1.comp (hsc.comp (continuous_snd.prodMk continuous_fst))).mul
        (hf₀.cont.comp (continuous_snd.add continuous_fst))).star)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold thPair heisO
  refine continuous_of_dominated (bound := fun _ => C * C₀) (fun w => ?_) (fun w => ?_) (integrable_const _) ?_
  · exact (hF.comp (Continuous.prodMk_right w)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul, norm_star, norm_mul, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC z) (hC₀ _) (norm_nonneg _) hC0
  · exact Filter.Eventually.of_forall fun z => hF.comp (continuous_id.prodMk continuous_const)

end GlobalTheory.MatCoefCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmoothStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_orbit_coefficient_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | exact GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | (intros; apply GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth <;> assumption)
end

