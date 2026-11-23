module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0088
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenCongruenceEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingOpenLevel

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem col_mem (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (p : Fin c) :
    (fun i => d.a i p) ∈ d.lat Λ (fun _ => 1) := by
  refine ⟨0, Λ.zero_mem, Pi.single p 1, fun q => ?_, ?_⟩
  · by_cases h : q = p
    · subst h; rw [Pi.single_eq_same]; exact FractionalIdeal.one_mem_one _
    · rw [Pi.single_eq_of_ne h]; exact FractionalIdeal.zero_mem _
  · funext i; simp [mulVec_single]

theorem map_mem (d : HermitianOrthogonalExtensionData A B c ε) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {y : Fin A.rank → D.host.E}
    (hy : y ∈ Λ) : frameMat B A d.ι *ᵥ y ∈ d.lat Λ (fun _ => 1) :=
  ⟨y, hy, 0, fun _ => FractionalIdeal.zero_mem _, by simp⟩

theorem lat_eq (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) :
    d.lat Λ (fun _ => 1) = Λ.map ((frameMat B A d.ι).mulVecLin.restrictScalars (𝓞 D.host.E)) ⊔
      Submodule.span (𝓞 D.host.E) (Set.range fun p i => d.a i p) := by
  refine le_antisymm ?_ (sup_le ?_ (Submodule.span_le.2 ?_))
  · rintro _ ⟨y, hy, u, hu, rfl⟩
    refine Submodule.add_mem_sup ⟨y, hy, rfl⟩ ?_
    choose r hr using fun p => (FractionalIdeal.mem_one_iff _).1 (hu p)
    have e : d.a *ᵥ u = ∑ p, r p • fun i => d.a i p := by
      funext i
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, ← hr, Algebra.smul_def, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩; exact map_mem d hy
  · rintro _ ⟨p, rfl⟩; exact col_mem d Λ p

theorem isLattice_lat (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) : Submodule.IsFullLattice D.host.E (d.lat Λ (fun _ => 1)) := by
  have hfg : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := by
    apply Submodule.IsLattice.of_fg D.host.E
    rw [lat_eq]
    exact (hΛ.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  let S := Submodule.span D.host.E (d.lat Λ (fun _ => 1) : Set (Fin B.rank → D.host.E))
  have hmap : ∀ y : Fin A.rank → D.host.E, frameMat B A d.ι *ᵥ y ∈ S := by
    intro y
    have hy : y ∈ Submodule.span D.host.E (Λ : Set _) := by rw [hΛ.span_eq_top]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (map_mem d hy)
    | zero => simp
    | add x y _ _ hx hy => simpa only [mulVec_add] using S.add_mem hx hy
    | smul a x _ hx => simpa only [mulVec_smul] using S.smul_mem a hx
  have hcols : ∀ u : Fin c → D.host.E, d.a *ᵥ u ∈ S := by
    intro u
    have e : d.a *ᵥ u = ∑ p, u p • fun i => d.a i p := by
      funext i
      simp [mulVec, dotProduct, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => S.smul_mem _ (Submodule.subset_span (col_mem d Λ p))
  have : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := hfg
  refine ⟨?_⟩
  apply Submodule.eq_top_iff'.2
  intro x
  have h := congrArg (fun M => M *ᵥ x) (GlobalTheory.UnitaryEmbeddingGroup.decomp d hε)
  simp only [add_mulVec, ← mulVec_mulVec, one_mulVec] at h
  rw [← h]
  exact S.add_mem (hmap _) (hcols _)

end GlobalTheory.UnitaryEmbeddingOpenLevel


open GlobalTheory.UnitaryEmbeddingOpenLevel in
theorem GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  intro D Y V d Λ 𝔪 hΛ h𝔪
  exact (congLev_open_compact V (isLattice_lat d one_ne_zero
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice Y Λ hΛ)) h𝔪).1

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedDict

open scoped Matrix

theorem sum_form_orthoFrame {K : Type} [Field K] [StarRing K] {n : ℕ} (G B : Matrix (Fin n) (Fin n) K)
    (hB : Bᴴ * G * B = 1) (c d : Fin n → K) :
    ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = ∑ i, star (c i) * d i := by
  have h1 : ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = star (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ d)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
    Matrix.one_mulVec]
  rfl

theorem isSelfDualC_inV : ∀ {D : D7} (S : HSp D) (fr : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1 → ∀ Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), SD D Ls → ∃ Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), (Λ : Set (Fin S.rank → D.host.E)) = GlobalTheory.MovedDict.inV fr Ls ∧ IsSelfDualC S Λ := by
  intro D S fr hfr Ls hLs
  classical
  have hB : fr.1ᴴ * S.gram * fr.1 = 1 := hfr
  obtain ⟨hfg, hspan, hdual⟩ := hLs
  let f : (Fin S.rank → D.host.E) →ₗ[D.host.E] (Fin S.rank → D.host.E) := Matrix.toLin' fr.1
  have hinv : ∀ y, fr.1 *ᵥ ((fr⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv' : ∀ y, (fr⁻¹).1 *ᵥ (fr.1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hmem : ∀ y, y ∈ Ls.map (f.restrictScalars (𝓞 D.host.E)) ↔ (fr⁻¹).1 *ᵥ y ∈ Ls := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [f, Matrix.toLin'_apply, hinv'] using hx
    · intro h
      exact ⟨_, h, by simp [f, Matrix.toLin'_apply, hinv]⟩
  have hform : ∀ x y : Fin S.rank → D.host.E, ∑ i, ∑ j, star (x i) * S.gram i j * y j =
      ∑ i, star (((fr⁻¹).1 *ᵥ x) i) * ((fr⁻¹).1 *ᵥ y) i := by
    intro x y
    have := sum_form_orthoFrame S.gram fr.1 hB ((fr⁻¹).1 *ᵥ x) ((fr⁻¹).1 *ᵥ y)
    rwa [hinv, hinv] at this
  refine ⟨Ls.map (f.restrictScalars (𝓞 D.host.E)), ?_, Submodule.IsLattice.of_fg D.host.E (hfg.map _), fun y => ?_⟩
  · ext x
    simp [inV, f, Matrix.toLin'_apply]
  · rw [hmem, hdual]
    constructor
    · intro h x hx
      rw [hmem] at hx
      obtain ⟨b, hb⟩ := h _ hx
      exact ⟨b, by rw [hform]; exact hb⟩
    · intro h x' hx'
      have hx : fr.1 *ᵥ x' ∈ Ls.map (f.restrictScalars (𝓞 D.host.E)) := by
        rw [hmem, hinv']; exact hx'
      obtain ⟨b, hb⟩ := h _ hx
      rw [hform, hinv'] at hb
      exact ⟨b, hb⟩

end GlobalTheory.MovedDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunOPlaceModelApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceThetaVal
open GlobalTheory.PlaceVec GlobalTheory.PlaceModel GlobalTheory.AdelicLatMove

theorem isThetaFunO_placeModel_apply : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (A B : HSp D)
    (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ (e : AE D) (f₀ Φ : WO A B → ℂ) (Tm : (WO A B → ℂ) →ₗ[ℂ] (WO A B → ℂ)),
    e * e = e → infPart D e = 0 →
    IsPlaceModel ψ (symplO A B) (heisO ψ A B) e (latO A B (ΛA : Set (Fin A.rank → D.host.E)) (ΛB : Set (Fin B.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    IsThetaFunO ψ A B f₀ →
    IsSBHalf e (latO A B (ΛA : Set (Fin A.rank → D.host.E)) (ΛB : Set (Fin B.rank → D.host.E)) fun _ => True) Φ →
    IsThetaFunO ψ A B (Tm Φ) := by
  intro D ψ hψ S T ΛS ΛT hS hT a f₀ Φ Tm ha hinf h₁ hf₀ hΦ
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hmul := exists_nsmul_mem_latO (selfDual_isFullLattice S ΛS hS) (selfDual_isFullLattice T ΛT hT)
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      b • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T b := fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  have ha' : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y z; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro x y z; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y
      have hz : symplO S T 0 y = 0 := by simpa using symplO_add_left S T 0 0 y
      rw [hz, AddChar.map_zero_eq_one]
    · intro y
      have hz : symplO S T y 0 = 0 := by simpa using symplO_add_right S T y 0 0
      rw [hz, AddChar.map_zero_eq_one]
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ, ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (half_infPart hinf hu.2)).1 hu.1 y hy
  have hmem := mem_waveSpan (X := half S T a) (Y := half S T (cA D a)) (L := Λ ⊓ half S T a)
    (L' := Λ ⊓ half S T (cA D a)) hb inf_le_right inf_le_right (fun u hu y hy => hLL' u hu y hy.1)
    (fun x hx h => ⟨(hdual x (half_infPart hinf hx)).2 fun u hu => by
      have := h _ (hsm ha' u hu)
      rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩)
    (half_div S T a) (half_div S T _) tf (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => a • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, a • u, hsm ha u hu, ?_⟩
      have := (mem_half S T).1 ht.2
      rw [← this, htr, smul_add, smul_comm a k u])
    Φ (fun t ht => (isHalf_iff S T).1 (hΦ.1 t ht)) _ hΦ.2.choose_spec.1
      (fun u hu => hΦ.2.choose_spec.2.1 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨hΦ.2.choose_spec.2.2 t ht, (half S T a).nsmul_mem ((isHalf_iff S T).1 (hΦ.1 t ht)) _⟩
  let P : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T (Tm g)}
      add_mem' := fun {g g'} hg hg' => by
        show IsThetaFunO ψ S T (Tm (g + g'))
        rw [map_add (f := _)]
        exact {
          quasi γ w := by simp only [Pi.add_apply, hg.quasi, hg'.quasi, mul_add]
          level := by
            obtain ⟨U, hU, h1⟩ := hg.level
            obtain ⟨U', hU', h2⟩ := hg'.level
            refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
            funext w
            have e1 := congrFun (h1 u hu.1 h0) w
            have e2 := congrFun (h2 u hu.2 h0) w
            unfold heisO at e1 e2 ⊢
            rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
          cont := hg.cont.add hg'.cont
          smooth k L h1 h2 w := (hg.smooth k L h1 h2 w).add (hg'.smooth k L h1 h2 w) }
      zero_mem' := by
        show IsThetaFunO ψ S T (Tm 0)
        rw [map_zero]
        exact {
          quasi γ w := by simp only [Pi.zero_apply, mul_zero]
          level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
          cont := continuous_const
          smooth k L _ _ w := contDiff_const }
      smul_mem' := fun c g hg => by
        show IsThetaFunO ψ S T (Tm (c • g))
        rw [map_smul]
        exact {
          quasi γ w := by rw [Pi.smul_apply, Pi.smul_apply, hg.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
          level := by
            obtain ⟨U, hU, h1⟩ := hg.level
            refine ⟨U, hU, fun u hu h0 => ?_⟩
            funext w
            have e1 := congrFun (h1 u hu h0) w
            unfold heisO at e1 ⊢
            rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
          cont := hg.cont.const_smul c
          smooth k L h1 h2 w := contDiff_const.mul (hg.smooth k L h1 h2 w) } }
  have hsub : waveSpan (fun x y => ψ (symplO S T x y)) (half S T a) (half S T (cA D a)) (Λ ⊓ half S T a) ≤ P := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hSB : IsSBHalf a Λ fun t => ψ (symplO S T t y) * halfInd a Λ t := by
      obtain ⟨k, hk, hky⟩ := hmul y (half_infPart (infPart_cA hinf) hy)
      have hne : ∀ t, ψ (symplO S T t y) * halfInd a Λ t ≠ 0 → t ∈ Λ ⊓ half S T a := fun t ht => by
        by_contra hn
        rw [halfInd_eq_ind, ind, if_neg hn, mul_zero] at ht
        exact ht rfl
      refine ⟨fun t ht => (isHalf_iff S T).2 (hne t ht).2, k, hk, fun u hu hu' t => ?_,
        fun t ht => nsmul_mem (hne t ht).1 k⟩
      have hu'' : u ∈ Λ ⊓ half S T a := ⟨hu, (isHalf_iff S T).1 hu'⟩
      have e1 := hb.left t (k • u) y
      have e2 := hb.nsmul k u y
      beta_reduce at e1 e2 ⊢
      rw [e1, e2, hLL' u hu'' _ hky, mul_one, halfInd_eq_ind, ind_add _ _ (nsmul_mem hu'' k)]
    have key : Tm (wave (fun x y => ψ (symplO S T x y)) (Λ ⊓ half S T a) x y) = heisO ψ S T x (heisO ψ S T y f₀) := by
      have e1 := h₁.trans _ hSB x ((isHalf_iff S T).2 hx)
      have e2 := h₁.modul _ (GlobalTheory.isSBHalf_halfInd a Λ) y ((isHalf_iff S T).2 hy)
      have e3 := h₁.vac
      rw [one_smul] at e3
      rw [e2, e3, halfInd_eq_ind] at e1
      exact e1
    show IsThetaFunO ψ S T (Tm _)
    rw [key]
    exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ y) x
  exact hsub hmem

end GlobalTheory.PlaceThetaVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

section Gen

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

def typeSpan (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : Submodule ℂ M :=
  ⨆ (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)), Y₀.map T

theorem typeSpan_le (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : typeSpan ρ Y₀ G ≤ G :=
  iSup₂_le fun _ h => h.1

theorem le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (h : Y₀ ≤ G) : Y₀ ≤ typeSpan ρ Y₀ G := by
  have h1 : Y₀.map LinearMap.id ≤ typeSpan ρ Y₀ G :=
    le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
      LinearMap.id ⟨by rwa [Submodule.map_id], fun _ _ _ => rfl⟩ le_rfl
  rwa [Submodule.map_id] at h1

theorem map_le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (T : M →ₗ[ℂ] M) (hT : Y₀.map T ≤ G)
    (hc : ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) : Y₀.map T ≤ typeSpan ρ Y₀ G :=
  le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
    T ⟨hT, hc⟩ le_rfl

end Gen

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def rTrL (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rTrL_apply (k : GA D V) (f : GA D V → ℂ) : rTrL k f = rTr V k f := rfl

def KIdx : Type := {p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ // GlobalTheory.CuspGK.InK M p.1 p.2}

def rhoK (i : KIdx M) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := rTrL (atTau θ V i.1.1 i.1.2)

def KStable (Y : Submodule ℂ (GA D V → ℂ)) : Prop :=
  ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ Y, rTr V (atTau θ V τ g) f ∈ Y

theorem kStable_iff (Y : Submodule ℂ (GA D V → ℂ)) : KStable θ M Y ↔ ∀ i, ∀ y ∈ Y, rhoK θ M i y ∈ Y :=
  ⟨fun h i y hy => h i.1.1 i.1.2 i.2 y hy, fun h τ g hg y hy => h ⟨(τ, g), hg⟩ y hy⟩

theorem kStable_inf {Y Y' : Submodule ℂ (GA D V → ℂ)} (h : KStable θ M Y) (h' : KStable θ M Y') :
    KStable θ M (Y ⊓ Y') :=
  fun τ g hg f hf => ⟨h τ g hg f hf.1, h' τ g hg f hf.2⟩

theorem kStable_gkGen (ψ : GA D V → ℂ) : KStable θ M (GlobalTheory.CuspGK.gkGen θ M ψ) :=
  (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ).k

theorem kStable_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (h : GlobalTheory.CuspGK.IsGKSub θ M A) : KStable θ M A := h.k

end GlobalTheory.KTypeProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem embLL_labLL {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem rowMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.rowMap d (ch.S.ptRow c) v).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ hSum β hβ τ hτ d hd c v hv
  have h0 := GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range _ D.what₂.embLL hSum.read.1 v hv
  have h1 := _root_.GlobalTheory.RowRho.coeff_rhoVr_mem_range (tauE D) D.what₂.embLL (fun τ x => ⟨labLL D τ x, embLL_labLL τ x⟩) _
    (ch.S.N.fr (.grid 0 D.R.m))⁻¹ _ h0
  have gen : ∀ (k : ∀ i, VV ℂ (wt ch.G (.grid i D.R.m)) →ₗ[ℂ] VV ℂ (wt ch.G (.grid (i + 1) D.R.m))),
      (∀ i (w : VV ℂ (wt ch.G (.grid i D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (k i w).1 m ∈ Set.range D.what₂.embLL) →
      ∀ j (w : VV ℂ (wt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (chainTo (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m))) k j w).1 m ∈ Set.range D.what₂.embLL := by
    intro k hk j
    induction j with
    | zero => intro w hw; exact hw
    | succ j ih => intro w hw; exact hk j _ (ih w hw)
  simp only [GlobalTheory.FunObj.GridChoice.rowMap, LinearMap.comp_apply]
  refine gen _ (fun i w hw m => ?_) D.R.m _ h1
  split_ifs with h
  · refine coeff_map_mem _ _ ?_ w hw m
    intro a b
    have := (hF.isRatAt hβ hτ hd c).2 ⟨i, h⟩ a b
    simpa [GlobalTheory.FunObj.Normal.IsRatAt, GlobalTheory.FunObj.Normal.IsRatIn, GlobalTheory.FunObj.Normal.kkIn, LinearMap.toMatrix_apply] using this
  · exact ⟨0, by simp⟩

end GlobalTheory.RowRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunOAlt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VecThetaDef

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N)
    {t : T} {p : Pair T} (d : FinDatum G t p), DefPair D.R.m p → p.InRange D.R.m → Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) := by
  intro D T L sc G W U N Z t p d hp hIn h
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (Z.vac_is p hp).2.theta)

end GlobalTheory.VecThetaDef
end
end

