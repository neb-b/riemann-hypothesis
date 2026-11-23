module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0095
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DefiniteSmallIrreducibleLieDerivative
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.DefiniteSmallIrred
theorem definite_small_irreducible_lie_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Ψ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
  GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X (fun h => ωB (1, h)) τ Y Ψ Φ' → ∀ h : GA D X,
  HasDerivAt (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) (GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' h) 0 := by
  intro hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨ Φ' hΦ' hder h
  have hw : IsWeilDatumO ψ W₁ X α (α / β) ωB := (GlobalTheory.Grid.isWeil_false ψ W₁ X α (α / β) ωB).1 hm.weilB
  have hthA : ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, IsThetaFunO ψ W₁ X Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have hth : IsThetaFunO ψ W₁ X Ψ := hthA Ψ hΨ
  have hpos : ∀ τ, (gramAt D W₁ τ).PosDef := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs₁ τ)
  obtain ⟨Gn, hGn⟩ := _root_.GlobalTheory.DefLift.Gen.exists_generator D ψ W₁ X α (α / β) ωB hw θ hθ τ Y hY
  have hGΨ : ∀ (g : GA D W₁) (k : GA D X),
      HasDerivAt (fun t : ℝ => thetaKO ωB g (k * oneP θ X τ Y t) Ψ) (thetaKO ωB g k Φ') 0 := by
    have hG : Gn Ψ = Φ' := by
      funext z
      have h1 := (hGn Ψ hth).2.2.2 1 z
      simp only [one_mul, map_one, Module.End.one_apply] at h1
      exact h1.unique (hder z)
    intro g k
    have h1 := (hGn Ψ hth).2.2.2 (g, k) 0
    simp only [Prod.mk_mul_mk, mul_one, hG] at h1
    exact h1
  let L : ℂ →ₗ[ℂ] (WO W₁ X → ℂ) := LinearMap.toSpanSingleton ℂ _ Ψ
  have hL : ∀ x, IsThetaFunO ψ W₁ X (L x) := fun x => GlobalTheory.OrientedHeis.theta_smul x hth
  have hL1 : L 1 = Ψ := by simp [L]
  obtain ⟨-, hD⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ W₁ X α (α / β) ωB hw θ hθ hpos ℂ L hL
    (fun _ => 1) continuous_const (fun _ _ _ => rfl) ν₁ 𝓕₁ hν₁.1 hν₁.2
  obtain ⟨L', -, hk, hlift⟩ := hD τ Y hY
  have hkid : ∀ g k, thetaKO ωB g k (L' 1) = thetaKO ωB g k Φ' := by
    intro g k
    have h1 := hk 1 g k
    rw [hL1] at h1
    exact h1.unique (hGΨ g k)
  have h2 := hlift h
  simp only [GlobalTheory.DefLift.lift, hL1, hkid] at h2
  exact h2
theorem theta_vanish_all_of_irreducible : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
  GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, p' Φ' ≠ 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' = 0 →
  ∀ Φ'' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  intro hP hTK hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂
  have hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hTK hLM
  set S := GlobalTheory.SquareComm.algF ψ θ false A₁ B with hSdef
  have hint := GlobalTheory.DefIrred.integrable_algF hψ hθ A₁ B hm.weilB hs₁ hν₁
  have tr : ∀ (Φ : WO W₁ X → ℂ) (g : GA D W₁) (h k : GA D X), thetaKO ωB g h (ωB (1, k) Φ) = thetaKO ωB g (h * k) Φ := by
    intro Φ g h k
    show (ωB (g, h) * ωB (1, k)) Φ 0 = _
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rfl
  have tsub : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ - Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ - GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ - Ψ)) = fun g => thetaKO ωB g h Φ - thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_sub]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.sub_apply]
    rw [e]
    exact integral_sub (hΦ h) (hΨ h)
  have tadd : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ + Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ + GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ + Ψ)) = fun g => thetaKO ωB g h Φ + thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_add (f := _)]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hΦ h) (hΨ h)
  have tsmul : ∀ (c : ℂ) Φ, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (c • Φ) = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ := by
    intro c Φ; funext h
    have e : (fun g => thetaKO ωB g h (c • Φ)) = fun g => c * thetaKO ωB g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul c _
  let Kint : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {Φ | (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) ∧ GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (a + b)) = fun g => thetaKO ωB g h a + thetaKO ωB g h b := by
            funext g; simp [thetaKO, map_add (f := _)]
          rw [e]; exact (ha.1 h).add (hb.1 h),
        by rw [tadd a b ha.1 hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨fun h => by simp [thetaKO], by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]⟩
      smul_mem' := fun c a ha => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (c • a)) = fun g => c * thetaKO ωB g h a := by
            funext g; simp [thetaKO, map_smul]
          rw [e]; exact (ha.1 h).const_mul c,
        by rw [tsmul, ha.2, smul_zero]⟩ }
  let K : Submodule ℂ (WO W₁ X → ℂ) := S ⊓ Kint
  obtain ⟨c, hc0, hc⟩ := hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D ψ θ hψ hθ W₁ X A₁ B α (α / β) ωB hm.weilB hs₁ ν₁ 𝓕₁ hν₁
  have kerp' : GlobalTheory.SquareComm.finRel ωB S ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    simp [map_sub, hm.mapB.invf u hu Ψ hΨ]
  have kill : ∀ Ψ ∈ S, p' Ψ = 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
    intro Ψ hΨ hp0
    obtain ⟨Φ₀, hΦ₀, hd, -, hI⟩ := hc Ψ hΨ
    have hp00 : p' Φ₀ = 0 := by
      have := kerp' hd
      rw [LinearMap.mem_ker, map_sub, hp0, zero_sub, neg_eq_zero] at this
      exact this
    have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp00])
    have h2 : GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 0 = 0 := by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]
    rw [h2] at h1
    have h3 : GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ₀ = 0 := (smul_eq_zero.1 h1.symm).resolve_left hc0
    have h4 := hrel _ hd
    rw [tsub Ψ Φ₀ (hint Ψ hΨ) (hint Φ₀ hΦ₀), h3, sub_zero] at h4
    exact h4
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p', rf g x ∈ K.map p' := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    refine ⟨ωB (1, g) Ψ, ⟨hm.mapB.stabX.1 g hg Ψ hΨS, fun h => ?_, ?_⟩, hm.mapB.eqf g hg Ψ hΨS⟩
    · simp only [tr]; exact hΨi (h * g)
    · funext h
      simp only [GlobalTheory.SquareComm.thetaInt, tr]
      exact congrFun hΨ0 (h * g)
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p', rl τ Y x ∈ K.map p' := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    obtain ⟨Φ', hΦ'S, hder⟩ := hm.mapB.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Φ', ⟨hΦ'S, hint Φ' hΦ'S, ?_⟩, hm.mapB.eql τ Y hY Ψ hΨS Φ' hΦ'S hder⟩
    funext h
    have hd := _root_.GlobalTheory.DefiniteSmallIrred.definite_small_irreducible_lie_derivative hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨS Φ' hΦ'S hder h
    have e0 : (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) = fun _ => (0 : ℂ) := by
      funext t; rw [hΨ0]; rfl
    rw [e0] at hd
    exact hd.unique (hasDerivAt_const 0 0)
  rcases hm.irred.2 (K.map p') stf stl with hbot | htop
  · exfalso
    have : p' Φ₁ ∈ K.map p' := ⟨Φ₁, ⟨hΦ₁, hint Φ₁ hΦ₁, hz₁⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hp₁ this
  · have : p' Φ₂ ∈ K.map p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, hΨp⟩ := this
    have h0 := kill (Φ₂ - Ψ) (S.sub_mem hΦ₂ hΨS) (by rw [map_sub, hΨp, sub_self])
    rw [tsub Φ₂ Ψ (hint Φ₂ hΦ₂) hΨi, hΨ0, sub_zero] at h0
    exact h0
end GlobalTheory.DefiniteSmallIrred
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_of_definite_small_irreducible : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
  GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, p' Φ' ≠ 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' = 0 →
  ∀ Φ'' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  first | exact @_root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | exact _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible | (intros; apply _root_.GlobalTheory.DefiniteSmallIrred.theta_vanish_all_of_irreducible <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftSurjectiveTripleInvariants
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleInv
theorem theta_lift_surjective_triple_invariants : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ := by
  intro hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTr hTr' R Rf hM
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := h.ψ ▸ hM.triple.base.std
  have hG : Γ.M.IsGood ψ := h.ψ ▸ hM.triple.geo.hM
  have hG' : Γ.M'.IsGood ψ := h.ψ ▸ hM.triple.geo.hM'
  have hX : Γ.W.J.det ≠ 0 := by
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (gram_det_ne X)
  have hV : Γ.V.J.det ≠ 0 := by
    rw [h.JW, one_smul]; exact gram_det_ne W
  have hV' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (gram_det_ne W₁)
  obtain ⟨hmain, hmain'⟩ := _root_.GlobalTheory.T.theta_image_eq_span_darboux hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTr hTr' R Rf hM
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT1, -⟩ := _root_.GlobalTheory.ThetaTransformInj.linear_injective D Γ.M ψ (sgn true W).gram e hG hstd hV hX (gram_det_ne _)
    intro Φ hΦ
    rw [← hmain T hT1] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    refine ⟨Ψ, hΨ, (hT1 Ψ ?_).symm⟩
    exact GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hM.triple.geo.hM hΨ
  · obtain ⟨T, hT1, -⟩ := _root_.GlobalTheory.ThetaTransformInj.linear_injective D Γ.M' ψ (sgn false W₁).gram e hG' hstd hV' hX (gram_det_ne _)
    intro Φ hΦ
    rw [← hmain' T hT1] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    refine ⟨Ψ, hΨ, (hT1 Ψ ?_).symm⟩
    exact GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM' hΨ
end GlobalTheory.TripleInv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_invariant_theta_surjective : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ := by
  first | exact @_root_.GlobalTheory.TripleInv.theta_lift_surjective_triple_invariants | exact _root_.GlobalTheory.TripleInv.theta_lift_surjective_triple_invariants | (intros; apply _root_.GlobalTheory.TripleInv.theta_lift_surjective_triple_invariants <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleProductAlgebraWeilRepRangeEqTop
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.Onto
theorem tripleProductAlgebra_weilRep_range_eq_top : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) = ⊤ ∧ (algF ψ θ false A₁ B).map (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) = ⊤ := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  obtain ⟨iA, iB⟩ := _root_.GlobalTheory.T.theta_image_eq_span_darboux hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have dV : Γ.V.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV.sig w)
  have dV' : Γ.V'.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV'.sig w)
  have dW : Γ.W.J.det ≠ 0 := det_ne_of_hasSig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)
  have gA : (sgn true W).gram.det ≠ 0 := by
    have e1 : (sgn true W).gram = -W.gram := rfl
    rw [h.JW, one_smul] at dV
    rw [e1, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) dV
  have gB : (sgn false W₁).gram.det ≠ 0 := by
    have e1 : (sgn false W₁).gram = W₁.gram := rfl
    rw [h.JW₁, Matrix.det_smul] at dV'
    rw [e1]
    exact right_ne_zero_of_mul dV'
  constructor
  · obtain ⟨T, hT, hinj⟩ := _root_.GlobalTheory.ThetaTransformInj.linear_injective D Γ.M ψ (sgn true W).gram e (hψ' ▸ hg.hM) hstd dV dW gA
    rw [← iA T hT]
    refine (map_thetaLift Γ.M ψ _ e _ _ (GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M Bs.ψ Bs.emb hg.hM) T hT hinj).trans ?_
    exact map_darbAlg_eq_top Γ.M Bs.ψ Bs.emb hg.hM R.p Rf.p _ (Filter.Eventually.of_forall fun _ => rfl)
      hm.real.quot.onto hm.fin.onto
  · obtain ⟨T, hT, hinj⟩ := _root_.GlobalTheory.ThetaTransformInj.linear_injective D Γ.M' ψ (sgn false W₁).gram e (hψ' ▸ hg.hM') hstd dV' dW gB
    rw [← iB T hT]
    refine (map_thetaLift Γ.M' ψ _ e _ _ (GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Γ.M' Bs.ψ Bs.emb hg.hM') T hT hinj).trans ?_
    refine map_darbAlg_eq_top Γ.M' Bs.ψ Bs.emb hg.hM' R.p' Rf.p' _ ?_ hm.real.quot'.onto hm.fin.onto'
    filter_upwards [Xc.T.eventually_cofinite_notMem] with v hv using (hm.fin.sph v hv).1.symm
end GlobalTheory.TripleAssembly.Onto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_algebra_map_surjective : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) = ⊤ ∧ (algF ψ θ false A₁ B).map (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) = ⊤ := by
  first | exact @_root_.GlobalTheory.TripleAssembly.Onto.tripleProductAlgebra_weilRep_range_eq_top | exact _root_.GlobalTheory.TripleAssembly.Onto.tripleProductAlgebra_weilRep_range_eq_top | (intros; apply _root_.GlobalTheory.TripleAssembly.Onto.tripleProductAlgebra_weilRep_range_eq_top <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRegulariserIsGood
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.RegGood
theorem regulariser_isGood : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (W W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωB : WRep W₁ X, IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧ GlobalTheory.FunObj.zdeg z ≠ 0 ∧
      ∀ i, ModInt θ ωB ν₁ 𝓕₁ ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
        ∃ u' ∈ GfC W₁, (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) =
          ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  intro hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hωB n Ψ u hΨ hu
  have hstd : IsStdChar D ψ (-1) := hωB.std
  obtain ⟨ωA, -, hωA, -⟩ := _root_.GlobalTheory.T.weilRepresentation_square_comm hP D ψ hstd W W₁ X α β hT
  obtain ⟨A⟩ := GlobalTheory.ChainFr.Model.nonempty_fr W
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    _root_.GlobalTheory.SquareAgree.exists_isOver D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hωA hωB
  obtain ⟨Pa, hPa⟩ := _root_.GlobalTheory.T.twisted_form_mem_regular_subspace hP D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD n Ψ hΨ
  obtain ⟨Pb, hPb⟩ := _root_.GlobalTheory.GoodComm.comm_at_good_place D ψ θ hθ W₁ X A₁ B α β ωB hωB n Ψ u hΨ hu
  classical
  obtain ⟨v, hv, hsp, ⟨t⟩⟩ := _root_.GlobalTheory.SplitAway.exists_splitsFully_notMem D.host.F D.host.E (Pa ∪ Pb ∪ Xc.T)
  have hvg : Xc.Good v := ⟨fun h => hv (Finset.mem_union_right _ h), hsp⟩
  obtain ⟨z, hzs, hzd, hzi⟩ :=
    hPa v (fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ h))) hvg t
  refine ⟨z, fun k hk => (hzs k hk).1, hzd, fun i => ⟨?_,
    hPb v (fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))) z (fun k hk => (hzs k hk).2) i⟩⟩
  obtain ⟨Φ₀D, hD, hSo⟩ := hzi i
  have hTD' := isTriple_atPlace hTD v t hvg
  obtain ⟨hDec, -⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig _ W.rank W₁.rank Γ Xc om om' hTD'
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D hSo
  exact _root_.GlobalTheory.ModGrowth.modInt_of_bound D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e { Bs with v₁ := v, τ₁ := t } Γ Xc om om' cA cB hθ { hO with } hν₁
    hTD' _ Φ₀D hD hconv (by
      obtain ⟨C, k, hC⟩ := hbd 0
      exact ⟨C, k, fun g h => by simpa using hC g h⟩)
end GlobalTheory.RegGood
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_regulariser_isGood : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (W W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωB : WRep W₁ X, IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧ GlobalTheory.FunObj.zdeg z ≠ 0 ∧
      ∀ i, ModInt θ ωB ν₁ 𝓕₁ ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
        ∃ u' ∈ GfC W₁, (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) =
          ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  first | exact @_root_.GlobalTheory.RegGood.regulariser_isGood | exact _root_.GlobalTheory.RegGood.regulariser_isGood | (intros; apply _root_.GlobalTheory.RegGood.regulariser_isGood <;> assumption)
end
end

