module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Generic

variable {B Hf W : Type} [Group B] [Group Hf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : B →* Hf) (Γ : Subgroup B)
  (ρ : B →* Module.End ℂ W) {J : Subgroup Hf} {χ : J →* ℂˣ}

theorem rho_mul (a b : B) (w : W) : ρ (a * b) w = ρ a (ρ b w) := by rw [map_mul]; rfl

theorem rho_rho_inv (a : B) (w : W) : ρ a (ρ a⁻¹ w) = w := by rw [← rho_mul, mul_inv_cancel, map_one]; rfl

theorem mem_adForms (s : Hf → B) (hs : ∀ u, π (s u) = u) (hρ : ∀ u, ρ (s u) = 1) (Ψ : B → W)
    (h : ∀ γ ∈ Γ, ∀ k (hk : π k ∈ J), ∀ x, Ψ (γ * x * k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (Ψ x)) :
    (fun u => Ψ (s u)) ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ := by
  intro γ u k
  have e : π (((γ : B) * s u)⁻¹ * s (π γ * u * k)) = k := by
    rw [map_mul, map_inv, map_mul, hs, hs, inv_mul_cancel_left]
  have h1 := h γ γ.2 _ (e ▸ k.2) (s u)
  rw [mul_inv_cancel_left] at h1
  have h2 : ∀ u, ρ (s u)⁻¹ = 1 := fun u => by
    have := map_mul ρ (s u)⁻¹ (s u)
    rwa [inv_mul_cancel, map_one, hρ, mul_one, eq_comm] at this
  refine h1.trans ?_
  have h3 : ρ (((γ : B) * s u)⁻¹ * s (π γ * u * k))⁻¹ = ρ γ := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, map_mul, h2, hρ, one_mul, mul_one]
  rw [h3]
  congr 3
  exact Subtype.ext e

theorem form_law {f : Hf → W} (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) {γ : B} (hγ : γ ∈ Γ) (k : B)
    (hk : π k ∈ J) (x : B) :
    ρ (γ * x * k)⁻¹ (f (π (γ * x * k))) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (ρ x⁻¹ (f (π x))) := by
  have h : f (π γ * π x * π k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ γ (f (π x)) := hf ⟨γ, hγ⟩ (π x) ⟨π k, hk⟩
  rw [map_mul π, map_mul π, h, map_smul, ← rho_mul, ← rho_mul]
  congr 3
  group

theorem vec_law (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {a b : W} {z : ℂ} (hz : ‖z‖ = 1) (k : B)
    (h : ∀ w, inner ℂ a w = z⁻¹ * inner ℂ b (ρ k w)) : a = z • ρ k⁻¹ b := by
  refine ext_inner_right ℂ fun w => ?_
  rw [h, inner_smul_left, ← hρ k (ρ k⁻¹ b), ← rho_mul, mul_inv_cancel, map_one, Complex.inv_eq_conj hz]
  rfl

theorem exists_dual [FiniteDimensional ℂ W] (u : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, inner ℂ a w = u w :=
  haveI := FiniteDimensional.complete ℂ W
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap u), fun _ => InnerProductSpace.toDual_symm_apply⟩

theorem exists_linear_section {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X → Y → Prop)
    (h0 : p 0 0) (hadd : ∀ x x' y y', p x y → p x' y' → p (x + x') (y + y')) (hsm : ∀ (a : ℂ) x y, p x y → p (a • x) (a • y))
    (hex : ∀ x, ∃ y, p x y) : ∃ th : X →ₗ[ℂ] Y, ∀ x, p x (th x) := by
  let S : Submodule ℂ (X × Y) :=
    { carrier := {z | p z.1 z.2}
      add_mem' := fun h h' => hadd _ _ _ _ h h'
      zero_mem' := h0
      smul_mem' := fun a _ h => hsm a _ _ h }
  obtain ⟨g, hg⟩ := (LinearMap.fst ℂ X Y ∘ₗ S.subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun x => (hex x).elim fun y hy => ⟨⟨(x, y), hy⟩, rfl⟩)
  refine ⟨LinearMap.snd ℂ X Y ∘ₗ S.subtype ∘ₗ g, fun x => ?_⟩
  have h1 : p (g x).1.1 (g x).1.2 := (g x).2
  have h2 : (g x).1.1 = x := LinearMap.congr_fun hg x
  rwa [h2] at h1

theorem scalar_of_form {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥)
    (Λ : ℂ) (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') = Λ * inner ℂ y y') :
    ∀ y ∈ U, th (LinearMap.adjoint th y) = ((‖Λ‖ : ℝ) : ℂ) • y := by
  obtain ⟨y₀, hy₀, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have e := h y₀ hy₀ y₀
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have hn : ((‖y₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have e1 : Λ = ((‖LinearMap.adjoint th y₀‖ ^ 2 / ‖y₀‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff (pow_ne_zero 2 hn)]
    exact e.symm
  have e2 : Λ = ((‖Λ‖ : ℝ) : ℂ) := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  intro y hy
  refine ext_inner_right ℂ fun y' => ?_
  rw [← LinearMap.adjoint_inner_right, h y hy, inner_smul_left, Complex.conj_ofReal, ← e2]

end Generic

section Kernel

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)


include hω hc hφ hinf hlev in
theorem kernel_law {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V) (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (x : GA D V)
    (g : GA D W) (w : c.W) :
    Datum.thetaKO ω (γ * x * k) g (φ w) = (Lev.levChi V β L k)⁻¹ * Datum.thetaKO ω x g (φ (c.ρ k w)) := by
  obtain ⟨κ, h1, h2⟩ := exists_finLift V ((finHom V).rangeRestrict k)
  have h3 : finHom V κ = finHom V k := congrArg Subtype.val h2
  have h4 : Lev.finE V κ = Lev.finE V k := by rw [Lev.finE_eq, Lev.finE_eq, h3]
  have h5 : κ⁻¹ * k ∈ GinfC V := by
    change finHom V (κ⁻¹ * k) = 1
    rw [map_mul, map_inv, h3, inv_mul_cancel]
  have h6 : c.ρ (κ⁻¹ * k) = c.ρ k := by rw [map_mul, hc.1 _ (inv_mem h1), one_mul]
  have h7 : Lev.levChi V β L κ = Lev.levChi V β L k := by unfold Lev.levChi; rw [h4]
  have e : ((γ * x * k, g) : GA D V × GA D W) = (γ, 1) * ((x, g) * ((κ, 1) * (κ⁻¹ * k, 1))) := by
    simp only [Prod.mk_mul_mk, mul_one, one_mul, mul_inv_cancel_left, mul_assoc]
  unfold Datum.thetaKO
  rw [e, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinf _ h5, h6,
    hlev κ ⟨h1, show Lev.finE V κ ∈ _ from h4 ▸ hk⟩, map_smul, map_smul, Pi.smul_apply, smul_eq_mul,
    hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ (hφ _)), h7]

theorem thetaKO_smul (h : GA D V) (g : GA D W) (a : ℂ) (f : Datum.WO V W → ℂ) :
    Datum.thetaKO ω h g (a • f) = a * Datum.thetaKO ω h g f := by
  unfold Datum.thetaKO
  rw [map_smul]
  rfl

theorem norm_levChi (k : GA D V) : ‖Lev.levChi V β L k‖ = 1 := norm_levFn _ _ _

theorem ext_law {x : Bridge.Gf V → c.W}
    (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V)
    (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (h : GA D V) :
    c.ext x (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (c.ext x h) :=
  form_law (finHom V).rangeRestrict (GQ V) c.ρ hx hγ k ((mem_grpOf V β L k).2 hk) h

theorem ext_finLift (hc : c.Is) (x : Bridge.Gf V → c.W) (u : Bridge.Gf V) : c.ext x (finLift V u) = x u := by
  change c.ρ (finLift V u)⁻¹ (x ((finHom V).rangeRestrict (finLift V u))) = x u
  rw [hc.1 _ (inv_mem (finLift_mem V u)), finLift_spec]
  rfl


include hω hc hφ hinf hlev in
theorem theta_classSum {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
    {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
    {x : Bridge.Gf V → c.W} (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) (g : GA D W) :
    ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext x h)) ∂ν =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (finLift V (y j)) g (φ (x (y j))) := by
  rw [integral_eq_classSum V β L hν hy]
  · simp only [ext_finLift c hc]
  · intro γ hγ k hk h
    rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, ext_law c β L hx hγ k hk, (c.ρ k).map_smul,
      rho_rho_inv c.ρ k, φ.map_smul, thetaKO_smul]
    exact inv_mul_cancel_left₀ (Lev.levChi_ne_zero L k) _


include hω hc hφ hinf hlev in
theorem exists_upVec (μ : Measure (GA D W)) (𝓖 : Set (GA D W)) (F : GA D W → ℂ)
    (hint : ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (F g)) 𝓖 μ) :
    ∃ Ψ : GA D V → c.W, (∀ h w, inner ℂ (Ψ h) w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F) ∧
      ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
        Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h) := by
  have h1 : ∀ h, ∃ a : c.W, ∀ w, inner ℂ a w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F := fun h =>
    exists_dual
      { toFun := fun w => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F
        map_add' := fun w w' => by
          unfold l2 Lift.pet
          rw [← integral_add (hint w h) (hint w' h)]
          simp only [Datum.thetaKO, map_add (f := _), Pi.add_apply, add_mul]
        map_smul' := fun a w => by
          unfold l2 Lift.pet
          simp only [Datum.thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
          exact integral_const_mul _ _ }
  choose Ψ hΨ using h1
  refine ⟨Ψ, hΨ, fun γ hγ k hk h => vec_law c.ρ hc.2.1 (norm_levChi β L k) k fun w => ?_⟩
  rw [hΨ, hΨ]
  unfold l2 Lift.pet
  rw [← integral_const_mul]
  congr 1
  funext g
  beta_reduce
  rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, mul_assoc]

end Kernel

theorem l2_sum_eq_sum_norm_sq_of_orthogonal {X I : Type} [MeasurableSpace X] [Fintype I] (μ : Measure X) (𝓖 : Set X) (w : I → ℂ) (k : I → X → ℂ) (F T : X → ℂ)
    (hT : ∀ g, T g = ∑ j, w j * k j g) (hi : ∀ j, IntegrableOn (fun g => k j g * starRingEnd ℂ (F g)) 𝓖 μ) :
    l2 μ 𝓖 T F = ∑ j, w j * l2 μ 𝓖 (k j) F := by
  unfold l2 Lift.pet
  simp only [hT, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun j _ => (hi j).const_mul _]
  simp only [integral_const_mul]

theorem l2_eq_star {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓖 : Set X) (F T : X → ℂ) :
    l2 μ 𝓖 T F = ∫ g in 𝓖, star (F g) * T g ∂μ := by
  unfold l2 Lift.pet
  simp only [mul_comm]
  rfl

end GlobalTheory.AdelicScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulMatrixMulVecCompletedSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.LatMatch

theorem exists_nat_mul_intAf' {F : Type} [Field F] [NumberField F] (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    ∃ m : ℕ, 0 < m ∧ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * t ∈ intAf F := by
  obtain ⟨m, hm, h⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_intAd t
  exact ⟨m, hm, fun v => h v⟩

set_option maxHeartbeats 1000000 in
theorem exists_nat_smul_intAE {D : D7} (w : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ k : ℕ, 0 < k ∧ k • w ∈ intAE D := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul β z =>
    obtain ⟨m, hm, hβ⟩ := exists_nat_mul_intAf' β
    obtain ⟨M, hM, o, ho⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_mem z
    refine ⟨m * M, Nat.mul_pos hm hM, ?_⟩
    have e : (m * M) • (β ⊗ₜ[D.host.F] z) = ((m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * β) ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E) := by
      have ho' : ((o : 𝓞 D.host.E) : D.host.E) = (M : D.host.E) * z := ho
      rw [ho', mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, nsmul_eq_mul]
    rw [e]
    exact AddSubgroup.subset_closure ⟨_, hβ, o, rfl⟩
  | add w w' h h' =>
    obtain ⟨k, hk, m⟩ := h
    obtain ⟨k', hk', m'⟩ := h'
    refine ⟨k * k', Nat.mul_pos hk hk', ?_⟩
    have e : (k * k') • (w + w') = k' • (k • w) + k • (k' • w') := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm k' k]
    rw [e]
    exact add_mem (nsmul_mem m k') (nsmul_mem m' k)

theorem exists_nat_smul_single {D : D7} (V : HSp D) :
    ∃ b : ℕ, 0 < b ∧ ∀ j : Fin V.rank, (Pi.single j (b : D.host.E) : Fin V.rank → D.host.E) ∈ GlobalTheory.Member.latC V := by
  classical
  have hspan := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.1
  have key : ∀ v : Fin V.rank → D.host.E, ∃ m : ℕ, 0 < m ∧ (m : D.host.E) • v ∈ GlobalTheory.Member.latC V := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
      rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨k, hk, hky⟩ := hy
      refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
      have e : ((m * k : ℕ) : D.host.E) • (x + y) = k • ((m : D.host.E) • x) + m • ((k : D.host.E) • y) := by
        simp only [smul_add, Nat.cast_mul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul]
        rw [mul_comm (k : D.host.E) (m : D.host.E)]
      rw [e]
      exact add_mem (Submodule.smul_of_tower_mem _ k hmx) (Submodule.smul_of_tower_mem _ m hky)
    | smul c x _ hx =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨d, hd, hdc⟩ := GlobalTheory.SmoothForms.Reduce.exists_nat_integral (fun _ : Unit => c)
      refine ⟨d * m, Nat.mul_pos hd hm, ?_⟩
      have e : ((d * m : ℕ) : D.host.E) • (c • x) = (⟨(d : D.host.E) * c, (mem_integralClosure_iff _ _).2 (hdc ())⟩ : 𝓞 D.host.E) • ((m : D.host.E) • x) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def]
        change (((d * m : ℕ) : D.host.E)) * (c * x i) = ((d : D.host.E) * c) * ((m : D.host.E) * x i)
        push_cast
        ring
      rw [e]
      exact (GlobalTheory.Member.latC V).smul_mem _ hmx
  choose m hm hmv using fun j : Fin V.rank => key (Pi.single j 1)
  refine ⟨∏ j, m j, Finset.prod_pos fun j _ => hm j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have : (Pi.single j (((∏ i ∈ Finset.univ.erase j, m i) * m j : ℕ) : D.host.E) : Fin V.rank → D.host.E) =
      (∏ i ∈ Finset.univ.erase j, m i) • ((m j : D.host.E) • Pi.single j 1) := by
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  rw [this]
  exact Submodule.smul_of_tower_mem _ _ (hmv j)

theorem mul_mem_intAE' (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mulVec_lamHat_bound : ∀ {D : D7} (V V' : HSp D) (X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' X
  classical
  obtain ⟨m, hm, hden⟩ := GlobalTheory.SmoothForms.Reduce.den_hat (D := D) (GlobalTheory.Member.latC V)
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.1
  choose k hk hkX using fun p : Fin V'.rank × Fin V.rank => exists_nat_smul_intAE (D := D) (X p.1 p.2)
  have hc : 0 < ∏ p, k p := Finset.prod_pos fun p _ => hk p
  have hcX : ∀ j i, (∏ p, k p) • X j i ∈ intAE D := by
    intro j i
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, i)), mul_smul]
    exact nsmul_mem (hkX (j, i)) _
  obtain ⟨b, hb, hbs⟩ := exists_nat_smul_single V'
  refine ⟨b * ((∏ p, k p) * m), Nat.mul_pos hb (Nat.mul_pos hc hm), fun y hy => ?_⟩
  have hy' : ∀ i, m • y i ∈ intAE D := hden y (by rw [← GlobalTheory.LatDual.lamHat_eq_hat]; exact hy)
  have hw : ∀ j, ((∏ p, k p) * m) • X.mulVec y j ∈ intAE D := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum]
    refine sum_mem fun i _ => ?_
    have := mul_mem_intAE' D (hcX j i) (hy' i)
    convert this using 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hV' : ∀ w : Fin V'.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (∀ j, w j ∈ intAE D) →
      (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) ∈ Formalism.L2.NTheta.LamHat V' := by
    intro w hw
    have e : (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) = ∑ l, (fun j => w l *
        ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single l (b : D.host.E) : Fin V'.rank → D.host.E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.natCast_def', mul_comm]
      · intro l _ hl
        rw [Pi.single_eq_of_ne (Ne.symm hl), TensorProduct.tmul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [e]
    refine sum_mem fun l _ => GlobalTheory.LatDual.smul_mem_lamHat V' _ (hw l) _ ?_
    refine AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, _, ?_, rfl⟩
    have h := (GlobalTheory.Member.mem_latC V' _).1 (hbs l)
    rw [Module.Basis.equivFun_symm_apply] at h
    exact h
  have := hV' _ hw
  convert this using 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  ring

end GlobalTheory.LatMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CMTraceZero

theorem exists_ne_zero_conj_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨_, hc, _, hτ⟩ := hB.cm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hw := hc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ w.embedding x
    rw [hall x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMTraceZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CommonModel


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.CommonModel.isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s) : IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.CommonModel.exists_common {R : Type} [CommRing R] {Y W₀ : Scheme.{0}}
    (s₀ : W₀ ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s₀) (i₀ : Y ⟶ W₀)
    {ι : Type} (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (f : ∀ i, Y ⟶ P i)
    (hp : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = i₀ ≫ s₀) (S : Finset ι) :
    ∃ (W : Scheme.{0}) (h : Y ⟶ W) (r : W ⟶ W₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (r ≫ s₀) ∧ h ≫ r = i₀ ∧
      ∀ i ∈ S, ∃ g : W ⟶ P i, h ≫ g = f i ∧ g ≫ p i = r ≫ s₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨W₀, i₀, 𝟙 W₀, by simpa using hs₀, by simp, by simp⟩
  | insert j S _ ih =>
    obtain ⟨W, h, r, hr, hhr, hg⟩ := ih
    have hc : h ≫ (r ≫ s₀) = f j ≫ p j := by
      rw [← Category.assoc, hhr, hf]
    refine ⟨pullback (r ≫ s₀) (p j), pullback.lift h (f j) hc, pullback.fst _ _ ≫ r, ?_, ?_, ?_⟩
    · rw [Category.assoc]
      exact _root_.GlobalTheory.ProjSpace.isProjOver_pullback hr (hp j)
    · rw [← Category.assoc, pullback.lift_fst, hhr]
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨pullback.snd _ _, pullback.lift_snd _ _ _, ?_⟩
        rw [Category.assoc, ← pullback.condition]
      · obtain ⟨g, hg₁, hg₂⟩ := hg i hi
        refine ⟨pullback.fst _ _ ≫ g, ?_, ?_⟩
        · rw [← Category.assoc, pullback.lift_fst, hg₁]
        · rw [Category.assoc, hg₂, Category.assoc]

end GlobalTheory.CommonModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVariableMultiplicationMemSpanHeisenbergOperaStatement
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVariableMultiplication_mem_span_heisenbergOperators : ∀ {P Q R S : ℕ} (l : Ln P Q R S), LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈ Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := by
  first | exact @GlobalTheory.MulVarSpan.mulX_mem_span | exact GlobalTheory.MulVarSpan.mulX_mem_span | (intros; apply GlobalTheory.MulVarSpan.mulX_mem_span <;> assumption)
end

