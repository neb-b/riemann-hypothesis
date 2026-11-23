module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0785
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisationDefiniteRealPointFockVectorAction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealFockActionP

section Vac

open Matrix GlobalTheory.VacuumCharacter GlobalTheory.RealFockAction
open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem om_vac_of {B : Base S T} {χ : (AE D)ˣ →* Circle} {ω : PairRep S T} (hB : B.Good)
    (hω : IsWeilDatumO B.F.ψ S T χ (χ * B.eta⁻¹) ω)
    (hχ : ∀ τ, HasInfExp D χ τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S) :
    ω (u, 1) f = (((detFam B.w.c (realGL B.F.θ S u))⁻¹ : ℂˣ) : ℂ) • f := by
  have hθ := hB.frame.vac.2.inf
  have hS := fun τ => GlobalTheory.FockBasis.isCartanInv_one (onb_posDef (hB.frame.onbS τ))
  have hT := hB.frame.cartT
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have hpq : ∀ τ, B.w.p τ + B.w.q τ = T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    simpa using (Fintype.card_congr e).symm
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (B.F.sT τ) (hT τ).1
  have ep : ∀ τ, p τ = B.w.p τ := fun τ => by
    have h1 := hB.frame.onbT τ
    rw [← hB.sig τ] at h1
    have h2 := (onb_laws h1 (hpq τ ▸ Nat.le_add_right _ _)).2
    rw [hp] at h2
    have h3 : (p τ : ℂ) = B.w.p τ := by linear_combination h2 / 2
    exact_mod_cast h3
  rw [_root_.GlobalTheory.WeilVacChar.vacuum_character D B.F.ψ hω.std S T B.F.θ hθ _ _ ω B.eta hB.eta hω (fun _ => 1) B.F.sT hS hT u hu 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (χ * B.eta⁻¹ * (B.eta ^ T.rank)⁻¹) τ ((B.w.c τ - p τ : ℤ) : ℚ) := fun τ => by
    have h1 := hasInfExp_twist (hasInfExp_twist (hχ τ) (hB.eta.2.2.2 τ) 1) (hB.eta.2.2.2 τ) T.rank
    rw [pow_one] at h1
    convert h1 using 1
    rw [← hpq τ, ep]
    push_cast
    ring
  rw [MonoidHom.map_one, mul_one, Circle.coe_inv, hxv _ _ hexp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    Units.val_inv_eq_inv_val]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := B.F.θ) τ u)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [one, (hd τ _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, mul_one, ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_one, one_pow,
    one_mul, show (realGL B.F.θ S u τ).val = compAt B.F.θ τ (Formalism.L2.Theta.mt S u) from rfl, zpow_sub₀ g0, zpow_natCast,
    inv_pow]
  have := pow_ne_zero (p τ) g0
  have := zpow_ne_zero (B.w.c τ) g0
  field_simp

theorem om_fock_of {B : Base S T} {χ : (AE D)ˣ →* Circle} {ω : PairRep S T} (hB : B.Good)
    (hω : IsWeilDatumO B.F.ψ S T χ (χ * B.eta⁻¹) ω)
    (hχ : ∀ τ, HasInfExp D χ τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hB.frame.vac.2.inf
  have hBS := fun τ => onb_posDef (hB.frame.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, om_vac_of hB hω hχ hf hv hu, GlobalTheory.FiniteFock.pureTensorO_smul,
    pureTensorO_subst (p := B.w.p) hB.frame.vac.1 hθ (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hB.frame.cartT
      (fun τ => (onb_laws (by have := hB.frame.onbT τ; rwa [← hB.sig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

end Vac

theorem om_fock_vP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m) (t : T0) (B : Base (Vc D j) (Wc D j)), R.IsThP → B.Good → B.F.ψ = R.ψ → B.F.θ = R.θ → B.F.sT = cart (R.MW j (sg0 D A)) → (∀ τ, (B.F.BS τ).val = R.BV j τ) → B.F.BT = onb (R.MW j (sg0 D A)) → B.eta = R.eta → (∀ τ, HasInfExp D (R.toLevCh.mu t ((j : ℕ) + 1)) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2)) → ∀ u ∈ GinfC (Vc D j), ∀ P, R.ωP j t (u, 1) (R.ptP j t P) = R.ptP j t (B.act u P) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R j t B hP hB hψ hθ hsT hBS hBT heta hχ u hu P
  have hfock : ∀ Q, R.ptP j t Q = B.F.fock (R.vP j t) Q := fun Q => by
    unfold RealDat.ptP
    rw [Frame.fock, hψ, hθ, hsT, hBT, funext hBS]
  have hf : IsThetaFunO B.F.ψ (Vc D j) (Wc D j) (R.vP j t) := by
    have := hP.pt_theta j t 1
    unfold RealDat.ptP pureTensorO at this
    rw [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
    rwa [hψ]
  have hv : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D j) (Wc D j)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP j t) := by
    rw [hψ, hθ, hsT]
    rw [hψ] at hf
    exact GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hP.vP j t) hf
  have hω : IsWeilDatumO B.F.ψ (Vc D j) (Wc D j) (R.toLevCh.mu t ((j : ℕ) + 1))
      (R.toLevCh.mu t ((j : ℕ) + 1) * B.eta⁻¹) (R.ωP j t) := by
    rw [hψ, heta]
    exact hP.ωP j t
  rw [hfock, hfock]
  exact GlobalTheory.RealFockActionP.om_fock_of hB hω hχ hf hv hu P

end GlobalTheory.RealFockActionP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanOfCoefficientSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Decomp

variable {D : D7}

theorem heisO_lin_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f - g) = heisO ψ S T x f - heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_sub]; rfl

theorem heisO_lin_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f + g) = heisO ψ S T x f + heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_add (f := _)]; rfl

theorem heisO_lin_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) :
    heisO ψ S T x (0 : WO S T → ℂ) = 0 := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_zero]

theorem theta_of_mem_span {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {𝒯 : Set (WO S T → ℂ)}
    (h0 : IsThetaFunO ψ S T 0) (h𝒯 : ∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) {φ : WO S T → ℂ} (hφ : φ ∈ Submodule.span ℂ 𝒯) : IsThetaFunO ψ S T φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h𝒯 x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact theta_add hx hy
  | smul c x _ hx => exact theta_smul c hx

theorem exists_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) (X : Finset (WO S T))
    (hX : ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨
      ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f) :
    ∃ L : WO S T → ((WO S T → ℂ) →ₗ[ℂ] ℂ), (∀ x₁, InvForm ψ S T a (L x₁)) ∧
      ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
        ℓ (heisO ψ S T x f) = ∑ x₁ ∈ X, L x₁ (heisO ψ S T x f) * ℓ (heisO ψ S T x₁ f) := by
  classical
  let K : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ
    {h | ∃ u g, IsHalf (cA D a) u ∧ IsThetaFunO ψ S T g ∧ h = heisO ψ S T u g - g}
  have inv_iff : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, InvForm ψ S T a ℓ ↔ K ≤ LinearMap.ker ℓ := by
    intro ℓ
    constructor
    · intro hℓ
      rw [Submodule.span_le]
      rintro h ⟨u, g, hu, hg, rfl⟩
      simp [LinearMap.mem_ker, map_sub, hℓ u hu g hg]
    · intro hle u hu g hg
      have := hle (Submodule.subset_span ⟨u, g, hu, hg, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      exact this
  have inv_comp : ∀ μ : ((WO S T → ℂ) ⧸ K) →ₗ[ℂ] ℂ, InvForm ψ S T a (μ ∘ₗ K.mkQ) := by
    intro μ
    rw [inv_iff]
    intro h hh
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero K).2 hh]
  let Fq : WO S T → (WO S T → ℂ) ⧸ K := fun x => K.mkQ (heisO ψ S T x f)
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) ⧸ K :=
    ∑ x₁ ∈ X, (LinearMap.proj x₁ : (WO S T → ℂ) →ₗ[ℂ] ℂ).smulRight (Fq x₁)
  have hA : ∀ c, A c = ∑ x₁ ∈ X, c x₁ • Fq x₁ := by
    intro c
    simp [A, LinearMap.sum_apply]
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range A).subtype (Submodule.ker_subtype _)
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.rangeRestrict (LinearMap.range_rangeRestrict A)
  let s := g ∘ₗ p
  have hs : ∀ q ∈ LinearMap.range A, A (s q) = q := by
    intro q hq
    have h1 : p q = ⟨q, hq⟩ := by
      have := LinearMap.congr_fun hp ⟨q, hq⟩
      simpa using this
    have h2 := LinearMap.congr_fun hg (p q)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    have h3 : A (g (p q)) = ((A.rangeRestrict (g (p q)) : LinearMap.range A) : (WO S T → ℂ) ⧸ K) := rfl
    simp only [s, LinearMap.comp_apply]
    rw [h3, h2, h1]
  refine ⟨fun x₁ => (LinearMap.proj x₁ ∘ₗ s) ∘ₗ K.mkQ, fun x₁ => inv_comp _, ?_⟩
  intro ℓ hℓ x hx
  have hle := (inv_iff ℓ).1 hℓ
  have hmem : Fq x ∈ LinearMap.range A := by
    rcases hX x hx with h0 | ⟨x₁, hx₁, he⟩
    · have : Fq x = 0 := by
        rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
        intro μ
        exact h0 (μ ∘ₗ K.mkQ) (inv_comp μ)
      rw [this]
      exact Submodule.zero_mem _
    · refine ⟨Pi.single x₁ 1, ?_⟩
      rw [hA, Finset.sum_eq_single x₁]
      · simp [Fq, he]
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd hx₁ h
  have key := congrArg (K.liftQ ℓ hle) (hs _ hmem)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hA, map_sum] at key
  simp only [map_smul, smul_eq_mul] at key
  have hb : ∀ y, K.liftQ ℓ hle (Fq y) = ℓ (heisO ψ S T y f) := fun y => rfl
  simp only [hb] at key
  rw [← key]
  rfl

theorem mem_span_of_coef_mem_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ 𝒢 𝒯 : Set (WO S T → ℂ), (∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) → (∀ Ψ ∈ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f)) → (∀ ℓ, InvForm ψ S T a ℓ → coef ψ S T a ℓ f ∈ Submodule.span ℂ 𝒢) → f ∈ Submodule.span ℂ 𝒯 := by
  intro D ψ S T hψ a ha f hf 𝒢 𝒯 h𝒯 h𝒢 hcoef
  obtain ⟨-, -, X, hXh, hX⟩ := _root_.GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform D ψ S T hψ (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) a ha f hf
  obtain ⟨L, hLinv, hL⟩ := exists_decomp ψ S T a f X hX
  have hspan : ∀ Ψ ∈ Submodule.span ℂ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ →
      ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f) := by
    intro Ψ hΨ x₁ hx₁
    induction hΨ using Submodule.span_induction with
    | mem Ψ hΨ => exact h𝒢 Ψ hΨ x₁ hx₁
    | zero => exact ⟨0, Submodule.zero_mem _, fun ℓ _ x _ => by simp [heisO_lin_zero]⟩
    | add Ψ₁ Ψ₂ _ _ h1 h2 =>
      obtain ⟨φ₁, m1, e1⟩ := h1
      obtain ⟨φ₂, m2, e2⟩ := h2
      refine ⟨φ₁ + φ₂, add_mem m1 m2, fun ℓ hℓ x hx => ?_⟩
      rw [heisO_lin_add, map_add (f := _), e1 ℓ hℓ x hx, e2 ℓ hℓ x hx, Pi.add_apply, add_mul]
    | smul c Ψ _ h =>
      obtain ⟨φ, m, e⟩ := h
      refine ⟨c • φ, Submodule.smul_mem _ c m, fun ℓ hℓ x hx => ?_⟩
      rw [GlobalTheory.SplitScalar.heisO_smul, map_smul, e ℓ hℓ x hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hφ : ∀ x₁ ∈ X, ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
      ℓ (heisO ψ S T x φ) = coef ψ S T a (L x₁) f x * ℓ (heisO ψ S T x₁ f) :=
    fun x₁ hx₁ => hspan _ (hcoef _ (hLinv x₁)) x₁ (hXh x₁ hx₁)
  choose! φ hφm hφe using hφ
  have hsum : (∑ x₁ ∈ X, φ x₁) ∈ Submodule.span ℂ 𝒯 := Submodule.sum_mem _ hφm
  have h0 : IsThetaFunO ψ S T 0 := by simpa using theta_sub hf hf
  have hzero := GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hψ a ha (f - ∑ x₁ ∈ X, φ x₁)
    (theta_sub hf (theta_of_mem_span h0 h𝒯 hsum)) (by
      intro ℓ hℓ x hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [heisO_lin_sub, GlobalTheory.SplitScalar.heisO_sum, map_sub, map_sum, hL ℓ hℓ x hx, sub_eq_zero]
      refine Finset.sum_congr rfl fun x₁ hx₁ => ?_
      rw [hφe x₁ hx₁ ℓ hℓ x hx, coef, if_pos hx])
  rw [sub_eq_zero] at hzero
  exact hzero ▸ hsum

end GlobalTheory.DownLift.SplitCoef.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorIsThetaFunctionTwoStepModel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwoStepModel

open GlobalTheory.ExportSeries

theorem datum_eq_tensorHalf {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Q : Finset (Pl D.host.E)} {eg eQ : AE D} (hg : IsIdemSum eg Pg) (hq : IsIdemSum eQ Q) (hd : Disjoint Pg Q)
    (he : IsIdemSum (eg + eQ) (Pg ∪ Q)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (fun x => if IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) =
      tensorHalf (cA D eQ) (cA D eg)
        (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) else 0)
        (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) := by
  have hA := _root_.GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff D S T βS βT Pg Q eg eQ hg hq hd he
  have hB := _root_.GlobalTheory.TwoStepRed.redM_twoStep D S T βS βT Pg Q eg eQ hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO S T, IsHalf (cA D eg) (cA D eg • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO S T, IsHalf (cA D eQ) (cA D eQ • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [tensorHalf_apply]
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add (f := _), add_comm]
  by_cases hx : IsHalf (cA D (eg + eQ)) x
  · have hx' : IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj S T βS βT x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      have c1 : IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) := ⟨hx, hi⟩
      have c2 : IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x)) := ⟨hcQ x, i2⟩
      have c3 : IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x)) := ⟨hcg x, i1⟩
      rw [if_pos c1, if_pos c2, if_pos c3, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x))) := fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end GlobalTheory.TwoStepModel

namespace GlobalTheory.ConjTwist

theorem isThetaAt_vP_twoStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t eg eQ fg hg hq hfg
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hd := GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    (R.Q t) (fun y => omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add (f := _), add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he (R.xiR t)]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.ConjTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DeltaRange

theorem delta_value_mem_range : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ), ∃ a : FractionRing (X.O i), ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  intro D N X ρ hρ i j b z
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker : Set (G D.host.E N.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker = (X.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact X.delta_open i
  have : Finite (G D.host.E N.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (X.O i) (FractionRing (X.O i))
    (algebraMap (X.O0 i) (X.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (X.delta i) σ : (X.O0 i)ˣ) : X.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (X.O0 i) (X.O i))) hopen hσ hn hpow).symm

end GlobalTheory.DeltaRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesMemPlacesOverGenerators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePlacesOver

theorem mem_placesOver : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ P ∈ Rl.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC P hP
  obtain ⟨k, hk⟩ := (hC.lev.Pg P).1 hP
  refine ⟨k, ?_⟩
  have h1 := Rl.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ P.asIdeal := h1
  simpa [placesOver] using h2

end GlobalTheory.TypePlacesOver
end

