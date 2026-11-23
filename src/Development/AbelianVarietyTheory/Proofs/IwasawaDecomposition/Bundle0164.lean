module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSecNormCoeffLocal
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

noncomputable section

namespace GlobalTheory.NormalDescent

open TopologicalSpace Opposite GlobalTheory.LBGerm GlobalTheory.FiniteAmple

theorem injective_res_of_isAffineOpen {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)]
    (h : W ≤ V) {x : X} (hx : x ∈ W) : Function.Injective (X.presheaf.map (homOfLE h).op).hom := by
  have hxV : x ∈ V := h hx
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hinj : Function.Injective (X.presheaf.germ V x hxV).hom :=
    IsLocalization.injective (M := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl) (S := X.presheaf.stalk x)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  intro a b e
  apply hinj
  rw [← X.presheaf.germ_res (homOfLE h) x hx]
  simp only [CommRingCat.comp_apply, e]

theorem exists_sec_normCoeff_local : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {M : LB X}, M.IsLB → ∀ t : (M.pull f).Sec, ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : IsDomain Γ(X, V)) (_ : IsIntegrallyClosed Γ(X, V))
        (τ : Γ(Y, f ⁻¹ᵁ V)), x ∈ V ∧ (∀ y : Y, f y ∈ V → (y ∈ nonzeroLocus t ↔ y ∈ Y.basicOpen τ)) ∧
        ∀ (k : ℕ) (z : X), z ∈ V →
          (z ∈ nonzeroLocus (u k) ↔ z ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)) := by
  intro X Y f _ _ _ M hM t
  let α : Type := {p : X.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2 ∧ IsIrreducible (p.1 : Set X)}
  have nd : ∀ a : α, IsDomain Γ(X, a.1.1) ∧ IsIntegrallyClosed Γ(X, a.1.1) := fun a =>
    GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible a.2.2.2
  have cov : ∀ x : X, ∃ a : α, x ∈ a.1.1 := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hM x
    have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents x)
    obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := M.U i ⊓ ⟨_, hC⟩) (x := x)
      ⟨hi, mem_irreducibleComponent⟩
    have hle : V ≤ M.U i ⊓ ⟨_, hC⟩ := hle
    exact ⟨⟨(V, i), hV, hle.trans inf_le_left, ⟨⟨x, hx⟩,
      (isIrreducible_irreducibleComponent (x := x)).2.open_subset V.isOpen fun q hq => (hle hq).2⟩⟩, hx⟩
  have le : ∀ a : α, f ⁻¹ᵁ a.1.1 ≤ (M.pull f).U fun _ => a.1.2 := fun a y hy => mem_pull.2 (a.2.2.1 hy)
  let τ : ∀ a : α, Γ(Y, f ⁻¹ᵁ a.1.1) := fun a => resG Y (le a) (t.f fun _ => a.1.2)
  let c : ∀ (k : ℕ) (a : α), Γ(X, a.1.1) := fun k a =>
    haveI := (nd a).1
    normCoeff (f.app a.1.1).hom (f.finite_app _ a.2.1) (τ a) k
  have key : ∀ k (x : X) (a b : α), x ∈ a.1.1 → x ∈ b.1.1 → gs (𝟙 X) x _ (c k a) =
      (gm (𝟙 X) x (M.U a.1.2 ⊓ M.U b.1.2) (M.g a.1.2 b.1.2)).val ^ k * gs (𝟙 X) x _ (c k b) := by
    intro k x a b ha hb
    obtain ⟨W, hW, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := a.1.1 ⊓ b.1.1) (x := x) ⟨ha, hb⟩
    have hle : W ≤ a.1.1 ⊓ b.1.1 := hle
    have la : W ≤ a.1.1 := hle.trans inf_le_left
    have lb : W ≤ b.1.1 := hle.trans inf_le_right
    have lg : W ≤ M.U a.1.2 ⊓ M.U b.1.2 := le_inf (la.trans a.2.2.1) (lb.trans b.2.2.1)
    have hWi : IsIrreducible (W : Set X) := ⟨⟨x, hx⟩, a.2.2.2.2.open_subset W.isOpen la⟩
    obtain ⟨_, _⟩ := GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWi
    obtain ⟨_, _⟩ := nd a
    obtain ⟨_, _⟩ := nd b
    have ea := GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout _ _ _ _ (isPushout_app f a.2.1 hW la) (injective_res_of_isAffineOpen a.2.1 la hx)
      (f.finite_app _ a.2.1) (f.finite_app _ hW) (τ a) k
    have eb := GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout _ _ _ _ (isPushout_app f b.2.1 hW lb) (injective_res_of_isAffineOpen b.2.1 lb hx)
      (f.finite_app _ b.2.1) (f.finite_app _ hW) (τ b) k
    have eτ : resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ a.1.1 from fun _ hy => la hy) (τ a) =
        (f.app W).hom (resG X lg (M.g a.1.2 b.1.2).val) *
          resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ b.1.1 from fun _ hy => lb hy) (τ b) := fn_ext fun y hy => by
      have hy' : (𝟙 Y ≫ f) y ∈ W := hy
      rw [gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y (le a) (la hy),
        gs_res (𝟙 Y) y (le b) (lb hy), gs_pull (𝟙 Y) f y W hy, gs_res (𝟙 Y ≫ f) y _ hy',
        gs_unit (𝟙 Y ≫ f) y _ (lg hy'),
        ← gm_pull_g M f (𝟙 Y) y (fun _ => a.1.2) (fun _ => b.1.2) (le a (la hy)) (le b (lb hy))]
      exact gs_compat t (𝟙 Y) y (le a (la hy)) (le b (lb hy))
    have e : resG X la (c k a) = resG X lg (M.g a.1.2 b.1.2).val ^ k * resG X lb (c k b) :=
      ea.trans ((congrArg (fun z => normCoeff (f.app W).hom (f.finite_app _ hW) z k) eτ).trans
        ((_root_.GlobalTheory.NormalDescent.normCoeff_mul _ _ _ _ k).trans (congrArg (_ * ·) eb.symm)))
    have e' := congrArg (gs (𝟙 X) x W) e
    rwa [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit _ x _ (lg hx)] at e'
  choose u hu using fun k => exists_sec_of_refinement (isLB_lbPow hM k) (fun a : α => a.1.1)
    (fun a _ => a.1.2) (fun a x hx => mem_powChart.2 (a.2.2.1 hx)) cov (c k) fun x a b ha hb => by
      rw [gm_lbPow_g k (𝟙 X) x _ _ (mem_powChart.2 (a.2.2.1 ha)) (mem_powChart.2 (b.2.2.1 hb)),
        Units.val_pow_eq_pow_val]
      exact key k x a b ha hb
  refine ⟨u, fun x => ?_⟩
  obtain ⟨a, ha⟩ := cov x
  refine ⟨a.1.1, a.2.1, (nd a).1, (nd a).2, τ a, ha, fun y hy => ?_, fun k z hz => ?_⟩
  · have hy : y ∈ f ⁻¹ᵁ a.1.1 := hy
    rw [mem_nonzeroLocus_iff_isUnit t (le a hy), ← gs_res (𝟙 Y) y (le a) hy]
    exact isUnit_gs_iff (𝟙 Y) y _ hy _
  · have hJ : z ∈ (lbPow M k).U fun _ => a.1.2 := mem_powChart.2 (a.2.2.1 hz)
    rw [mem_nonzeroLocus_iff_isUnit (u k) hJ, hu k z _ a hJ hz, Units.isUnit_units_mul]
    exact isUnit_gs_iff (𝟙 X) z _ hz _

end GlobalTheory.NormalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSectionCompatibleSquareThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionLimitSq

section Flat

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem good_sq_iff (z : Z) (J' : (Z ⟶ X) → L.ι) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) z (fun ψ _ => J' ψ) ↔ Good L z J' := by
  constructor
  · intro h ψ
    have := GlobalTheory.Algebraise.mem_wc.1 (h ψ)
    simpa using this
  · intro h ψ
    exact GlobalTheory.Algebraise.mem_wc.2 (by simpa using h ψ)

theorem eq_const_of_fin_one {α β : Type} (J : α → (Fin 1 → β)) : J = fun ψ _ => J ψ 0 :=
  funext fun ψ => funext fun κ => congrArg (J ψ) (Subsingleton.elim _ _)

theorem sval_flat {a n m : ℤ} {g : Y ⟶ X} {t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))}
    {s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g)
      (fun _ => n))}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j →
      gs r z _ (t.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j))
    (r : Z ⟶ Y) (z : Z) (J' : (Z ⟶ X) → L.ι) (hJ : Good L z J') :
    sval t r z J' = sval s r z (fun ψ _ => J' ψ) :=
  h Z r z (J' (r ≫ g)) (by simpa using hJ (r ≫ g))

end Flat

theorem existsUnique_sec_of_compatible_sq : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hm : (((2 * n : ℕ) : ℤ)) = 2 * (n : ℤ) := by push_cast; ring
  have hn2 : 1 ≤ 2 * n := by omega
  choose t ht using fun e => GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (fstG I e P.A).left (s e)
  have htc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι),
      Good P.L z J → sval (t (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (t e) r z J := by
    intro e Z r z J hJ
    rw [sval_flat (ht (e + 1)) _ z J hJ, sval_flat (ht e) r z J hJ]
    exact hs e Z r z _ ((good_sq_iff z J).2 hJ)
  obtain ⟨σ₀, hσ₀, hσ₀u⟩ := GlobalTheory.SectionLimit.existsUnique_sec_of_compatible hS R I P (2 * n) hn2 t htc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.linComb_pow_section_unflatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ₀
  refine ⟨σ, fun e Z r z J hJ => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨J', rfl⟩ : ∃ J' : (Z ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff z J').1 hJ
    rw [← sval_flat hσ _ z J' hJ', hσ₀ e Z r z J' hJ', sval_flat (ht e) r z J' hJ']
  · obtain ⟨τ, hτ⟩ := GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ'
    have hτσ : τ = σ₀ := hσ₀u τ fun e Z r z J hJ => by
      rw [sval_flat hτ _ z J hJ, hσ' e Z r z _ ((good_sq_iff z J).2 hJ), ← sval_flat (ht e) r z J hJ]
    have hL := LB.isLB_linComb P.isLB (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (2 : ℤ))
    refine DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    obtain ⟨J', rfl⟩ : ∃ J' : (P.A.left ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff y J').1 hJ
    rw [← sval_flat hτ _ y J' hJ', ← sval_flat hσ _ y J' hJ', hτσ]

end GlobalTheory.SectionLimitSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOThZeroTriv
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker Complex Classical
open Formalism.L2.Th1.H (matH alphaQ qOf opU slice pow4)
open scoped BigOperators ComplexConjugate Real

namespace WeilVac

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem kappa_ne_zero {γ₀ : IsoK D} (k : KapChoice γ₀) : k.kappa ≠ 0 := by
  refine finprod_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => zpow_ne_zero _ ?_
  intro h0
  have h1 := k.rt_pow p p.2.1 p.2.2
  have hpi : k.pi p ≠ 0 := by
    intro h
    have h2 := k.pi_gen p p.2.1 p.2.2
    rw [h, Ideal.span_singleton_zero] at h2
    exact pow_ne_zero _ (k.pp p).ne_bot h2
  have hE : (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) ≠ 0 := by
    set_option synthInstance.maxHeartbeats 200000 in
      simpa using hpi
  rw [h0, zero_pow (mul_ne_zero two_ne_zero (classNumber_ne_zero _))] at h1
  exact div_ne_zero ((map_ne_zero _).2 hE) ((map_ne_zero _).2 ((map_ne_zero _).2 hE)) h1.symm

theorem thMM_spec (B : Formalism.L2.Ker.Base D cc δ) (h : B.StdOK) : B.IsThMM B.thMM ∧ B.thMM ≠ 0 := by
  obtain ⟨e, u⟩ := ThetaVec.thetaVector _ _ _ _ _ _ _ _ h _ (kappa_ne_zero B.kc)
  have h1 : B.IsThMM B.thMM := Classical.epsilon_spec (p := IsThM B.L B.ω₀ B.cq B.lamM B.gC B.kappa) e
  exact ⟨h1, (u _ h1.1 h1.2).1⟩

theorem areaOK (B : Formalism.L2.Ker.Base D cc δ) : B.AreaOK := by
  rw [Formalism.L2.Ker.Base.AreaOK, ThetaVec.area_eq]
  exact GlobalTheory.OddTheta.area_eq B.L _ fun z => by rw [← B.lat]; rfl

theorem q_int (B : Formalism.L2.Ker.Base D cc δ) (h : B.StdOK) {x : D.what₂.Tau → ℂ} (hx : x ∈ B.lamM) :
    ∃ m : ℤ, qOf B.cq (matH (hOne B.L D.what₂.Tau)) x = m := by
  have hs : ∀ a, slice a (0 : Fin 4 × D.what₂.Tau → ℂ) = 0 := fun _ => rfl
  have h1 := h.betaSemi.1 (B.gC (ThetaVec.ins 0 x)) ⟨ThetaVec.ins 0 x, fun a => by
    rw [ThetaVec.slice_ins]; split_ifs; exacts [hx, B.lamM.zero_mem], rfl⟩
  rw [h.betaAlpha, ← mul_self_eq_one_iff] at h1
  simp only [ThetaVec.slice_ins, Fin.prod_univ_four, hs, h.alpha0, Fin.isValue, if_true, Fin.reduceEq, if_false,
    mul_one] at h1
  rw [alphaQ, ← Complex.exp_add, Complex.exp_eq_one_iff] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨m, ?_⟩
  have : (qOf B.cq (matH (hOne B.L D.what₂.Tau)) x : ℂ) = m := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    linear_combination hm
  exact_mod_cast this

theorem entry_mem (B : Formalism.L2.Ker.Base D cc δ) {N N' : ℕ} {x : VC D N N'}
    (hx : x ∈ La D (tor0 D cc δ) (stdL D N) (stdL D N')) : x ∈ powLat B.lamM N N' := by
  refine (AddSubgroup.closure_le _).2 ?_ hx
  rintro _ ⟨w, hw, A, hA, rfl⟩ i j
  exact AddSubgroup.subset_closure ⟨w, hw, A i j, (GlobalTheory.OddGenus.mem_iff_entries D N N' A).1 hA i j, rfl⟩

theorem Hf_eq (B : Formalism.L2.Ker.Base D cc δ) {N N' : ℕ} (z w : VC D N N') :
    Hf D (tor0 D cc δ) z w =
      ∑ i, ∑ j, matH (hOne B.L D.what₂.Tau) (fun τ => z τ i j) (fun τ => w τ i j) := by
  have hA : area (tor0 D cc δ).abelian₂ = latticeArea B.L := (areaOK B).trans (ThetaVec.area_eq _)
  have e : ∀ u v : D.what₂.Tau → ℂ, matH (hOne B.L D.what₂.Tau) u v =
      ∑ τ, u τ * conj (v τ) / (latticeArea B.L : ℂ) := fun u v => ThetaVec.stdH_apply B.L u v
  simp only [e, Hf, hA, Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem thZero_mem (B : Formalism.L2.Ker.Base D cc δ) (h : B.StdOK) (N N' : ℕ) :
    B.thZero N N' ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N') := by
  have hθ := (thMM_spec B h).1.1
  refine ⟨?_, fun x hx z => ?_⟩
  · have hd : Differentiable ℂ B.thMM := differentiableOn_univ.1 hθ.1.differentiableOn
    unfold Formalism.L2.Ker.Base.thZero tensPow
    fun_prop
  · have hx' := entry_mem B hx
    choose m hm using fun i j => q_int B h (hx' i j)
    have h1 : Real.sqrt D.host.d / 2 * (Hf D (tor0 D cc δ) x x).re = ((∑ i, ∑ j, m i j : ℤ) : ℝ) := by
      rw [Hf_eq B]
      push_cast
      simp only [Complex.re_sum, Finset.mul_sum, ← hm]
      rfl
    have h2 : al D (tor0 D cc δ) x = ∏ i, ∏ j, alphaQ B.cq (matH (hOne B.L D.what₂.Tau)) fun τ => x τ i j := by
      rw [al, h1, round_intCast, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      simp only [alphaQ, hm, ← Complex.exp_sum, ← Finset.mul_sum]
      congr 1
      push_cast
      ring
    rw [h2, U, Hf_eq B, Hf_eq B]
    simp only [Formalism.L2.Ker.Base.thZero, tensPow, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Complex.exp_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hθ.2 _ (hx' i j) fun τ => z τ i j

end WeilVac

open WeilVac

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendLineBundleFactorial
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ExtendLineBundleComponents

theorem exists_integral_components (X : Scheme.{0}) [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    ∃ (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) ∧ (∀ x, ∃ a, x ∈ V a) ∧
      ∀ a, IsIntegral (V a).toScheme ∧ CompactSpace (V a).toScheme := by
  have : IsNoetherian X := {}
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))
  have heq : ∀ (x : X) (Z W : Set X), Z ∈ irreducibleComponents X → W ∈ irreducibleComponents X →
      x ∈ Z → x ∈ W → Z = W := by
    intro x Z W hZ hW hxZ hxW
    have := hX x
    exact GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents_of_isDomain hZ hW hxZ hxW
  have hopen : ∀ Z ∈ irreducibleComponents X, IsOpen Z := fun Z hZ => by
    have e : Zᶜ = ⋃ W ∈ irreducibleComponents X \ {Z}, W := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
      constructor
      · intro hx
        refine ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents x, fun h ↦ hx ?_⟩,
          mem_irreducibleComponent⟩
        exact (show irreducibleComponent x = Z from h) ▸ mem_irreducibleComponent
      · rintro ⟨W, ⟨hW, hne⟩, hxW⟩ hxZ
        exact hne (heq x W Z hW hZ hxW hxZ)
    rw [← isClosed_compl_iff, e]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have : IsReduced X := isReduced_of_isReduced_stalk _
  let V : irreducibleComponents X → X.Opens := fun Z => ⟨Z.1, hopen Z.1 Z.2⟩
  refine ⟨irreducibleComponents X, V, fun a b x ha hb => Subtype.ext (heq x a b a.2 b.2 ha hb),
    fun x => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩,
    fun a => ?_⟩
  have : IrreducibleSpace (V a).toScheme := Subtype.irreducibleSpace a.2.1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  exact isCompact_iff_compactSpace.mp (isClosed_of_mem_irreducibleComponents a.1 a.2).isCompact

theorem uniqueFactorizationMonoid_stalk_toScheme (X : Scheme.{0}) (U : X.Opens)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (y : U.toScheme) :
    UniqueFactorizationMonoid (U.toScheme.presheaf.stalk y) :=
  MulEquiv.uniqueFactorizationMonoid
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv (hX _)

end GlobalTheory.ExtendLineBundleComponents


open GlobalTheory.ExtendLineBundleComponents GlobalTheory.GenSpread in
theorem GlobalTheory.exists_lineBundle_extension_of_isDomain : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X]
    [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, IsDomain (X.presheaf.stalk x)) →
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB →
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  intro X Y _ _ j hj hdom hufm L hL
  obtain ⟨A, V, hd, hc, hV⟩ := exists_integral_components X hdom
  have key : ∀ a, ∃ M : LB (V a).toScheme, M.IsLB ∧
      LBIso (M.pull (j ∣_ V a)) (L.pull (j ⁻¹ᵁ V a).ι) := by
    intro a
    have := (hV a).1
    have := (hV a).2
    obtain ⟨M, hM, φ, hφ⟩ := GlobalTheory.exists_lineBundle_extension (V a).toScheme (j ⁻¹ᵁ V a).toScheme
      (j ∣_ V a) inferInstance (uniqueFactorizationMonoid_stalk_toScheme X (V a) hufm)
      (L.pull (j ⁻¹ᵁ V a).ι) (pull_isLB hL _)
    exact ⟨M, hM, φ, hφ⟩
  choose M hM hML using key
  obtain ⟨N, hN, hNM⟩ := _root_.GlobalTheory.glue_lineBundles X A V hd hc M hM
  refine ⟨N, hN, _root_.GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover Y A (fun a => j ⁻¹ᵁ V a) (fun a b y ha hb => hd a b _ ha hb)
    (fun y => hc (j y)) _ _ (pull_isLB hN j) hL fun a => ?_⟩
  have e1 : LBIso ((N.pull j).pull (j ⁻¹ᵁ V a).ι) ((N.pull (V a).ι).pull (j ∣_ V a)) :=
    LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hN _ rfl).symm (lbIso_pull_pull hN _ (morphismRestrict_ι j (V a)).symm)
  have e2 : LBIso ((N.pull (V a).ι).pull (j ∣_ V a)) ((M a).pull (j ∣_ V a)) :=
    lbIso_pullback (hNM a) _
  exact LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hL _) e1
    (LBIso.trans (pull_isLB (pull_isLB hN _) _) (pull_isLB (hM a) _) (pull_isLB hL _) e2 (hML a))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtGaussianParametersAtIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss.ParDer

variable {l m n : Type} [Fintype m]

theorem der_mul {M : ℝ → Matrix l m ℂ} {N : ℝ → Matrix m n ℂ} {M' : Matrix l m ℂ} {N' : Matrix m n ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hN : ∀ i j, HasDerivAt (fun t => N t i j) (N' i j) s)
    (i : l) (j : n) : HasDerivAt (fun t => (M t * N t) i j) ((M' * N s + M s * N') i j) s := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hM i k).fun_mul (hN k j)

theorem der_dot {u v : ℝ → m → ℂ} {u' v' : m → ℂ} {s : ℝ}
    (hu : ∀ i, HasDerivAt (fun t => u t i) (u' i) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) :
    HasDerivAt (fun t => u t ⬝ᵥ v t) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hu k).fun_mul (hv k)

theorem der_mulVec {M : ℝ → Matrix l m ℂ} {v : ℝ → m → ℂ} {M' : Matrix l m ℂ} {v' : m → ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s)
    (i : l) : HasDerivAt (fun t => (M t *ᵥ v t) i) ((M' *ᵥ v s + M s *ᵥ v') i) s :=
  der_dot (u := fun t => M t i) (u' := M' i) (hM i) hv

theorem der_vecMul {M : ℝ → Matrix m n ℂ} {v : ℝ → m → ℂ} {M' : Matrix m n ℂ} {v' : m → ℂ} {s : ℝ}
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (j : n) : HasDerivAt (fun t => (v t ᵥ* M t) j) ((v' ᵥ* M s + v s ᵥ* M') j) s :=
  der_dot (v := fun t i => M t i j) (v' := fun i => M' i j) hv fun i => hM i j

theorem par_deriv : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  intro P Q A x Z g g' h0 h0' hg hg'
  have hY : ∀ i j, HasDerivAt (fun t => (g t * baseY A) i j) ((Z * baseY A) i j) 0 := fun i j => by
    simpa using der_mul (N := fun _ => baseY A) (N' := 0) hg (fun _ _ => hasDerivAt_const _ _) i j
  have hZ : Z * baseY A = Matrix.fromRows (Z.toBlocks₁₁ * A + Z.toBlocks₁₂) (Z.toBlocks₂₁ * A + Z.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Z, baseY, Matrix.fromBlocks_mul_fromRows]
    simp
  have hY1 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₁ i j) ((Z.toBlocks₁₁ * A + Z.toBlocks₁₂) i j) 0 :=
    fun i j => by have := hY (.inl i) j; rw [hZ] at this; exact this
  have hY2 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₂ i j) ((Z.toBlocks₂₁ * A + Z.toBlocks₂₂) i j) 0 :=
    fun i j => by have := hY (.inr i) j; rw [hZ] at this; exact this
  have e2 : (g 0 * baseY A).toRows₂ = 1 := by rw [h0, Matrix.one_mul]; rfl
  have e1 : (g 0 * baseY A).toRows₁ = A := by rw [h0, Matrix.one_mul]; rfl
  obtain ⟨hdet, hinv⟩ := GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity Q (fun t => (g t * baseY A).toRows₂) _ e2 hY2
  have hA : ∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0 := fun i j => by
    have := der_mul (N' := -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂)) hY1 hinv i j
    rw [e1, e2, inv_one, Matrix.mul_one, Matrix.mul_neg, ← sub_eq_add_neg] at this
    exact this
  have eA : matA (g 0 * baseY A) = A := by rw [h0, Matrix.one_mul, matA_baseY]
  have hv : ∀ i, HasDerivAt (fun t => (g t *ᵥ baseV x) i) ((Z *ᵥ baseV x) i) 0 := fun i => by
    simpa using der_mulVec (v := fun _ => baseV x) (v' := 0) hg (fun _ => hasDerivAt_const _ _) i
  have hf : ∀ i, HasDerivAt (fun t => (baseF x ᵥ* g' t) i) ((baseF x ᵥ* (-Z)) i) 0 := fun i => by
    simpa using der_vecMul (v := fun _ => baseF x) (v' := 0) (M' := -Z) (fun _ => hasDerivAt_const _ _) hg' i
  have hv1 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inl) i) ((Z.toBlocks₁₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inl i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₁₁])
  have hv2 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inr) i) ((Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inr i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf1 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inl) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₁)) i) 0 :=
    fun i => (hf (.inl i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf2 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inr) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₂)) i) 0 :=
    fun i => (hf (.inr i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₂])
  have ev : (g 0 *ᵥ baseV x) ∘ Sum.inr = 0 := by rw [h0, Matrix.one_mulVec]; rfl
  have ef : (baseF x ᵥ* g' 0) ∘ Sum.inl = 0 := by rw [h0', Matrix.vecMul_one]; rfl
  have hX : ∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0 := by
    rintro (i | j)
    · refine ((hv1 i).fun_sub (der_mulVec hA hv2 i)).congr_deriv ?_
      rw [ev, eA]
      simp [dX, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    · refine ((der_vecMul hf1 hA j).fun_add (hf2 j)).congr_deriv ?_
      rw [ef, eA]
      simp [dX, Matrix.vecMul_add, Matrix.neg_vecMul, Matrix.vecMul_vecMul, add_comm]
  refine ⟨hA, hX, ?_⟩
  have hd := der_dot (u := fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) ∘ Sum.inr)
    (u' := dX Z A x ∘ Sum.inr) (fun j => hX (.inr j)) hv2
  refine (hdet.fun_mul hd.fun_neg.cexp).congr_deriv ?_
  simp only [ev, e2]
  rw [h0, h0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base]
  simp [dS, sub_eq_add_neg]

end GlobalTheory.OscGauss.ParDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOfWeakDerivOnInvariantTotalSetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (D : Set H) (x w : H), U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ t y, ‖U t y‖ = ‖y‖) → (∀ y, Continuous fun t => U t y) → Dense (Submodule.span ℂ D : Set H) → (∀ t, ∀ y ∈ D, U t y ∈ D) → (∀ y ∈ D, HasDerivAt (fun t : ℝ => inner ℂ (U t x) y) (inner ℂ w y) 0) → HasDerivAt (fun t : ℝ => U t x) w 0 := by
  first | exact @GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | exact GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total | (intros; apply GlobalTheory.Mem.Osc.hasDerivAt_of_weak_on_invariant_total <;> assumption)
end

