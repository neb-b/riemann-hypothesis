module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveTensorOmegaStd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBase
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPerLev
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_perLev : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g k : ℕ), P.g = g → ∃ (τ : Matrix (Fin g) (Fin g) ℂ) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  rintro hU P g k rfl
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hb, hW⟩ := hU P rig hrig
  let Q : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hrange : Set.range Q = (u.Λ : Set (Fin P.g → ℂ)) := Subtype.range_coe
  have hQ : Function.Injective Q ∧ DiscreteTopology Q.range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧
      Hm.IsHermitian ∧ (∀ z : Fin P.g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (Q x) (Q y)).im = Ef x y := by
    refine ⟨Subtype.val_injective, ?_, hrange ▸ u.full, hAH.1, hAH.2.1, fun x y => (hE x y).symm⟩
    have h := u.discrete
    change DiscreteTopology (Set.range Q)
    rw [hrange]
    exact h
  obtain ⟨h1, h2, h3, h4⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 _ Ef _ Q Hm hQ
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 _ Ef _ hb h4 h3
  obtain ⟨h, τ, hh, -, -, hs, hp, -, hper⟩ := SiegelPeriod.exists_siegel_form _ Ef _ bas Q Hm hbas hQ
  let ψ : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofBijective h.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hh, Matrix.mulVec_surjective_iff_isUnit.2 hh⟩
  have hψ : ∀ a, ψ.symm (per τ a) = (bas a : Fin P.g → ℂ) := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hper a).symm
  obtain ⟨u', hex, hΛ, -⟩ := exists_holUnif_reparam P.A P.L P.g u ψ.symm (fun _ => 1)
    (differentiable_const _) (fun _ => one_ne_zero) rfl
  refine ⟨τ, fun a => u'.ex ((k : ℂ)⁻¹ • per τ a), rfl, hs, hp, u', fun z => ?_, fun n a b c hn hc => ?_,
    fun _ => rfl⟩
  · rw [hΛ]
    constructor
    · intro hz
      refine ⟨bas.symm ⟨_, hz⟩, ψ.symm.injective ?_⟩
      rw [hψ, LinearEquiv.apply_symm_apply]
    · rintro ⟨a, rfl⟩
      rw [hψ]
      exact (bas a).2
  · rw [hex, hex, map_smul, map_smul, hψ, hψ]
    exact hW n (bas a) (bas b) c hn (by rw [hbas]; exact hc)

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPeriodLevelOfSiegelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelObject

open GlobalTheory.TensorSiegel

theorem exists_lattice_form {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ),
      DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧
      (∀ z, z ∈ Λ ↔ ∃ a, z = per τ a) ∧
      ∀ a b, (hermForm Hm (per τ a) (per τ b)).im = omegaStd a b := by
  let σ : Fin 1 × Fin g ≃ Fin g := Equiv.uniqueProd _ _
  let G : Matrix (Fin 1) (Fin 1) ℤ := 1
  have hG : (G.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [show G.map (Int.cast : ℤ → ℝ) = 1 from Matrix.map_one _ Int.cast_zero Int.cast_one]
    exact Matrix.PosDef.one
  have hper : ∀ x : Fin 1 → (Fin g ⊕ Fin g → ℤ), period σ τ x = per τ (x 0) := fun x => by
    funext i
    exact period_apply σ τ x 0 i
  have hsum : ∀ x y : Fin 1 → (Fin g ⊕ Fin g → ℤ),
      ∑ u, ∑ v, G u v * omegaStd (x u) (y v) = omegaStd (x 0) (y 0) := fun x y => by simp [G]
  let EF : LinearMap.BilinForm ℤ (Fin 1 → (Fin g ⊕ Fin g → ℤ)) :=
    LinearMap.mk₂ ℤ (fun x y => omegaStd (x 0) (y 0))
      (fun x x' y => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun x y y' => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
  have hEF : Function.Bijective EF :=
    bijective_tensor_omegaStd G (by simp [G]) EF fun x y => (hsum x y).symm
  obtain ⟨h1, h2, h3⟩ := period_isLattice σ hp
  have him := im_formMatrix_period σ G hs hp
  let Q := (period σ τ).toIntLinearMap
  let e := LinearEquiv.ofInjective Q h1
  refine ⟨LinearMap.range Q, formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ,
    e.symm.dualMap.toLinearMap ∘ₗ EF ∘ₗ e.symm.toLinearMap, h2, h3, formMatrix_isHermitian σ hG hp,
    fun z hz => formMatrix_pos σ hG hp hz, fun a b => ?_,
    e.symm.dualMap.bijective.comp (hEF.comp e.symm.bijective), fun z => ?_, fun a b => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    refine Eq.trans ?_ (him x y).symm
    rw [hsum]
    simp [EF]
  · exact ⟨fun ⟨x, hx⟩ => ⟨x 0, hx.symm.trans (hper x)⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, (hper _).trans ha.symm⟩⟩
  · have := him (fun _ => a) (fun _ => b)
    rwa [hsum, hper, hper] at this

theorem exists_perLev_of_siegel : ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → ∃ (P : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  intro hU _ g k τ hs hp
  obtain ⟨Λ, Hm, Ef, h1, h2, h3, h4, h5, h6, hΛ, hω⟩ := exists_lattice_form τ hs hp
  obtain ⟨P, u, χ, hg, rfl, hAH, -⟩ := GlobalTheory.principalTorus_algebraic g Λ Hm Ef h1 h2 h3 h4 h5 h6
  obtain ⟨E', hE', -, -, -, -, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU P g u Hm χ hAH
  refine ⟨P, fun a => u.ex ((k : ℂ)⁻¹ • per τ a), hg, hs, hp, u, hΛ, fun n a b c hn hc => ?_, fun _ => rfl⟩
  refine hW n ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
  have h : E' ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩ = omegaStd a b := by
    have h' := hE' ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [Subtype.coe_mk, Subtype.coe_mk, hω] at h'
    exact Int.cast_injective h'
  rw [h, hc]

end GlobalTheory.SiegelObject
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSectionNonzeroNearTwo
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoPrimeSection

open TopologicalSpace

section General

variable {X : Scheme.{0}} {L : LB X}

theorem exists_global [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (a : Γ(X, ⊤)) {V : X.Opens}
    (hV : X.basicOpen a ≤ V) {θ : ∀ i, Γ(X, V ⊓ L.U i)} (hθ : θ ∈ secOn L V) {g : X} (hg : g ∈ X.basicOpen a)
    {i : L.ι} (hi : g ∈ X.basicOpen (θ i)) : ∃ u : L.Sec, g ∈ Out.nonzeroLocus u := by
  have mem_nonzeroLocus (s : L.Sec) (x : X) :
      x ∈ Out.nonzeroLocus s ↔ ∃ k, x ∈ L.U k ∧ IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (s.f k)) := by
    refine Opens.mem_iSup.trans (exists_congr fun k => ⟨fun h => ?_, fun ⟨h, hu⟩ => ?_⟩)
    · have hk : x ∈ L.U k := X.basicOpen_le _ h
      refine ⟨hk, ?_⟩
      rw [gs_eq (𝟙 X) x _ hk]
      exact (X.mem_basicOpen _ _ hk).1 h
    · rw [gs_eq (𝟙 X) x _ h] at hu
      exact (X.mem_basicOpen _ _ h).2 hu
  let topSec (s : Γ(GlobalTheory.LB.toMod L, ⊤)) : L.Sec :=
    ⟨fun i => resG X (le_inf le_top le_rfl) (GlobalTheory.LB.coord s i),
      fun i j => by
        change resG X _ (resG X _ _) = _ * resG X _ (resG X _ _)
        rw [GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_resG, GlobalTheory.LB.coord_rel s i j _ _ le_rfl, GlobalTheory.LB.resG_self]⟩
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  obtain ⟨n, t, ht⟩ := QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod L)
    isCompact_univ isQuasiSeparated_univ a le_top rfl
    (((GlobalTheory.LB.toMod L).presheaf.map (homOfLE hV).op ((GlobalTheory.LB.secOnEquiv _ _).symm ⟨θ, hθ⟩)))
  have hi' : g ∈ V ⊓ L.U i := X.basicOpen_le _ hi
  have hm : (𝟙 X : X ⟶ X) g ∈ X.basicOpen a ⊓ L.U i := ⟨hg, hi'.2⟩
  refine ⟨topSec t, (mem_nonzeroLocus _ _).2 ⟨i, hi'.2, ?_⟩⟩
  have q := congrArg (fun s => gs (𝟙 X) g _ (GlobalTheory.LB.coord s i)) ht
  have e : gs (𝟙 X) g (L.U i) ((topSec t).f i) =
      gs (𝟙 X) g ⊤ a ^ n * gs (𝟙 X) g (V ⊓ L.U i) (θ i) := by
    refine (gs_res (𝟙 X) g _ hi'.2 _).trans ((gs_res (𝟙 X) g _ hm _).symm.trans (q.symm.trans
      ((gs_mul (𝟙 X) g _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res (𝟙 X) g _ hm _)))))
    exact (gs_res (𝟙 X) g _ hm _).trans ((LBGerm.gs_pow (𝟙 X) g _ hg _ _).trans
      (congrArg (· ^ n) (gs_res (𝟙 X) g _ hg _)))
  rw [e]
  exact (((LBGerm.isUnit_gs_iff (𝟙 X) g ⊤ trivial a).2 hg).pow n).mul
    ((LBGerm.isUnit_gs_iff (𝟙 X) g _ hi' _).2 hi)

def add (s t : L.Sec) : L.Sec :=
  ⟨fun i => s.f i + t.f i, fun i j => by rw [map_add (f := _), map_add (f := _), s.compat i j, t.compat i j, mul_add]⟩

theorem add_comm' (s t : L.Sec) : add s t = add t s := by
  unfold add
  simp only [add_comm (s.f _)]

theorem mem_nonzeroLocus_add {s t : L.Sec} {y : X} (hs : y ∈ Out.nonzeroLocus s) (ht : y ∉ Out.nonzeroLocus t) :
    y ∈ Out.nonzeroLocus (add s t) := by
  have mem_nonzeroLocus (s : L.Sec) (x : X) :
      x ∈ Out.nonzeroLocus s ↔ ∃ k, x ∈ L.U k ∧ IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (s.f k)) := by
    refine Opens.mem_iSup.trans (exists_congr fun k => ⟨fun h => ?_, fun ⟨h, hu⟩ => ?_⟩)
    · have hk : x ∈ L.U k := X.basicOpen_le _ h
      refine ⟨hk, ?_⟩
      rw [gs_eq (𝟙 X) x _ hk]
      exact (X.mem_basicOpen _ _ hk).1 h
    · rw [gs_eq (𝟙 X) x _ h] at hu
      exact (X.mem_basicOpen _ _ h).2 hu
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hs
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  have hn : ¬ IsUnit (gs (𝟙 X) y (L.U k) (t.f k)) := fun h => ht ((mem_nonzeroLocus _ _).2 ⟨k, hk, h⟩)
  have e : gs (𝟙 X) y (L.U k) ((add s t).f k) = gs (𝟙 X) y (L.U k) (s.f k) + gs (𝟙 X) y (L.U k) (t.f k) :=
    gs_add (𝟙 X) y _ hk _ _
  rw [e]
  by_contra h
  have h₁ := (IsLocalRing.mem_maximalIdeal _).2 h
  have h₂ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h₃ := Ideal.sub_mem _ h₁ h₂
  rw [add_sub_cancel_right] at h₃
  exact (IsLocalRing.mem_maximalIdeal _).1 h₃ u

end General

theorem exists_basicOpen_two {R : Type} [CommRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {p q : PrimeSpectrum R} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : PrimeSpectrum R, r ∉ z.asIdeal → z ∈ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have key : ∀ z : PrimeSpectrum R, z ∈ U ↔ ¬ I ≤ z.asIdeal := fun z => by
    rw [← Set.notMem_compl_iff, hI]
    rfl
  have : ¬ (I : Set R) ⊆ p.asIdeal ∪ q.asIdeal := fun h =>
    (Ideal.subset_union.1 h).elim ((key p).1 hp) ((key q).1 hq)
  obtain ⟨r, hr, hn⟩ := Set.not_subset.1 this
  exact ⟨r, fun h => hn (Or.inl h), fun h => hn (Or.inr h), fun z hz => (key z).2 fun h => hz (h hr)⟩

theorem exists_sec_fibre (hL : Out.Laws) (hL₂ : Out.Laws2) {R : Type} [CommRing R] (Q : Out.PolAV (Sp R)) (p : Sp R) :
    ∃ th : Q.L.Sec, ∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨V, hV, θ, hθ, -, nz⟩ := PushInv.pushInvertible_any hL₂.secBaseChangeAny hL.globalSectionsRank _ Q p
  obtain ⟨g, i, hg, hi⟩ := nz p hV
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
  have := Q.isAb.proper
  have : CompactSpace Q.A.left := QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have : QuasiSeparatedSpace Q.A.left := quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have e := Scheme.preimage_basicOpen_top Q.A.hom f
  obtain ⟨u, hu⟩ := exists_global Q.isLB (Q.A.hom.appTop f) (e.ge.trans (Q.A.hom.preimage_mono hf)) hθ
    (g := g) (e.le (show Q.A.hom g ∈ (Sp R).basicOpen f from hg ▸ hpf)) hi
  exact ⟨u, g, hg, hu⟩

open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem main : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), ∃ (th : Q.L.Sec) (r : R), r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : Sp R, r ∉ z.asIdeal → ∃ x : Q.A.left, Q.A.hom x = z ∧ x ∈ Out.nonzeroLocus th := by
  intro hL hL₂ R _ _ Q p q
  obtain ⟨th, hp, hq⟩ : ∃ th : Q.L.Sec, (∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th) ∧
      ∃ x : Q.A.left, Q.A.hom x = q ∧ x ∈ Out.nonzeroLocus th := by
    obtain ⟨s, x, hx, hs⟩ := exists_sec_fibre hL hL₂ Q p
    obtain ⟨t, y, hy, ht⟩ := exists_sec_fibre hL hL₂ Q q
    by_cases h₁ : y ∈ Out.nonzeroLocus s
    · exact ⟨s, ⟨x, hx, hs⟩, y, hy, h₁⟩
    by_cases h₂ : x ∈ Out.nonzeroLocus t
    · exact ⟨t, ⟨x, hx, h₂⟩, y, hy, ht⟩
    exact ⟨add s t, ⟨x, hx, mem_nonzeroLocus_add hs h₂⟩, y, hy, add_comm' t s ▸ mem_nonzeroLocus_add ht h₁⟩
  have := Q.isAb.smooth
  obtain ⟨x, hx, hx'⟩ := hp
  obtain ⟨y, hy, hy'⟩ := hq
  obtain ⟨r, h₁, h₂, h₃⟩ := exists_basicOpen_two (R := R) (p := p) (q := q)
    (Q.A.hom.isOpenMap _ (Out.nonzeroLocus th).isOpen) ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
  refine ⟨th, r, h₁, h₂, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := h₃ z hz
  exact ⟨w, e, hw⟩

end GlobalTheory.TwoPrimeSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSeparatingPairs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.EtaleLocInj

theorem exists_separating_pairs {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (h : φ.Etale) :
    ∃ s : Finset (S × S), ∑ p ∈ s, p.1 * p.2 = 1 ∧ ∀ e e' : S →+* ℂ, e.comp φ = e'.comp φ →
      ∑ p ∈ s, e p.1 * e' p.2 ≠ 0 → e = e' := by
  algebraize [φ]
  obtain ⟨t, ht, h1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := S)).1 inferInstance
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  refine ⟨s, ?_, fun e e' hee hne => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simpa [map_sum] using h1
  · letI : Algebra R ℂ := (e.comp φ).toAlgebra
    let a : S →ₐ[R] ℂ := { e with commutes' := fun _ => rfl }
    let a' : S →ₐ[R] ℂ := { e' with commutes' := fun r => (RingHom.congr_fun hee r).symm }
    let F := Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
    ext x
    have h2 := congrArg F (ht x)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_mul, map_sub, map_sum, Algebra.TensorProduct.lift_tmul, map_one, map_zero] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · have h4 := (sub_eq_zero.1 h3).symm
      rw [_root_.one_mul, _root_.mul_one] at h4
      exact h4
    · exact (hne h3).elim

theorem eq_of_valAtHom_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x x' : Sp ℂ ⟶ X)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valAtHom x U h = valAtHom x' U h') : x = x' := by
  rw [← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h,
    ← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h']
  congr 2
  ext1
  exact e

theorem exists_open_injOn :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ), Etale π → IsOpen B → b₀ ∈ B → IsHolTo B y → ∃ B' : Set (Fin m → ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ ∀ b ∈ B', ∀ b' ∈ B', y b ≫ π = y b' ≫ π → y b = y b' := by
  intro X Y π m B y b₀ hπ _ hb₀ hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π (y b₀ (default : PrimeSpectrum ℂ)))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show y b₀ (default : PrimeSpectrum ℂ) ∈ ((π ⁻¹ᵁ V : X.Opens) : Set X) from hxV) (π ⁻¹ᵁ V).isOpen
  have e : U ≤ π ⁻¹ᵁ V := hUV
  obtain ⟨s, hs1, hs⟩ := exists_separating_pairs _ (π.etale_appLE hV hU e)
  set C : Set (Fin m → ℂ) := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} with hC
  have hCo : IsOpen C := (hy U 0).1
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hb₀C : b₀ ∈ C := ⟨hb₀, h₀⟩
  have hc : ∀ f : Γ(X, U), ContinuousAt (fun b => valAt' (y b) U f) b₀ := fun f =>
    (hy U f).2.continuousOn.continuousAt (hCo.mem_nhds hb₀C)
  let F : (Fin m → ℂ) × (Fin m → ℂ) → ℂ := fun q => ∑ p ∈ s, valAt' (y q.1) U p.1 * valAt' (y q.2) U p.2
  have hF : ContinuousAt F (b₀, b₀) := by
    refine tendsto_finsetSum _ fun p _ => ?_
    exact ((hc p.1).comp_of_eq continuousAt_fst rfl).mul ((hc p.2).comp_of_eq continuousAt_snd rfl)
  have hF0 : F (b₀, b₀) ≠ 0 := by
    simp only [F, ← valAt'_mul, ← valAt'_sum, hs1, valAt'_one _ h₀]
    exact one_ne_zero
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hF.eventually_ne hF0)
  obtain ⟨B', hB'sub, hB'o, hB'⟩ := mem_nhds_iff.1
    (Filter.inter_mem (hCo.mem_nhds hb₀C) (Filter.inter_mem hu hv))
  refine ⟨B', hB'o, hB', fun b hb => (hB'sub hb).1.1, fun b hb b' hb' hbb => ?_⟩
  have h1 := (hB'sub hb).1.2
  have h2 := (hB'sub hb').1.2
  refine eq_of_valAtHom_eq hU _ _ h1 h2 (hs _ _ ?_ ?_)
  · ext f
    rw [RingHom.comp_apply, RingHom.comp_apply, ← valAt'_eq_valAtHom, ← valAt'_eq_valAtHom,
      valAt'_appLE _ _ _ _ _ _ h1, valAt'_appLE _ _ _ _ _ _ h2, hbb]
  · simp only [← valAt'_eq_valAtHom]
    have h3 : F (b, b') ≠ 0 := huv (Set.mk_mem_prod (hB'sub hb).2.1 (hB'sub hb').2.2)
    exact h3

end GlobalTheory.EtaleLocInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamUnit

theorem famUnit : ∀ κ : Rule, Funct κ → UnitSp κ → FamUnit κ := by
  intro κ hF hU S _ _ _ _ _ y
  obtain ⟨u, hu⟩ := GlobalTheory.KeySmoothBase.exists_unit_normal (κ := κ) hF hU S y
  exact ⟨u, GlobalTheory.KeySpec.isValue_of_generic κ hF hU S y u fun K _ _ f x hf hx =>
    hu K f x ((RingHom.injective_iff_ker_eq_bot f).1 hf) hx⟩

end GlobalTheory.KeyFamUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralBaseChangeAndLocalization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem GeomInt.baseChange {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    (K' : Type) [Field K'] [Algebra K K'] : GeomInt K' (K' ⊗[K] R) := by
  haveI := h.1
  refine ⟨inferInstance, fun L _ _ => ?_⟩
  letI : Algebra K L := ((algebraMap K' L).comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := h.2 L
  exact (Algebra.TensorProduct.cancelBaseChange K K' L L R).toMulEquiv.isDomain _

theorem GeomInt.away {K R : Type} [Field K] [CommRing R] [Algebra K R] (h : GeomInt K R)
    {r : R} (hr : r ≠ 0) : GeomInt K (Localization.Away r) := by
  haveI := h.1
  haveI : Algebra.Smooth R (Localization.Away r) := Algebra.Smooth.of_isLocalization_Away r
  refine ⟨Algebra.Smooth.comp K R _, fun L _ _ => ?_⟩
  haveI := h.2 L
  letI : Algebra (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    (Algebra.TensorProduct.map (AlgHom.id L L)
      (IsScalarTower.toAlgHom K R (Localization.Away r))).toAlgebra
  haveI : IsScalarTower L (L ⊗[K] R) (L ⊗[K] Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right K L (Submonoid.powers r)
    (Localization.Away r) (by ext; simp [RingHom.algebraMap_toAlgebra])
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (hM := ?_) (S := L ⊗[K] Localization.Away r)
    (M := (Submonoid.powers r).map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
  rw [Submonoid.map_powers]
  apply powers_le_nonZeroDivisors_of_noZeroDivisors
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  exact fun h0 => hr (hinj (by rw [h0, map_zero]))

theorem geomInt_baseChange_and_away :
    ∀ (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R],
      GeomInt K R → GeomInt K' (K' ⊗[K] R) ∧ ∀ r : R, r ≠ 0 → GeomInt K (Localization.Away r) :=
  fun _ K' _ _ _ _ _ _ h => ⟨h.baseChange K', fun _ hr => h.away hr⟩

end GlobalTheory.KeyFam
end

