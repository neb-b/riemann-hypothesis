module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanDeriv
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem tanDeriv_of : TanDeriv := by
  intro V _ _ Y s' B s v₀ hB hv₀ hs hss y hy W hyW
  have hv₀S : v₀ ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} := ⟨hv₀, by rw [← hy]; exact hyW⟩
  have hnhds : {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W} ∈ 𝓝 v₀ := (hs W 0).1.mem_nhds hv₀S
  have hval : ∀ v (hv : v ∈ {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}) (b : Sec s' W),
      valAt' (s v) W b = CxPts.ev s' (RingHom.id ℂ) W b ⟨s v, hss v hv.1⟩ := by
    intro v hv b
    simp only [valAt', CxPts.ev, valR, dif_pos hv.2]
    rfl
  let g : Sec s' W → V → ℂ := fun b v => valAt' (s v) W b
  have hd : ∀ b, DifferentiableAt ℂ (g b) v₀ := fun b =>
    ((hs W b).2 v₀ hv₀S).differentiableAt ((hs W b).1.mem_nhds hv₀S)
  have hadd : ∀ b c, g (b + c) =ᶠ[𝓝 v₀] g b + g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b + c) = valAt' (s v) W b + valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_add _ _ _)
  have hmul : ∀ b c, g (b * c) =ᶠ[𝓝 v₀] g b * g c := fun b c =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (b * c) = valAt' (s v) W b * valAt' (s v) W c
      rw [hval v hv, hval v hv, hval v hv]
      exact CxPts.ev_mul _ _ _)
  have hconst : ∀ a : ℂ, ∀ᶠ v in 𝓝 v₀, g (algebraMap ℂ (Sec s' W) a) v = a := fun a =>
    Filter.eventually_of_mem hnhds (fun v hv => by
      change valAt' (s v) W (algebraMap ℂ (Sec s' W) a) = a
      rw [hval v hv]
      exact CxPts.ev_algX (show (⟨s v, hss v hv.1⟩ : CxPts s' (RingHom.id ℂ)) ∈ CxPts.ptsIn s' (RingHom.id ℂ) W from hv.2) a)
  have hyeq : (⟨s v₀, hss v₀ hv₀S.1⟩ : CxPts s' (RingHom.id ℂ)) = y := Subtype.ext hy.symm
  have hv0 : ∀ b, g b v₀ = CxPts.evHom hyW b := fun b => by
    change valAt' (s v₀) W b = _
    rw [hval v₀ hv₀S b, hyeq]
    exact CxPts.ev_eq hyW b
  have hφa : ∀ a : ℂ, CxPts.evHom hyW (algebraMap ℂ (Sec s' W) a) = a := fun a =>
    (CxPts.ev_eq hyW _).symm.trans (CxPts.ev_algX hyW a)
  letI : Module (Sec s' W) (V →L[ℂ] ℂ) := Module.compHom _ (CxPts.evHom hyW)
  haveI : IsScalarTower ℂ (Sec s' W) (V →L[ℂ] ℂ) := ⟨fun a b m => by
    change (CxPts.evHom hyW (a • b)) • m = a • ((CxPts.evHom hyW b) • m)
    have h1 : CxPts.evHom hyW (a • b) = a * CxPts.evHom hyW b :=
      (congrArg (CxPts.evHom hyW) (Algebra.smul_def a b)).trans
        ((map_mul (CxPts.evHom hyW) _ _).trans (congrArg (· * CxPts.evHom hyW b) (hφa a)))
    exact (congrArg (· • m) h1).trans (mul_smul _ _ _)⟩
  let L : Sec s' W →ₗ[ℂ] (V →L[ℂ] ℂ) :=
    { toFun := fun b => fderiv ℂ (g b) v₀
      map_add' := fun b c => by
        change fderiv ℂ (g (b + c)) v₀ = fderiv ℂ (g b) v₀ + fderiv ℂ (g c) v₀
        rw [(hadd b c).fderiv_eq, fderiv_add (hd b) (hd c)]
      map_smul' := fun a b => by
        change fderiv ℂ (g (a • b)) v₀ = a • fderiv ℂ (g b) v₀
        have h' : g (a • b) =ᶠ[𝓝 v₀] fun v => a * g b v := by
          rw [Algebra.smul_def]
          filter_upwards [hmul (algebraMap ℂ _ a) b, hconst a] with v h1 h2
          rw [h1, Pi.mul_apply, h2]
        rw [h'.fderiv_eq, fderiv_const_mul (hd b)] }
  let D : Derivation ℂ (Sec s' W) (V →L[ℂ] ℂ) := Derivation.mk' L (fun b c => by
    change fderiv ℂ (g (b * c)) v₀ =
      (CxPts.evHom hyW b) • fderiv ℂ (g c) v₀ + (CxPts.evHom hyW c) • fderiv ℂ (g b) v₀
    rw [(hmul b c).fderiv_eq, fderiv_mul (hd b) (hd c), hv0 b, hv0 c])
  refine ⟨D.liftKaehlerDifferential.restrictScalars ℂ, fun b ω => ?_, fun b => ?_⟩
  · change D.liftKaehlerDifferential (b • ω) = _
    rw [LinearMap.map_smul]
    exact congrArg (· • D.liftKaehlerDifferential ω) (CxPts.ev_eq hyW b).symm
  · change D.liftKaehlerDifferential (KaehlerDifferential.D ℂ _ b) = _
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem exists_basis {B : Type} [CommRing B] [Algebra ℂ B] (d : ℕ) (a : Fin d → B)
    (he : (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B).toRingHom.Etale) :
    ∃ b : Module.Basis (Fin d) B Ω[B⁄ℂ], ∀ l, b l = KaehlerDifferential.D ℂ B (a l) := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := (MvPolynomial.aeval a).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap ℂ B r = MvPolynomial.aeval a (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C])
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := he
  let b0 := Algebra.TensorProduct.basis B (KaehlerDifferential.mvPolynomialBasis ℂ (Fin d))
  refine ⟨b0.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ (MvPolynomial (Fin d) ℂ) B),
    fun l => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    ← KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearEquiv.apply_symm_apply,
    show algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X l) = a l from MvPolynomial.aeval_X a l]

private theorem exists_phi {B : Type} [CommRing B] [Algebra ℂ B] (e : B →ₐ[ℂ] ℂ) (d : ℕ)
    (bs : Module.Basis (Fin d) B Ω[B⁄ℂ]) :
    ∃ φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (r : B) (ω : Ω[B⁄ℂ]), φ (r • ω) = e r • φ ω) ∧ (∀ l, φ (bs l) = Pi.single l 1) ∧
      ∀ ω : Ω[B⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → B) (ω' : Fin m → Ω[B⁄ℂ]),
        (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i := by
  let φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun ω l => e (bs.repr ω l)
      map_add' := by
        intro x y
        funext l
        simp
      map_smul' := by
        intro c x
        funext l
        rw [← algebraMap_smul B c x, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
          AlgHom.commutes]
        simp }
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro r ω
    funext l
    simp [φ]
  · intro l
    funext l'
    by_cases h : l' = l
    · subst h
      simp [φ]
    · simp [φ, Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
  · intro ω hω
    refine ⟨d, fun l => bs.repr ω l, bs, ?_, (bs.sum_repr ω).symm⟩
    intro i
    simpa [φ] using congrFun hω i

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanExists_of :
    UpperTheory.Gal.W2.TanExists := by
  intro Z Y sZ s' d hsmooth c₁ c₂ h₁ h₂ hc₁ y hy
  haveI := hsmooth
  obtain ⟨U, x, hUaff, hzU, het⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := sZ) (D := d)
    ((↑y ≫ c₁ : Sp ℂ ⟶ Z) (IsLocalRing.closedPoint ℂ))
  have hyU : ⊤ ≤ (↑y : Sp ℂ ⟶ Y) ⁻¹ᵁ (c₁ ⁻¹ᵁ U ⊓ c₂ ⁻¹ᵁ U) := by
    rw [GlobalTheory.Points.le_preimage_iff]
    have h2 := hzU
    rw [hy] at h2
    exact ⟨hzU, h2⟩
  obtain ⟨V, hVaff, hyV, hVle⟩ := GlobalTheory.Points.exists_isAffineOpen_le (↑y : Sp ℂ ⟶ Y) hyU
  have hV1 : V ≤ c₁ ⁻¹ᵁ U := hVle.trans inf_le_left
  have hV2 : V ≤ c₂ ⁻¹ᵁ U := hVle.trans inf_le_right
  have hg := HasRingHomProperty.appLE @Etale c₁ hc₁ ⟨U, hUaff⟩ ⟨V, hVaff⟩ hV1
  have hres : ∀ t, (c₁.appLE U V hV1).hom t = Sec.res s' hV1 (appSec sZ s' c₁ U t) := by
    intro t
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  have heq : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom =
      (c₁.appLE U V hV1).hom.comp (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := semiHom_appSec h₁ U r 1
      simp only [Algebra.smul_def, _root_.mul_one, map_one, RingHom.id_apply] at h1
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.C r) =
          DVR.FlatBC.algX sZ U r := MvPolynomial.eval₂Hom_C _ _ _
      refine Eq.trans ?_ ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres _)).symm
      change algebraMap ℂ (Sec s' V) r = Sec.res s' hV1 (appSec sZ s' c₁ U (algebraMap ℂ (Sec sZ U) r))
      rw [h1, AlgHom.commutes]
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.X i) = x i :=
        MvPolynomial.eval₂Hom_X' _ _ _
      exact ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres (x i))).symm
  have het' : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom.Etale := by
    rw [heq]
    exact RingHom.Etale.stableUnderComposition _ _ het hg
  obtain ⟨bs, hbs⟩ := UpperTheory.Gal.W2.exists_basis d _ het'
  have hyV' : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := hyV
  let e : Sec s' V →ₐ[ℂ] ℂ :=
    { toRingHom := CxPts.evHom hyV'
      commutes' := fun r => (CxPts.ev_eq hyV' _).symm.trans (CxPts.ev_algX hyV' r) }
  obtain ⟨φ, hsm, hbasis, hker⟩ := UpperTheory.Gal.W2.exists_phi e d bs
  refine ⟨fun j l => φ (KaehlerDifferential.D ℂ (Sec s' V) (Sec.res s' hV2 (appSec sZ s' c₂ U (x j)))) l,
    U, V, hV1, hV2, x, hyV', hUaff, hVaff, φ, ?_, ?_, ?_, ?_⟩
  · intro b ω
    rw [hsm]
    congr 1
    exact (CxPts.ev_eq hyV' b).symm
  · intro l
    have h3 := hbasis l
    rw [hbs l] at h3
    exact h3
  · intro j
    rfl
  · intro ω hω
    obtain ⟨m, b, ω', hb, hsum⟩ := hker ω hω
    exact ⟨m, b, ω', fun i => (CxPts.ev_eq hyV' (b i)).trans (hb i), hsum⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTorusCount
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem det_lattice_restrict_eq_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Lz : Submodule ℤ E) [DiscreteTopology Lz] [IsZLattice ℝ Lz]
    (f : E →ₗ[ℝ] E) (fL : Lz →ₗ[ℤ] Lz) (hfL : ∀ x, (fL x : E) = f x) :
    ((LinearMap.det fL : ℤ) : ℝ) = LinearMap.det f := by
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let b := Module.Free.chooseBasis ℤ Lz
  let bR := Module.Basis.ofZLatticeBasis ℝ Lz b
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bR, ← eq_intCast (Int.castRingHom ℝ),
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.ofZLatticeBasis_apply, ← hfL, Module.Basis.ofZLatticeBasis_repr_apply]
  rfl

private theorem exists_lattice_reps {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : AddSubgroup E) (hd : DiscreteTopology L)
    (hs : Submodule.span ℝ (L : Set E) = ⊤) (f : E →ₗ[ℝ] E) (hf : ∀ z ∈ L, f z ∈ L)
    (hdet : LinearMap.det f ≠ 0) :
    ∃ Fz : Finset E, (∀ z ∈ Fz, f z ∈ L) ∧ (∀ z, f z ∈ L → ∃! z', z' ∈ Fz ∧ z - z' ∈ L) ∧
      (Fz.card : ℝ) = |LinearMap.det f| := by
  classical
  let Lz : Submodule ℤ E := AddSubgroup.toIntSubmodule L
  haveI : DiscreteTopology Lz := hd
  haveI : IsZLattice ℝ Lz := ⟨hs⟩
  haveI := ZLattice.module_free ℝ Lz
  haveI := ZLattice.module_finite ℝ Lz
  let fL : Lz →ₗ[ℤ] Lz :=
    { toFun := fun x => ⟨f x, hf x x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp }
  have hfL : ∀ x, (fL x : E) = f x := fun x => rfl
  have hdetZ := det_lattice_restrict_eq_det Lz f fL hfL
  have hdetL : LinearMap.det fL ≠ 0 := by
    intro h; apply hdet; rw [← hdetZ, h]; simp
  let fe := LinearMap.equivOfDetNeZero f hdet
  have hfe : ∀ z, fe z = f z := fun z => rfl
  have finj : Function.Injective f := by
    intro x y h; apply fe.injective; rw [hfe, hfe, h]
  have hinj : Function.Injective fL := fun x y h => Subtype.ext (finj (congrArg Subtype.val h))
  let N := LinearMap.range fL
  let e := LinearEquiv.ofInjective fL hinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ (e : Lz →+ N).toIntLinearMap = fL := by ext x; rfl
  rw [hcomp] at hcard
  haveI : Finite (Lz ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Int.natAbs_ne_zero.mpr hdetL)
  letI := Fintype.ofFinite (Lz ⧸ N)
  let s : (Lz ⧸ N) → E := fun q => fe.symm ((Quotient.out q : Lz) : E)
  have hs_f : ∀ q, f (s q) = ((Quotient.out q : Lz) : E) := fun q => by
    rw [← hfe]; exact fe.apply_symm_apply _
  have hsinj : Function.Injective s := by
    intro q q' h
    have h1 : (Quotient.out q : Lz) = Quotient.out q' := Subtype.ext (by rw [← hs_f, ← hs_f, h])
    rw [← Submodule.Quotient.mk_out q, ← Submodule.Quotient.mk_out q', h1]
  have key : ∀ z (hz : f z ∈ L) (q' : Lz ⧸ N),
      z - s q' ∈ L ↔ q' = Submodule.Quotient.mk (⟨f z, hz⟩ : Lz) := by
    intro z hz q'
    constructor
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N :=
        ⟨⟨z - s q', h⟩, by ext; simp [fL, hs_f]⟩
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out] at hm
      exact hm.symm
    · intro h
      have hm : (⟨f z, hz⟩ : Lz) - Quotient.out q' ∈ N := by
        rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out, h]
      obtain ⟨l, hl⟩ := hm
      have : f (l : E) = f (z - s q') := by
        rw [← hfL, hl, map_sub, hs_f]; rfl
      rw [← finj this]; exact l.2
  refine ⟨Finset.univ.image s, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hs_f]; exact (Quotient.out q).2
  · intro z hz
    refine ⟨s (Submodule.Quotient.mk (⟨f z, hz⟩ : Lz)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (key z hz _).mpr rfl⟩, ?_⟩
    rintro z' ⟨hz', hzz'⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz'
    rw [(key z hz q).mp hzz']
  · rw [Finset.card_image_of_injective _ hsinj, Finset.card_univ, ← Nat.card_eq_fintype_card, ← hcard,
      ← hdetZ, Nat.cast_natAbs, Int.cast_abs]

theorem UpperTheory.Gal.W2.torusCount_of :
    UpperTheory.Gal.W2.DetReal → UpperTheory.Gal.W2.TorusCount := by
  intro hDR W _ _ _ Λ hd hs Θ hΘ hdet
  let f : W →ₗ[ℝ] W := (1 - Θ).restrictScalars ℝ
  have hR : ((LinearMap.det f : ℝ) : ℂ) = _ := hDR W (1 - Θ)
  have hdf : LinearMap.det f = Complex.normSq (LinearMap.det (1 - Θ)) := by
    apply Complex.ofReal_injective
    rw [hR, Complex.mul_conj]
  have hfz : ∀ z, f z ∈ Λ ↔ Θ z - z ∈ Λ := by
    intro z
    show (1 - Θ) z ∈ Λ ↔ _
    rw [LinearMap.sub_apply, Module.End.one_apply, ← neg_sub, neg_mem_iff]
  have hfL : ∀ z ∈ Λ, f z ∈ Λ := fun z hz => (hfz z).mpr (sub_mem (hΘ z hz) hz)
  have hpos : 0 < LinearMap.det f := by rw [hdf]; exact Complex.normSq_pos.mpr hdet
  obtain ⟨Fz, h1, h2, h3⟩ := exists_lattice_reps Λ hd hs f hfL hpos.ne'
  refine ⟨Fz, fun z hz => (hfz z).mp (h1 z hz), fun z hz => h2 z ((hfz z).mpr hz), ?_⟩
  rw [Complex.mul_conj, ← hdf, ← abs_of_pos hpos, ← h3]
  norm_cast
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR
open Polynomial
open scoped Classical

namespace UpperTheory.Gal.W2

def SimDiag : Prop :=
  ∀ (g : ℕ) (I : Type) (M : I → Matrix (Fin g) (Fin g) ℂ), (∀ i j, M i * M j = M j * M i) →
    (∀ i, ∃ p : ℂ[X], p.Separable ∧ aeval (M i) p = 0) → ∃ (Sb : Matrix (Fin g) (Fin g) ℂ) (d : I → Fin g → ℂ),
      Sb.det ≠ 0 ∧ ∀ i, M i * Sb = Sb * Matrix.diagonal (d i)

def ExtendEmb : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (φ : 𝓞 F →+* ℂ), ∃ τ : F →+* ℂ, ∀ c : 𝓞 F, φ c = τ (c : F)

def KillsMat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ q : (𝓞 F)[X], Kills a ga q ↔ (q.sum fun i b => ρ (a b) * H ^ i) = 0

def HSep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (H : Matrix (Fin g) (Fin g) ℂ), (∀ c, ρ (a c) * H = H * ρ (a c)) → ∀ χ : F[X], χ.Monic → χ.Separable →
    (∀ q : (𝓞 F)[X], χ ∣ q.map (algebraMap (𝓞 F) F) → (q.sum fun i b => ρ (a b) * H ^ i) = 0) →
    ∃ p : ℂ[X], p.Separable ∧ aeval H p = 0

def DiagExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ χ : F[X], IsMinOf a ga χ → χ.Separable → ∃ Sb ty ev, IsDiag a ρ H Sb ty ev

def TypeCount : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ H : Matrix (Fin g) (Fin g) ℂ, ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ ∧ (evFull ty ev τ).card = n

def TraceLat : Prop :=
  ∀ (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (g : ℕ) (P : L →+ (Fin g → ℂ)), Function.Injective P →
    DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → ∀ (f : L →ₗ[ℤ] L) (H : Matrix (Fin g) (Fin g) ℂ),
    (∀ x, P (f x) = H *ᵥ P x) → ((LinearMap.trace ℤ L f : ℤ) : ℂ) = H.trace + (starRingEnd ℂ) H.trace

def TraceDual : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (s : (F →+* ℂ) → ℂ),
    (∀ c : 𝓞 F, ∃ m : ℤ, ∑ τ : F →+* ℂ, τ (c : F) * s τ = m) → ∃ b : F, ∀ τ, s τ = τ b

def NewtonPoly : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (m : (F →+* ℂ) → Multiset ℂ), (∀ τ, (m τ).card = n) →
    (∀ j : ℕ, ∃ b : F, ∀ τ, ((m τ).map fun r => r ^ j).sum = τ b) →
    ∃ χ : F[X], χ.Monic ∧ χ.natDegree = n ∧ ∀ τ, χ.map τ = ((m τ).map fun r => X - C r).prod

def PowSumRat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ j : ℕ, ∃ b : F, ∀ τ, ((evFull ty ev τ).map fun r => r ^ j).sum = τ b

def RootsFull : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ χ : F[X], IsMinOf a ga χ → χ.natDegree = n → ∀ τ, rts χ τ = evFull ty ev τ

def MarkDiag : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ H : Matrix (Fin g) (Fin g) ℂ, ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ mu, IsMark a ρ t₀ H mu ↔ evAt ty ev t₀ = {mu}

def TspDiag : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (ty : Fin g → (F →+* ℂ)) (t₀ : F →+* ℂ) (i₀ : Fin g), ComplexEmbedding.conjugate t₀ ≠ t₀ →
    (∀ i, ty i = t₀ ↔ i = i₀) → (∀ i j, ty j = ComplexEmbedding.conjugate (ty i) → i = i₀ ∨ j = i₀) →
    ∀ W : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ),
    (∀ S, S ∈ W ↔ Sᵀ = S ∧ ∀ (c : 𝓞 F) i j, S i j * ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) * S i j) →
    Function.Bijective (fun (S : W) (j : {j // ty j = ComplexEmbedding.conjugate t₀}) => S.1 i₀ j.1)

def BallChar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ H : Matrix (Fin g) (Fin g) ℂ, H.det ≠ 0 → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ mu, evAt ty ev t₀ = {mu} →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), IsCoordC bar ρ M₀ co →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) → d = n - 1 ∧
      ∀ y : ℂ, LinearMap.det (1 - y • T) =
        ((evAt ty ev (ComplexEmbedding.conjugate t₀)).map fun r => 1 - y * (mu / (starRingEnd ℂ) r)).prod

def CspDim : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∃ co : (Fin (n - 1) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, IsCoordC bar ρ M₀ co

def FibDet : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (H : Matrix (Fin g) (Fin g) ℂ), ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ (k : ℕ) (α : Fin k → 𝓞 F) (y : ℂ),
    LinearMap.det (1 - y • fibMap H (diagAct a ρ α)) = ∏ s, ∏ i, (1 - ty i (α s : F) * (y * ev i))

def FibW : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ)
    (χ : F[X]) (mu : ℂ), (∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ) → 1 ≤ n →
    (∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1) →
    (∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ) → (∀ τ, rts χ τ = evFull ty ev τ) → evAt ty ev t₀ = {mu} →
    ∀ (x : F) (y : ℂ), (∏ i, (1 - ty i x * (y * ev i))) * (starRingEnd ℂ) (∏ i, (1 - ty i x * ev i)) = fibW t₀ ε x y χ mu

def EvIntegral : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)), IsPeriod D ρ P₀ → ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), (∀ x, P₀ (ga x) = H *ᵥ P₀ x) → ∀ (Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ), IsDiag a ρ H Sb ty ev → ∀ i (x : 𝓞 F), 1 - ty i ((2 * x : 𝓞 F) : F) * ev i ≠ 0

def EigTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 F →+* O) (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ), IsSig a bar ρ n t₀ ε → ∀ (D : PLat O bar) (P₀ : D.La →+ (Fin g → ℂ)) (M₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → IsHermOf D P₀ M₀ →
    ∀ (ga : D.La →ₗ[O] D.La) (H : Matrix (Fin g) (Fin g) ℂ), FixesPer D P₀ ga H → ∀ χ : F[X], IsMinOf a ga χ → χ.natDegree = n → χ.Separable →
    ∀ (d : ℕ) (co : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ), IsCoordC bar ρ M₀ co →
    ∀ T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ), (∀ b, co (T b) = H * co b * (H.map star)⁻¹) →
    ∀ (k : ℕ) (α : Fin k → 𝓞 F), (∀ s, (2 : 𝓞 F) ∣ α s) → (∃ mu, IsMark a ρ t₀ H mu) ∧ ∀ mu, IsMark a ρ t₀ H mu →
      mu ∈ rts χ t₀ ∧ LinearMap.det (1 - T) ≠ 0 ∧ LinearMap.det (1 - fibMap H (diagAct a ρ α)) ≠ 0 ∧
      ∀ t : ℂ, LinearMap.det (1 - t • T) / LinearMap.det (1 - T) * (LinearMap.det (1 - t • fibMap H (diagAct a ρ α)) *
        (starRingEnd ℂ) (LinearMap.det (1 - fibMap H (diagAct a ρ α)))) = locW t₀ ε α t χ mu

def RootSumW : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (m : ℕ),
    ComplexEmbedding.conjugate t₀ ≠ t₀ → (∀ i, lam (ComplexEmbedding.conjugate t₀) i = m) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 F) ∣ α s) ∧
      ∀ (χ : F[X]) (r : (F →+* ℂ) → Fin n → ℂ), χ.Separable → (∀ τ, rts χ τ = Finset.univ.val.map (r τ)) → ∀ y : ℂ,
        (c.sum fun α w => w * ((rts χ t₀).map fun mu => locW t₀ ε α y χ mu).sum) =
          (∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ)) *
            (y ^ ((n - 1) * m + ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ i, lam τ i) *
              ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))

def RootSumWOff : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (lam : (F →+* ℂ) → Fin n → ℕ) (m : ℕ),
    ComplexEmbedding.conjugate t₀ ≠ t₀ → (∀ i, lam t₀ i = m) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ c : (Fin k → 𝓞 F) →₀ ℂ, (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ (2 : 𝓞 F) ∣ α s) ∧
      ∀ (χ : F[X]) (r : (F →+* ℂ) → Fin n → ℂ), χ.Separable → (∀ τ, rts χ τ = Finset.univ.val.map (r τ)) → χ.coeff 0 ≠ 0 → (∃ q : ℝ, ∀ z ∈ rts χ t₀, z * (starRingEnd ℂ) z = q) → ∀ y : ℂ,
        (c.sum fun α w => w * ((rts χ t₀).map fun mu => locW t₀ ε α y χ mu).sum) =
          (∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ)) *
            (y ^ (m + ∑ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ε τ * ∑ i, lam τ i) *
              ∑ i : Fin n, y ^ (∑ j ∈ Finset.univ.erase i, lam (ComplexEmbedding.conjugate t₀) j + (i : ℕ)))

end UpperTheory.Gal.W2
end
end

