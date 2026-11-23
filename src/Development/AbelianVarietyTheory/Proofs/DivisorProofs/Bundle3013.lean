module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedSymmetricCubicalBundleExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BundleExt

theorem exists_rigLB_cubical_symm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ (PP : RigLB G) (cub : CubicalStr G PP), PP.IsSymmetric ∧ ∃ cm : CubeMap tF.G G, cm.F = e ∧ cm.e = j ∧ cm.IsPullCubical tF.cub cub := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hns Z zs i OZ N d J S π j _ BD hU hPre tF htF G _ _ e hsa he hC
  obtain ⟨M, hM, hw⟩ := _root_.GlobalTheory.DescLBExt.exists_lb_extension Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hPre tF htF G e hsa he hC
  obtain ⟨⟨-, -, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU
  have := hsa.smooth
  have := hsa.geomConnected
  obtain ⟨h1, h2⟩ : QuasiCompact (π ≫ zs) ∧ LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    exact ⟨inferInstance, inferInstance⟩
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ zs)
  haveI : IsDominant j := ⟨hdense⟩
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  obtain ⟨L', c', m, hF, he', hpc, hsym⟩ :=
    DenseCubeExt.exists_cubical_extension S _ j hS G tF.G e he tF.PP tF.cub M hM hw
  exact ⟨L', c', hsym tF.sym, m, hF, he', hpc⟩

end GlobalTheory.BundleExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRouteDatumFinitePureTensorsVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_routeDatum_finite_pureTensors_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧
        ∃ (ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ))
          (P : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁))
          (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁)) (c : ℂ),
          Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧
          ∀ Y, ι φ₀ Y = c * (matLat (Fin (G.V (.grid i j)).rank) Λ : Set _).indicator 1 (P.val * Y) := by
  first | exact @GlobalTheory.SmallDatum.exists_datum_pure_linBar | exact GlobalTheory.SmallDatum.exists_datum_pure_linBar | (intros; apply GlobalTheory.SmallDatum.exists_datum_pure_linBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricChartRingFactorisationLocalHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isComplAt_ringEquiv_comp {A R S : Type} [CommRing A] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (ψ : A →+* R) (σ : R ≃+* S) (h : IsComplAt ψ) : IsComplAt ((σ : R →+* S).comp ψ) := by
  obtain ⟨hN, hC, hF, hM, hR⟩ := h
  have hmap : (maximalIdeal R).map σ = maximalIdeal S := map_ringEquiv_maximalIdeal σ
  have hcomap : (maximalIdeal S).comap (σ : R →+* S) = maximalIdeal R := by
    rw [← hmap]; exact Ideal.comap_map_of_bijective _ σ.bijective
  refine ⟨isNoetherianRing_of_ringEquiv R σ, ?_, ?_, ?_, ?_⟩
  · haveI := hC
    rw [← hmap, IsAdicComplete.congr_ringEquiv]; exact hC
  · exact RingHom.Flat.comp hF (RingHom.Flat.of_bijective σ.bijective)
  · rw [← Ideal.comap_comap, hcomap, ← Ideal.map_map, hM]; exact hmap
  · intro s
    obtain ⟨a, b, hb, hab⟩ := hR (σ.symm s)
    refine ⟨a, b, ?_, ?_⟩
    · simpa using hb.map (σ : R →+* S)
    · have : (σ : R →+* S) (σ.symm s * ψ b - ψ a) ∈ maximalIdeal S := by
        rw [← Ideal.mem_comap, hcomap]; exact hab
      simpa using this

theorem exists_chartRing_factor : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W], Nonempty (ℚ →+* W) → ∀ (m N : ℕ) (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial (Fin m ⊕ Fin N) W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → (∀ i, ψV (MvPolynomial.X (.inl i)) ∈ maximalIdeal V) → ∃ (k : Type) (_ : Field k) (e : ℕ) (ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* ChartRing k m e) (θ : ChartRing k m e →+* V), GlobalTheory.TChart.IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) ∧ ∀ i, ψ (MvPolynomial.X (.inl i)) = bdParam k m e i := by
  intro W _ _ hQ m N V _ _ hV ψV hCV hXV
  obtain ⟨R, _, _, _, ψ, θ, hψ, hθ, hθψ, hψC⟩ :=
    exists_complAt_factor_of_isAdicComplete W (Fin m ⊕ Fin N) V hV ψV hCV
  obtain ⟨hreg, -⟩ := isRegularLocalRing_and_isDomain_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC
  haveI := hreg
  let t : Fin m → R := fun i => ψ (MvPolynomial.X (.inl i))
  have ht : ∀ i, t i ∈ maximalIdeal R := by
    intro i
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (θ (t i)) := hu.map θ
    have h2 : θ (t i) = ψV (MvPolynomial.X (.inl i)) := by
      show (θ.comp ψ) _ = _; rw [hθψ]
    rw [h2] at h1
    exact (mem_maximalIdeal _).1 (hXV i) h1
  have hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R := by
    intro a ha i
    exact cotangent_indep_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC m (Function.Embedding.inl) ht a
      (Ideal.mem_sup_left ha) i
  have hQR : Nonempty (ℚ →+* R) := ⟨(ψ.comp MvPolynomial.C).comp hQ.some⟩
  obtain ⟨k, _, e, σ, hσ⟩ := _root_.GlobalTheory.CohenChart.exists_ringEquiv_chartRing R hψ.2.1 hQR m t ht hind
  refine ⟨k, inferInstance, e, (σ : R →+* ChartRing k m e).comp ψ, θ.comp (σ.symm : ChartRing k m e →+* R),
    isComplAt_ringEquiv_comp ψ σ hψ, inferInstance, ?_, ?_, ?_⟩
  · rw [← hθψ]; ext x <;> simp
  · show IsLocalHom ((σ : R →+* ChartRing k m e).comp (ψ.comp MvPolynomial.C))
    infer_instance
  · intro i; exact hσ i

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m : ℕ), Odd m → ∀ (T : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (y : T ⟶ P.A) (c : Γ(T.left, ⊤)), GlobalTheory.Ex.OneGen.ThG P.A P.L rig m th y c → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (y ^ m).left) (fun _ => 1)), IsTorsFrame P rig m (y ^ m) τ ∧ IsValueAt P.A P.L ((1 : ℕ) : ℤ) th (y ^ m) (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) c := by
  first | exact @GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt | exact GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt | (intros; apply GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTorsionLiftZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsLiftRoot

open ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cubN_succ' (k : ℕ) (a m x : A) : cubN θ (k + 1) a m x = cubN θ k a m x * θ (a * m ^ k) m x :=
  Finset.prod_range_succ _ _

theorem ex_pow (c x : A) (w : U) (k : ℕ) :
    (⟨x, w⟩ : Ex h c) ^ k = ⟨x ^ k, w ^ k * (cubN θ k 1 x c)⁻¹⟩ := by
  induction k with
  | zero => exact Ex.ext (pow_zero x).symm (by simp [cubN]; rfl)
  | succ k ih =>
    rw [pow_succ, ih]
    refine Ex.ext (pow_succ x k).symm ?_
    rw [Ex.mul_u, cubN_succ' h]
    show _ = _ * (_ * θ (1 * x ^ k) x c)⁻¹
    rw [_root_.one_mul, h.s01 c, h.s12 (x ^ k) c x, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem cubN_pow (a x : A) (n k : ℕ) :
    cubN θ n 1 a (x ^ k) * cubN θ k 1 x a ^ n = cubN θ n 1 a x ^ k * cubN θ k 1 x (a ^ n) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, h.N_one]; simp [cubN]
  | succ k ih =>
    have e := h.N_add n 1 a (x ^ k) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    rw [cubN_succ' h, cubN_succ' h, _root_.one_mul, pow_succ x k, h.s12 (x ^ k) x a, h.s01 (x ^ k) a x,
      h.s12 (x ^ k) x (a ^ n), h.s01 (x ^ k) (a ^ n) x]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ih' ⊢
    simp only [add_nsmul, one_nsmul, nsmul_add]
    linear_combination (norm := abel) e' + ih'

end Alg

section Key

variable {A U X : Type} [CommGroup A] [CommGroup U] [AddCommGroup X] [Module.Free ℤ X] {θ : A → A → A → U}
  (h : IsCub θ)
include h

theorem exists_mult_pow_eq_one {c : X → A} (hc : ∀ χ χ', c (χ + χ') = c χ * c χ') {n : ℕ} (c' : X → A)
    (hc' : ∀ χ, c' χ ^ n = c χ) {b : A} (hb : b ^ n = 1) :
    ∃ v, Mult θ c b v ∧ ∀ χ, ((⟨b, v χ⟩ : Ex h (c χ)) ^ n).u = 1 := by
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive (Ex h b) := e.constr ℤ fun i => Additive.ofMul ⟨c' (e i), 1⟩
  let p : Additive (Ex h b) →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul x.toMul.b) fun _ _ => rfl
  have fb : ∀ χ, (f χ).toMul.b ^ n = c χ := fun χ => by
    have := LinearMap.congr_fun (e.ext (f₁ := n • (p.toIntLinearMap ∘ₗ f))
      (f₂ := (AddMonoidHom.mk' (fun χ => Additive.ofMul (c χ)) hc).toIntLinearMap) fun i => by
        show n • p (f (e i)) = Additive.ofMul (c (e i))
        rw [show f (e i) = Additive.ofMul ⟨c' (e i), 1⟩ from e.constr_basis ℤ _ i, ← hc', ofMul_pow]; rfl) χ
    exact Additive.ofMul.injective (by rw [ofMul_pow]; exact this)
  have fadd : ∀ χ χ', (f (χ + χ')).toMul = (f χ).toMul * (f χ').toMul := fun χ χ' => by rw [map_add (f := _)]; rfl
  let g : X → Ex h b := fun χ => (f χ).toMul ^ n
  have gadd : ∀ χ χ', g (χ + χ') = g χ * g χ' := fun χ χ' => by simp only [g, fadd, mul_pow]
  have gb : ∀ χ, (g χ).b = c χ := fun χ => (Ex.pow_b _ _).trans (fb χ)
  have m : Mult θ c b fun χ => (g χ).u := by
    refine ⟨?_, fun χ χ' => ?_⟩
    · show ((f 0).toMul ^ n).u = 1
      rw [map_zero, toMul_zero, one_pow]; rfl
    · show (g (χ + χ')).u * _ = _
      rw [gadd, Ex.mul_u, gb, gb, h.s01 b, h.s12 (c χ) b, inv_mul_cancel_right]
  have mp := m.pow (h := h) hc n
  have wadd : ∀ χ χ', ((⟨b, (g (χ + χ')).u⟩ : Ex h (c (χ + χ'))) ^ n).u =
      ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u * ((⟨b, (g χ').u⟩ : Ex h (c χ')) ^ n).u := fun χ χ' => by
    have := mp.2 χ χ'
    rwa [hb, h.face₃, _root_.mul_one] at this
  have wroot : ∀ χ, ∃ r : U, r ^ n = ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u := fun χ => by
    refine ⟨(f χ).toMul.u ^ n * (cubN θ n 1 b (f χ).toMul.b)⁻¹, ?_⟩
    have e₁ : (g χ).u = (f χ).toMul.u ^ n * (cubN θ n 1 (f χ).toMul.b b)⁻¹ := by
      show ((f χ).toMul ^ n).u = _
      rw [show (f χ).toMul = ⟨(f χ).toMul.b, (f χ).toMul.u⟩ from rfl, ex_pow h]
    rw [ex_pow h, ← fb χ]
    show _ = (g χ).u ^ n * (cubN θ n 1 b ((f χ).toMul.b ^ n))⁻¹
    have e₂ := cubN_pow h (f χ).toMul.b b n n
    rw [hb, h.N_one, _root_.one_mul] at e₂
    rw [e₁]
    apply Additive.ofMul.injective
    have e₂' := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, nsmul_add, nsmul_neg] at e₂' ⊢
    rw [smul_neg, smul_neg, e₂']
    abel
  choose r hr using wroot
  let W : X →ₗ[ℤ] Additive U := (AddMonoidHom.mk' (fun χ => Additive.ofMul ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u)
    wadd).toIntLinearMap
  let ro : X →ₗ[ℤ] Additive U := e.constr ℤ fun i => Additive.ofMul (r (e i))⁻¹
  have roW : ∀ χ, (ro χ).toMul ^ n * ((⟨b, (g χ).u⟩ : Ex h (c χ)) ^ n).u = 1 := fun χ => by
    have := LinearMap.congr_fun (e.ext (f₁ := n • ro) (f₂ := -W) fun i => by
      show n • ro (e i) = -W (e i)
      rw [show ro (e i) = Additive.ofMul (r (e i))⁻¹ from e.constr_basis ℤ _ i, ← ofMul_pow, inv_pow, hr]; rfl) χ
    apply Additive.ofMul.injective
    rw [ofMul_mul, ofMul_pow, ofMul_one]
    exact eq_neg_iff_add_eq_zero.1 this
  have roadd : ∀ χ χ', (ro (χ + χ')).toMul = (ro χ).toMul * (ro χ').toMul := fun χ χ' => by rw [map_add (f := _)]; rfl
  refine ⟨fun χ => (g χ).u * (ro χ).toMul, ⟨?_, fun χ χ' => ?_⟩, fun χ => ?_⟩
  · show (g 0).u * (ro 0).toMul = 1
    rw [show (g 0).u = 1 from m.1, map_zero, toMul_zero, _root_.mul_one]
  · show (g (χ + χ')).u * (ro (χ + χ')).toMul * _ = (g χ).u * (ro χ).toMul * ((g χ').u * (ro χ').toMul)
    rw [roadd, mul_right_comm, m.2, _root_.mul_mul_mul_comm]
  · rw [ex_pow h, ← roW χ, ex_pow h, mul_pow]
    show (g χ).u ^ n * (ro χ).toMul ^ n * _ = (ro χ).toMul ^ n * ((g χ).u ^ n * _)
    rw [mul_comm ((g χ).u ^ n), _root_.mul_assoc]

end Key

section Main

theorem exists_qk_zero_of_pow_eq : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℕ), 1 ≤ n →
    ∀ (c' : D.X → (𝟙_ (Over (Sp R)) ⟶ D.P.A)), (∀ χ, c' χ ^ n = D.c χ) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A), b ^ n = 1 →
    ∃ p : QkPt D F n, p.y = 0 ∧ p.g.b = b := by
  intro R _ _ D hB n _ c' hc' F _ _ b hb
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  have C := isCub_cubV D.cub (T := TF (R := R) F) hJ
  have cpw : ∀ (x : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (k : ℕ), toUnit (TF (R := R) F) ≫ x ^ k = (toUnit _ ≫ x) ^ k :=
    fun x k => by
      induction k with
      | zero => rw [pow_zero, pow_zero]; exact MonObj.comp_one _
      | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  have cpow : ∀ χ, (toUnit (TF (R := R) F) ≫ c' χ) ^ n = cP D (TF (R := R) F) χ := fun χ => by
    rw [← cpw, hc']; rfl
  obtain ⟨v, m, hv⟩ := exists_mult_pow_eq_one C (cPoint_add D (TF (R := R) F)) (fun χ => toUnit _ ≫ c' χ) cpow hb
  have i0 : ∀ χ, ix (𝟙 _) hJ (0 : D.X) χ = 1 := fun χ => by
    have := ix_add (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨q, h₁, h₂, -⟩ := exists_qk hJ (n := n) 0 b v m fun χ => by
    rw [i0]; exact Ex.ext ((Ex.pow_b _ _).trans hb) (hv χ)
  exact ⟨q, h₁, h₂⟩

end Main

end GlobalTheory.TorsLiftRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeEquivCompletedLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory.UPoinc.TraitCompare

theorem exists_trait_lattice_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ (x : Y.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : Y.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsSemiAbelian G → IsGrpPullback G out.G (spMap j ≫ Y.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ ρT : D.toPre.X ≃+ T.P.D.toPre.X, (∀ y s, PsiCoord D.toPre y s → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (ψ s ^ 2) (T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r _hOver _hpt f _hf habl hT x R _ _ _ j hR _hj G _ _ gm hG hgm D A U hLB
    hPsi m hm T ψ hψ hTy
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : CharZero T.V := T.cdvr.2.2
  have hTV : GlobalTheory.Mum.Base T.V := ⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR T.cdvr, inferInstance⟩
  have hξT : spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x = spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [spMap_comp, Category.assoc]
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := by
    simp [spMap]
  obtain ⟨tW, mW, PW, e, he⟩ := GlobalTheory.UPoinc.TraitPull.exists_pull_unif E H Dw l Xo c T T.V hTV inferInstance (RingHom.id T.V)
    (fun _ _ h => h) inferInstance
  obtain ⟨βT, hβT, hLT, hactT⟩ := hT T _ hTy
  have hβ' : IsGrpPullback tW.G out.G (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) (mW.φ ≫ βT) :=
    (mW.cart.comp hβT).congr (by rw [hid, Category.id_comp, hξT]) rfl
  have w : (mW.φ ≫ βT) ≫ out.G.hom = (tW.G.hom ≫ spMap ψ) ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [hβ'.1.w, Category.assoc]
  let β : tW.G.left ⟶ G.left := hgm.1.lift (mW.φ ≫ βT) (tW.G.hom ≫ spMap ψ) w
  have hβgm : β ≫ gm = mW.φ ≫ βT := hgm.1.lift_fst _ _ _
  have hβG : β ≫ G.hom = tW.G.hom ≫ spMap ψ := hgm.1.lift_snd _ _ _
  have hβ : IsGrpPullback tW.G G (spMap ψ) β := hgm.cancel (by rw [hβgm]; exact hβ') hβG
  have hLBW : LBIso PW.U.LG.L (U.LG.L.pull β) := by
    rw [PW.bundle]
    exact LBIso.trans tW.PP.isLB (LB.isLB_pull out.L.isLB _) (LB.isLB_pull U.LG.isLB _)
      (LBIso.trans tW.PP.isLB (LB.isLB_pull T.t.PP.isLB _) (LB.isLB_pull out.L.isLB _)
        (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mW) (GlobalTheory.LN.GenericPoint.lbIso_pull hLT mW.φ rfl))
      (GlobalTheory.LN.GenericPoint.lbIso_pull hLB β hβgm.symm).symm

  have hab : ∀ z, (spMap j ≫ Y.Z.fromSpecStalk x) z ∈ abLocus out.G ↔ z ∈ abLocus G :=
    abLocus_pullback abLocusOne out.semi hgm.1
  have hTy' : jK T.V ≫ (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) ≫ r = T.y ≫ C.i := by
    rw [← hξT]; exact hTy
  have hgen : spMap ψ (genericPoint (Sp T.V)) ∈
      (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    show _ ∈ abLocus G
    rw [← hab]
    apply habl
    let pt : Sp (FractionRing T.V) := ⟨⊥, Ideal.isPrime_bot⟩
    have hpt : jK T.V pt = genericPoint (Sp T.V) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun s => ?_)
      change algebraMap T.V (FractionRing T.V) s ∈ (⊥ : Ideal (FractionRing T.V)) ↔ s ∈ (⊥ : Ideal T.V)
      rw [Ideal.mem_bot, Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff]
    rw [← hpt]
    exact ⟨T.y pt, (congrArg (fun g : Sp (FractionRing T.V) ⟶ C.Z => g pt) hTy').symm⟩

  have hPsi' : ∀ y, PsiUnitOn D.toPre y (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    intro y
    have hs : (⇑(spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G) = abLocus G := Set.ext hab
    have := hPsi y
    rw [hs] at this
    exact this

  let bc : tW.G ≅ (Over.pullback (specOf ψ)).obj G :=
    Over.isoMk hβ.1.isoPullback (by simp)
  have hbcβ : β = bc.hom.left ≫ pullback.fst G.hom (specOf ψ) := by
    simp [bc]
  have hbc : IsMonHom bc.hom := GlobalTheory.Mum.isMonHom_of_isGrpPullback_fst bc (hβ.congr rfl hbcβ)
  obtain ⟨D₂, A₂, hD, U₂, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U T.V hTV.1 ψ hψ _ hPsi' hgen tW.G bc hbc
  obtain ⟨hL₁, hC₁, hE₁⟩ := PullUnif.main R hR G hG D A U T.V hTV tW.G tW.semi D₂ A₂ U₂ ψ β hψ bc hbc hbcβ hD hU

  have hid' : IsGrpPullback tW.G tW.G (spMap (RingHom.id T.V)) (𝟙 tW.G.left) :=
    GlobalTheory.LN.SelfCmp.isGrpPullback_of_eq_id tW.G hid
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U
    (RingHom.id T.V) (𝟙 _) hid'
  have hρs := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  have hρT := GlobalTheory.SpreadTorMatch.torMatch_of_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂ U₂
    (RingHom.id T.V) (𝟙 _) hid'
  have hρ's := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂
    U₂ (RingHom.id T.V) (𝟙 _) hid' ρ' hρ'
  have hL₂ : LBIso PW.U.LG.L (U₂.LG.L.pull (𝟙 _)) :=
    LBIso.trans PW.U.LG.isLB (LB.isLB_pull U.LG.isLB _) (LB.isLB_pull U₂.LG.isLB _) hLBW
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL₁ (𝟙 _) (Category.id_comp β).symm).symm
  have hC₂ := TorCoord.coordMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV inferInstance tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id _) (𝟙 _) (fun _ _ h => h) hid' hL₂ ρ hρT
  have hE₂ := equivMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U (RingHom.id _)
    (𝟙 _) (fun _ _ h => h) ρ hρT
  obtain ⟨-, -, -, -, n, ⟨eZ⟩⟩ := GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice E H Dw l Xo c T
  haveI : Module.Finite ℤ T.P.D.toPre.X := Module.Finite.equiv eZ.symm
  haveI : Module.Finite ℤ PW.D.toPre.X := Module.Finite.equiv e.toAddEquiv.toIntLinearEquiv.symm
  have hρ'i : Function.Injective ρ' := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ.comp ρ').toIntLinearMap (hρs.comp hρ's)
    exact Function.Injective.of_comp (f := ⇑ρ) (g := ⇑ρ') h
  haveI : Module.Finite ℤ D₂.toPre.X := Module.Finite.of_surjective ρ'.toIntLinearMap hρ's
  have hρi : Function.Injective ρ := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ'.comp ρ).toIntLinearMap (hρ's.comp hρs)
    exact Function.Injective.of_comp (f := ⇑ρ') (g := ⇑ρ) h
  let ρE : D₂.toPre.X ≃+ PW.D.toPre.X := AddEquiv.ofBijective ρ ⟨hρi, hρs⟩
  refine ⟨(hD.xe.symm.trans ρE).trans e.toAddEquiv, ?_, ?_⟩
  · intro y s hs
    obtain ⟨r₂, hr₂⟩ := GlobalTheory.BetaAdd.exists_coord D₂ (hD.xe.symm y)
    obtain ⟨h0, r', hr', hass⟩ := he (ρ (hD.xe.symm y))
    refine ⟨h0, ?_⟩
    have h1 : Associated (ψ s) r' := (hC₁ y s r₂ hs hr₂).trans (hC₂ _ r₂ r' hr₂ hr' : Associated r₂ r')
    exact (h1.pow_pow (n := 2)).trans hass
  · intro a y
    obtain ⟨fR, hfRmon, hfRgm, hfRchar⟩ := hm a
    have hcompat : (tW.act.act a).left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc ((tW.act.act a).left ≫ β) ≫ gm = (tW.act.act a).left ≫ mW.φ ≫ βT := by rw [Category.assoc, hβgm]
          _ = mW.φ ≫ (T.t.act.act a).left ≫ βT := by rw [← Category.assoc, mW.act a, Category.assoc]
          _ = mW.φ ≫ βT ≫ (f a).left := by rw [hactT a]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, hfRgm, reassoc_of% hβgm]
      · rw [Category.assoc, hβG, Category.assoc, Over.w fR, hβG, ← Category.assoc, Over.w (tW.act.act a)]
    obtain ⟨m₂, hm₂⟩ := endChar_exists_of_isMonHom T.V hTV tW.G tW.semi D₂ A₂ U₂ (tW.act.act a) (tW.act.hom a)
    have h1 := hE₁ fR (tW.act.act a) hfRmon (tW.act.hom a) hcompat (m a) m₂ hfRchar hm₂ y
    have h2 := hE₂ (tW.act.act a) (tW.act.act a) (tW.act.hom a) (tW.act.hom a) (by simp) m₂ _ hm₂
      (GlobalTheory.UPoinc.endChar_act E H T.V hTV tW PW a) (hD.xe.symm y)
    show e (ρ (hD.xe.symm (m a y))) = H.bar a • e (ρ (hD.xe.symm y))
    have h1' : hD.xe.symm (m a y) = m₂ (hD.xe.symm y) := h1
    rw [h1', h2]
    exact e.map_smul _ _

end GlobalTheory.UPoinc.TraitCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromBase_identity_along_morphism : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])) (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧ (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (a b : Q.X) (zz : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L zz J → Good M₀ zz J₀ → val (τ₀ a b) r zz J = gm (r ≫ cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q (a + b) ≫ β), J (r ≫ cpt Q (a + b)))) * (gm (r ≫ cpt Q a) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q a ≫ β), J (r ≫ cpt Q a))))⁻¹ * (gm (r ≫ cpt Q b) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q b ≫ β), J (r ≫ cpt Q b))))⁻¹ * gm (r ≫ cpt Q 0) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q 0 ≫ β), J (r ≫ cpt Q 0))) * val (τ₁ a b) (r ≫ spMap ιb) zz J₀ := by
  first | exact @GlobalTheory.UChart.FromBaseAlong.fromBase_along | exact GlobalTheory.UChart.FromBaseAlong.fromBase_along | (intros; apply GlobalTheory.UChart.FromBaseAlong.fromBase_along <;> assumption)
end

