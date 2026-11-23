module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart


set_option backward.isDefEq.respectTransparency false in
theorem Taut.isRegularLocalRing_and_isRelParam : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ C : Taut (zetaAway n) g n φ, IsRegularLocalRing C.R ∧ CharZero C.R ∧ Function.Injective C.b ∧ C.b.Flat ∧ IsRelParam C.b C.t ∧ IsRegularLocalRing (C.R ⧸ ((maximalIdeal C.R).comap C.b).map C.b) := by
  intro g n φ _ C
  haveI : IsNoetherianRing C.W := C.noeth
  haveI : IsLocalHom C.iw := C.ψ_loc
  set X := (LowChart.powA C.F C.T.r).left with hX
  set π := LowChart.toO C.F C.T.r with hπ
  set y := C.u (closedPoint C.W) with hy
  let φ₀ : X.presheaf.stalk y →+* C.W := (Scheme.stalkClosedPointTo C.u).hom
  let σ := (π.stalkMap y).hom
  let L := Localization.AtPrime (π y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of (cycAway n)) (π y)
  let ρ : cycAway n →+* X.presheaf.stalk y := σ.comp (e.inv.hom.comp (algebraMap (cycAway n) L))
  have h3 : (Sp (cycAway n)).fromSpecStalk (π y) = Spec.map e.inv ≫ spMap (algebraMap (cycAway n) L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (π y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := π y)).symm
  have hb : C.T.b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk C.u
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y)
    have key : spMap C.T.b = spMap (φ₀.comp ρ) := by
      rw [← C.u_base, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (π y).asIdeal = (maximalIdeal C.W).comap C.T.b := by
    have : π y = spMap C.T.b (closedPoint C.W) := by
      rw [hy, ← C.u_base, Scheme.Hom.comp_apply]
    rw [this]; rfl
  haveI : IsRegularLocalRing (X.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk C.F y
  have het := C.u_et
  haveI hW : IsRegularLocalRing C.W := by
    letI : Algebra (X.presheaf.stalk y) C.W := φ₀.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y) C.W := het.1
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm
  obtain ⟨hRreg, hRdom⟩ := isRegularLocalRing_and_isDomain_of_isComplAt C.W (Fin C.m ⊕ Fin C.N) C.R C.ψ C.compl C.ψ_loc
  have hρspec : spMap ρ = X.fromSpecStalk y ≫ π := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y), h3]
    simp only [spMap, ρ, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
  have hflatρ : ρ.Flat := by
    haveI := GlobalTheory.SmoothStalkNormal.flat_fromSpecStalk' X y
    have h : Flat (spMap ρ) := by rw [hρspec]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  have hiwflat : C.iw.Flat :=
    (show (algebraMap C.W (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W)).Flat from
      RingHom.flat_algebraMap_iff.mpr inferInstance).comp C.compl.2.2.1
  have hbeq : C.b = C.iw.comp (φ₀.comp ρ) := by rw [← hb]; rfl
  have hbflat : C.b.Flat := by rw [hbeq]; exact (hflatρ.comp het.1).comp hiwflat
  have hinj : Function.Injective C.b := GlobalTheory.SmoothStalkNormal.injective_of_flat_of_isDomain C.b hbflat
  have hmW : (maximalIdeal C.R).comap C.iw = maximalIdeal C.W := IsLocalRing.maximalIdeal_comap C.iw
  have h𝔮 : (maximalIdeal C.R).comap C.b = (π y).asIdeal := by
    rw [hq, show C.b = C.iw.comp C.T.b from rfl, ← Ideal.comap_comap, hmW]
  have hle : ((maximalIdeal C.R).comap C.b).map C.b ≤ (maximalIdeal C.W).map (C.ψ.comp MvPolynomial.C) := by
    rw [show C.b = C.iw.comp C.T.b from rfl, ← Ideal.map_map]
    refine Ideal.map_mono (Ideal.map_le_iff_le_comap.2 ?_)
    rw [← Ideal.comap_comap, hmW]
  refine ⟨hRreg, charZero_of_injective_ringHom hinj, hinj, hbflat, ⟨fun k => C.bd k, fun c hc k =>
    cotangent_indep_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc C.m ⟨Sum.inl, Sum.inl_injective⟩ (fun k => C.bd k) c
      (sup_le_sup_left hle (maximalIdeal C.R ^ 2) hc) k⟩, ?_⟩
  have hfib := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal (Sp (cycAway n)) X π y
  set I := (maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y))).map σ with hIdef
  have hI : I = (π y).asIdeal.map ρ := by
    have hsurj : Function.Surjective e.inv.hom := e.commRingCatIsoToRingEquiv.symm.surjective
    have hmL : maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y)) = (maximalIdeal L).map e.inv.hom :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
    rw [hIdef, hmL, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    rfl
  set 𝔭 := I.map φ₀ with h𝔭def
  have h𝔭 : 𝔭.map C.iw = ((maximalIdeal C.R).comap C.b).map C.b := by
    rw [h𝔭def, hI, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hbeq, h𝔮]
  have hIm : I ≤ maximalIdeal (X.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap σ).ge
  have h𝔭m : 𝔭 ≤ maximalIdeal C.W := het.2.1 ▸ Ideal.map_mono hIm
  have h𝔭ne : 𝔭 ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top h𝔭m
  haveI : Nontrivial (C.W ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.2 h𝔭ne
  haveI : IsLocalRing (C.W ⧸ 𝔭) := IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
  have hreg𝔭 : IsRegularLocalRing (C.W ⧸ 𝔭) := by
    let χ : (X.presheaf.stalk y ⧸ I) →+* (C.W ⧸ 𝔭) := Ideal.quotientMap 𝔭 φ₀ Ideal.le_comap_map
    have hχflat : χ.Flat := GlobalTheory.Pat.flat_quotientMap_map φ₀ het.1 I
    letI : Algebra (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := χ.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := hχflat
    have hcomm : (Ideal.Quotient.mk 𝔭).comp φ₀ = χ.comp (Ideal.Quotient.mk I) := by
      ext a; simp [χ]
    have hmax : maximalIdeal (C.W ⧸ 𝔭) = (maximalIdeal (X.presheaf.stalk y ⧸ I)).map (algebraMap _ _) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective, ← het.2.1,
        ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
        Ideal.map_map, hcomm]
      rfl
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ _ hmax
  have hfin := isRegularLocalRing_quotient_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc 𝔭 h𝔭ne hreg𝔭
  rwa [show C.ψ.comp MvPolynomial.C = C.iw from rfl, h𝔭] at hfin

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularPeriodicRatioCoverFamilies
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isUnit_res_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (f : Γ(X, U)) (hVU : V ≤ U)
    (h : V ≤ X.basicOpen f) : IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  have e : X.presheaf.map (homOfLE hVU).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ X.presheaf.map (homOfLE h).op := by
    rw [← Functor.map_comp]; rfl
  rw [e]
  exact hu

theorem ratio_periodic_isReg : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (N : ℕ) (σ : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (σ k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), σ k (z + l) = σ k z) → (∀ k j, ∀ z ∈ pre u.ex (W k), z ∈ pre u.ex (W j) → σ k z = val u.ex _ (r k j) z ^ N * σ j z) → ∀ k, IsReg u.ex (W k) (σ k) := by
  intro A _ g L u hA n W r hR N σ hhol hper htr
  obtain ⟨-, -, -, -, hinf, hmono, -, -, hres, hev, -, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨-, hcov, hbasic, hself, hcoc⟩ := hR
  have hv : ∀ (U V : A.left.Opens) (h : V ≤ U) (b : Γ(A.left, U)), ∀ z ∈ pre u.ex V,
      val u.ex V ((A.left.presheaf.map (homOfLE h).op).hom b) z = val u.ex U b z :=
    fun U V h b z hz => hres U V h b z hz
  have hmul : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a * b) z = val u.ex U a z * val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_mul e (a : Sec (str A) U) b
  have hsub : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a - b) z = val u.ex U a z - val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_sub e (a : Sec (str A) U) b
  have hpow : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ (a : Γ(A.left, U)) (m : ℕ),
      val u.ex U (a ^ m) z = val u.ex U a z ^ m := by
    intro U z hz a m
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he]; exact map_pow e (a : Sec (str A) U) m
  have hunit : ∀ k j, IsUnit ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) :=
    fun k j => isUnit_res_of_le_basicOpen _ _ (hbasic k j).ge
  let M : LB A.left := ⟨Fin n, W, fun k j => (hunit k j).unit ^ N⟩
  have hMg : ∀ k j, ((M.g k j : Γ(A.left, W k ⊓ W j))) =
      ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) ^ N := by
    intro k j
    change (((hunit k j).unit ^ N : Γ(A.left, W k ⊓ W j)ˣ) : Γ(A.left, W k ⊓ W j)) = _
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]

  have hval : ∀ k j (V : A.left.Opens) (h : V ≤ W k ⊓ W j), ∀ z ∈ pre u.ex V,
      val u.ex V ((res h (M.g k j) : Γ(A.left, V))) z = val u.ex (W k) (r k j) z ^ N := by
    intro k j V h z hz
    have hz' : z ∈ pre u.ex (W k ⊓ W j) := hmono _ _ h hz
    have e1 : ((res h (M.g k j) : Γ(A.left, V))) =
        (A.left.presheaf.map (homOfLE h).op).hom (M.g k j : Γ(A.left, W k ⊓ W j)) := rfl
    rw [e1, hv _ _ h _ z hz, hMg, hpow _ z hz', hv _ _ _ _ z hz']
  have hM : M.IsLB := by
    refine ⟨hcov, fun k => ?_, fun k j l => ?_⟩
    · apply Units.ext
      change (A.left.presheaf.map _).hom (M.g k k : Γ(A.left, W k ⊓ W k)) = 1
      rw [hMg, hself k, map_one, one_pow, map_one]
    · apply Units.ext
      rw [Units.val_mul]
      apply sub_eq_zero.mp
      apply _root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA
      intro z hz
      have hk : z ∈ pre u.ex (W k) := hmono _ _ (inf_le_left.trans inf_le_left) hz
      have hj : z ∈ pre u.ex (W j) := hmono _ _ (inf_le_left.trans inf_le_right) hz
      rw [hsub _ z hz, hmul _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz,
        hcoc k j l z hk hj, mul_pow, sub_self]
  have htrans : ∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j),
      σ i z = val u.ex _ (M.g i j).val z * σ j z := by
    intro i j z hz
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := hz
    rw [hinf] at hz'
    have e := hval i j (W i ⊓ W j) le_rfl z hz
    have e2 : ((res (le_rfl : W i ⊓ W j ≤ W i ⊓ W j) (M.g i j) : Γ(A.left, W i ⊓ W j))) = (M.g i j).val := by
      change (A.left.presheaf.map (homOfLE le_rfl).op).hom _ = _
      have : (homOfLE (le_rfl : W i ⊓ W j ≤ W i ⊓ W j)).op = 𝟙 _ := rfl
      rw [this, CategoryTheory.Functor.map_id]; rfl
    rw [e2] at e
    change σ i z = val u.ex (W i ⊓ W j) (M.g i j).val z * σ j z
    rw [e]
    exact htr i j z hz'.1 hz'.2
  exact _root_.GlobalTheory.PeriodicSecAlg.main A g L u hA M hM σ hhol hper htrans

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {T : Scheme.{0}}
  (t : SAB H T)

def LatPres {R : Type} [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) {g M : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R) : Prop :=
  (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
    ∀ (cf : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x)
        (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp φ)) ≫ e i) cf w →
      (spMap (epsMul δ) ≫ w ∈ lat t p (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x) (kind p) ↔
        ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1)

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)


abbrev LocAssign {X W : Scheme.{0}} (r : ℕ) (jB : W ⟶ X) (U : X.Opens) : Type 1 :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W), ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)

end Free

end GlobalTheory.ArLieBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumProd

def tensLB {X : Scheme.{0}} (L M : LB X) : LB X :=
  LB.mk (L.ι × M.ι) (fun p => L.U p.1 ⊓ M.U p.2) fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) *
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2)

abbrev extLB {X X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) : LB X :=
  tensLB (L₁.pull f₁) (L₂.pull f₂)

section MapsAt

variable {Y X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

def extIdx (j₁ : L₁.ι) (j₂ : L₂.ι) : (extLB L₁ L₂ f₁ f₂).ι :=
  ((fun _ => j₁, fun _ => j₂) : (PUnit → L₁.ι) × (PUnit → L₂.ι))

lemma mapsAt₂_le_a (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

lemma mapsAt₂_le_1 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₁ (fun _ : PUnit => p ≫ f₁) (fun _ => j₁) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.1 PUnit.unit
  exact h1

lemma mapsAt₂_le_2 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₂ (fun _ : PUnit => p ≫ f₂) (fun _ => j₂) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.2 PUnit.unit
  exact h1

def MapsAt₂ (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n)))
    (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n)))
    (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))) : Prop :=
  ∀ (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι),
    res (mapsAt₂_le_1 w p j₁ j₂ jL) (b₁.s fun _ => j₁) * res (mapsAt₂_le_2 w p j₁ j₂ jL) (b₂.s fun _ => j₂) =
      (pullU p _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL))) ^ n * res (mapsAt₂_le_a w p j₁ j₂ jL) (a.s fun _ => jL)

end MapsAt

structure IsSumPolAV {S : Scheme.{0}} (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A) : Prop where
  hom₁ : IsMonHom a₁
  hom₂ : IsMonHom a₂
  lim : IsIso (lift a₁ a₂)
  w : ∃ w : LB.Iso P.L (extLB P₁.L P₂.L a₁.left a₂.left), w.IsGen

variable {R : Type} [CommRing R] [IsDomain R]

structure IsSumDeg (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X)
    (q₂ : D.X →+ D₂.X) : Prop where
  hom₁ : IsMonHom p₁
  hom₂ : IsMonHom p₂
  lim : IsIso (lift p₁ p₂)
  xsum : Function.Bijective (q₁.prod q₂)
  c_pr₁ : ∀ x, D.c x ≫ p₁ = D₁.c (q₁ x)
  c_pr₂ : ∀ x, D.c x ≫ p₂ = D₂.c (q₂ x)
  w : ∃ w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left), w.IsGen ∧
    (∃ b₁ b₂, MapsAt₂ w (eSec D.P.A) 1 D.rig b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ D₁.rig ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ D₂.rig) ∧
    ∀ x, ∃ b₁ b₂, MapsAt₂ w (D.xK x) (-1) (D.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ (D₁.psi (q₁ x)) ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ (D₂.psi (q₂ x))

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  intro E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a
  exact GlobalTheory.CechKS.isTangent_of_fibre (E := E) t U v hv x0 hU A m u hm hu a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaDown

theorem isThetaPt_of_map : ∀ (B : Scheme.{0}) [IsLocallyNoetherian B] (P : PolAV B) (K C : Type) [Field K] [Field C] (j : K →+* C) (s : Sp K ⟶ B) (x : Sp C ⟶ B) (hx : spMap j ≫ s = x) (k : ℕ) (J : Type) (p : J → (Over.mk s ⟶ P.A)) (w : J → K), (∀ i, p i ^ k ^ 2 = 1) → IsThetaPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (j (w i))) → IsThetaPt P k p (fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (w i)) := by
  intro B _ P K C _ _ j s x hx k J p w hp H
  have h₁ : Laws := GlobalTheory.firstFiveLaws.1
  have h₂ : Laws2 := GlobalTheory.firstFiveLaws.2.1
  have hk : Odd k := H.1
  let eC : Γ(Sp C, ⊤) ≃+* C := (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv
  have hkC : (k : C) ≠ 0 := by
    have := H.2.1.map eC.toRingHom
    rw [map_natCast] at this
    exact this.ne_zero
  have hkK : IsUnit (k : K) := IsUnit.mk0 _ fun h0 => hkC (by rw [← map_natCast j, h0, map_zero])
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local h₁ h₂ P s hk hkK p hp
  have hC := GlobalTheory.Ex.Specialise.isThetaPt_map h₂ P j hx hw₀
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := eC.symm.isLocalRing
  obtain ⟨u, hu⟩ := GlobalTheory.ThetaUniq.exists_unit_over h₁.globalFns P hk
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x hC) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x H)
  set c : C := eC (u : Γ((Over.mk x).left, ⊤)) with hcdef
  have hc : ∀ i, j (w i) = c * j (w₀ i) := fun i => by
    have q := (congrArg eC (hu i)).trans (map_mul eC _ _)
    exact (eC.apply_symm_apply (j (w i))).symm.trans (q.trans (congrArg (_ * ·) (eC.apply_symm_apply (j (w₀ i)))))
  have hu0 : c ≠ 0 := fun h0 => (u.isUnit.map eC.toRingHom).ne_zero h0
  by_cases hz : ∀ i, w₀ i = 0
  · have e : w = w₀ := funext fun i => j.injective (by rw [hc, hz, map_zero, MulZeroClass.mul_zero])
    subst e
    exact hw₀
  · push_neg at hz
    obtain ⟨i₀, hi₀⟩ := hz
    have hd : j (w i₀ / w₀ i₀) = c := by
      rw [map_div₀, hc, mul_div_assoc, div_self ((map_ne_zero j).2 hi₀), _root_.mul_one]
    have hd0 : w i₀ / w₀ i₀ ≠ 0 := fun h0 => hu0 (by rw [← hd, h0, map_zero])
    have e : ∀ i, w i = (w i₀ / w₀ i₀) * w₀ i := fun i => j.injective (by rw [map_mul, hd, hc])
    have := GlobalTheory.Ex.Specialise.isThetaPt_mul P hw₀ hd0
    convert this using 2 with i
    rw [e i]

end GlobalTheory.Mum.ThetaDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOverOpenPartSubsetAbelianLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.KerAb

theorem subset_abLocus {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Zh : ZHOut ρ M U₀ EE) (hO : S.Over₀ M U₀) :
    (U₀ : Set M.Z) ⊆ abLocus Zh.G := by
  intro z hz
  rw [Zh.ab]
  show S.TT M z = ⊥
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  have h1 : S.perp ⊥ = ⊤ := by
    refine top_unique fun a _ h hh => ?_
    rw [AddSubgroup.mem_bot.mp hh]
    simp [ZH.eStd]
  rw [ZH.ThetaSys.TT, ZH.ThetaSys.HH, hO.supI_eq hz, S.supp, ← h1, hpp]

theorem ker_mem_and_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∀ (R : Type) [CommRing R] (q : Sp R ⟶ M.Z) (V' : Type) [CommRing V'] [IsDomain V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → spMap g' ≫ q = spMap h ≫ ξ → (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ q ⁻¹' (U₀ : Set M.Z) ∧ (U₀ : Set M.Z) ⊆ abLocus out.G := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm T ξ hξ R _ q V' _ _ h g' hh hq
  refine ⟨?_, subset_abLocus out hAdm.1⟩
  obtain ⟨ξ₀, h₀, -⟩ := hξ
  let w : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  let v : Sp (FractionRing T.V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing T.V))
  have e₁ : spMap g' w = (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g').symm
  have e₂ : spMap h w = jK T.V v := by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap h ⊥ = Ideal.comap (algebraMap T.V (FractionRing T.V)) ⊥
    rw [← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hh,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective T.V (FractionRing T.V))]
  have e₃ : q (spMap g' w) = U₀.ι (ξ₀ v) := by
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply, e₂, ← Scheme.Hom.comp_apply, ← h₀, Scheme.Hom.comp_apply]
  rw [← e₁]
  show q (spMap g' w) ∈ U₀
  rw [e₃]
  exact (ξ₀ v).2

end GlobalTheory.UPoinc.KerAb
end

