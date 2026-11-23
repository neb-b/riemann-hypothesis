module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsLie
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem QLog.Chart.existsUnique_isLie : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ O E _ _ _ hF G d c f hf
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin d) (algebraMap O E)) := by
    intro s t h
    ext α
    have := congrArg (MvPowerSeries.coeff α) h
    simp only [MvPowerSeries.coeff_map] at this
    exact hF.inj this
  obtain ⟨hex, hcomp⟩ := GlobalTheory.QLog.defect_compat p O E hF G d c f hf
  choose s hs _ using fun n : ℕ => hex (p ^ n)
  have hadd := GlobalTheory.QLog.cobOne_ev_defect_dvd p O E hF G d c f hf
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.LieOfAdditive.existsUnique_lie_of_additive p O G (fun n => c.ev n (s n))
    (fun n => hadd n (s n) (hs n)) (fun n => hcomp n (s n) (s (n + 1)) (hs n) (hs (n + 1)))
  refine ⟨l, ⟨fun n => In.top_iff.2 ⟨s n, hs n⟩, ?_⟩, ?_⟩
  · intro n w φ t hφ ht
    have : t = s n := hinj (ht.trans (hs n).symm)
    subst this
    exact hl n w φ hφ
  · intro l' hl'
    exact huniq l' fun n w φ hφ => hl'.2 n w φ (s n) hφ (hs n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLift
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomLift

theorem eq_one_of_grpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'}
    (z : Over.mk (T.hom ≫ f) ⟶ G) (hz : z.left = (1 : T ⟶ G').left ≫ φ) : z = 1 := by
  have e := h.2 T 1 1 z z hz hz
  rw [_root_.mul_one, ← hz] at e
  exact _root_.mul_eq_left.1 (Over.OverMorphism.ext e)

theorem one_left {S : Scheme.{0}} (T G : Over S) [GrpObj G] :
    (1 : T ⟶ G).left = T.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  rfl

theorem one_eq_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
  rw [Hom.one_def, toUnit_unit, Category.id_comp]

theorem existsUnique_isMonHom_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left),
    IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme A → IsAbelianScheme B →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : A ⟶ B), i ≫ φ.left = f₀.left ≫ j → ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j := by
  intro R R₀ _ _ π hπ hnil A₀ B₀ _ _ A B _ _ i j hA hB hAab hBab f₀ _ φ hφ
  obtain ⟨z, hz⟩ : ∃ z : Over.mk (A₀.hom ≫ spMap π) ⟶ A, z.left = i := ⟨Over.homMk i hA.1.w, rfl⟩
  have hzl : ∀ g : A ⟶ B, (z ≫ g).left = i ≫ g.left := fun g => by rw [Over.comp_left, hz]
  have hu : (1 : A₀ ⟶ A₀).left ≫ i = (1 : Over.mk (A₀.hom ≫ spMap π) ⟶ A).left := by
    have := eq_one_of_grpPullback hA (T := A₀) (Over.homMk ((1 : A₀ ⟶ A₀).left ≫ i) (by
      change (_ ≫ i) ≫ A.hom = A₀.hom ≫ spMap π
      rw [Category.assoc, hA.1.w, ← Category.assoc, Over.w])) rfl
    rw [← this]; rfl
  have h1 : (1 : A₀ ⟶ A₀) ≫ f₀ = 1 := by
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hc : z ≫ ((1 : A ⟶ A) ≫ φ) = 1 := by
    apply eq_one_of_grpPullback hB
    rw [← Category.assoc, comp_one, Over.comp_left, ← h1, Over.comp_left, Category.assoc, ← hφ,
      ← Category.assoc, hu]
  obtain ⟨f, hfdef⟩ : ∃ f : A ⟶ B, f = φ * ((1 : A ⟶ A) ≫ φ)⁻¹ := ⟨_, rfl⟩
  have hηf : η[A] ≫ f = η[B] := by
    have e : η[A] ≫ ((1 : A ⟶ A) ≫ φ) = η[A] ≫ φ := by
      rw [← Category.assoc, comp_one, one_eq_unit]
    rw [hfdef, comp_mul, GrpObj.comp_inv, e, mul_inv_cancel, one_eq_unit]
  have hf : IsMonHom f := GlobalTheory.rigidity_holds (Sp R) A B hAab hBab f hηf
  have hfl : i ≫ f.left = f₀.left ≫ j := by
    rw [← hzl, hfdef, comp_mul, GrpObj.comp_inv, hc, inv_one, _root_.mul_one, hzl, hφ]
  refine ⟨f, ⟨hf, hfl⟩, fun g ⟨hg, hgl⟩ => ?_⟩
  obtain ⟨d, hddef⟩ : ∃ d : A ⟶ B, d = g * f⁻¹ := ⟨_, rfl⟩
  have hzg : z ≫ g = z ≫ f := Over.OverMorphism.ext (by rw [hzl, hzl, hgl, hfl])
  have hzd : z ≫ d = 1 := by rw [hddef, comp_mul, GrpObj.comp_inv, hzg, mul_inv_cancel]
  have hηd : η[A] ≫ d = η[B] := by
    rw [hddef, comp_mul, GrpObj.comp_inv, hηf, IsMonHom.one_hom, mul_inv_cancel, one_eq_unit]
  have key := GlobalTheory.Rigidity.eq_comp_section R R₀ π hπ hnil A B A₀ i hA.1 hAab.smooth hAab.proper
    hAab.geomConnected (η[A] : 𝟙_ (Over (Sp R)) ⟶ A).left (Over.w _) d
    (spMap π ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left) (by
      rw [← hzl, hzd, one_left]
      exact Category.assoc _ _ _)
  have hd : d = 1 := by
    apply Over.OverMorphism.ext
    rw [key, one_left, ← hηd]
    rfl
  rw [hddef] at hd
  exact mul_inv_eq_one.1 hd

end GlobalTheory.HomLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFree
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumSurj

theorem unitSec_mul' {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec
  exact map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_surj {U : Scheme.{0}} (b : Sec Gm U) : ∃ u : (Γ(U, ⊤))ˣ, unitSec u = b := by
  obtain ⟨y, hy⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective U).2 b
  exact ⟨Additive.toMul y.down, hy⟩

theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := by
  intro U ⟨x⟩
  have h1 : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using h1.map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom

end GlobalTheory.EtC.KumSurj


open GlobalTheory.EtC.KumSurj in
theorem GlobalTheory.EtC.kum_surjective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  intro q _ A _ hq hp x
  obtain ⟨κ, hκ, bd, hbd, hex, ⟨s, hs⟩, hlast⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have hE : Inv q (sp A) := inv_sp q A hq
  have hqX : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨_, h2, h3⟩ := hex (sp A) hE 0
  obtain ⟨_, _, _, hpc, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  obtain ⟨hpid, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  set y := HK.post ℤ ((chains ℤ).obj (sp A)) κ (0 + 1) (restrH (Int.castRingHom (ZMod q)) (sp A) (tw q 1) (0 + 1) x) with hy
  have hqy : (q : ℤ) • y = 0 := by
    have := (h3 y).2 ⟨x, rfl⟩
    rw [hpc, hpid] at this
    exact this
  have hy0 : y = 0 := by
    obtain ⟨e⟩ := GlobalTheory.T.etale_descent_picard_group A
    have h1 : (q : ℤ) • e y = 0 := by rw [← map_zsmul, hqy, map_zero]
    have h2' : (Additive.toMul (e y)) ^ q = 1 := by
      have := congrArg Additive.toMul h1
      rw [natCast_zsmul, toMul_nsmul] at this
      exact this
    have := hp _ h2'
    apply e.injective
    rw [map_zero]
    exact congrArg Additive.ofMul this
  obtain ⟨g, hg⟩ := (h2 x).1 hy0
  obtain ⟨-, hbij, hadd, -, -⟩ := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hbij.2 g
  obtain ⟨u, rfl⟩ := unitSec_surj b
  have hsu := hs _ u hqX
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨u, by rw [← hg, hsu, one_smul]⟩
  · refine ⟨u⁻¹, ?_⟩
    have hsi := hs _ u⁻¹ hqX
    have hsum : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u⁻¹)) +
        bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
      rw [← map_add (f := _), ← hadd, ← unitSec_mul', inv_mul_cancel]
      have h0 : unitSec (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) = 0 := by
        have := unitSec_mul' (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1
        rw [mul_one] at this
        exact (left_eq_add.1 this)
      have h00 : secClass Gm (0 : Sec Gm (Spec (CommRingCat.of A))) = 0 := by
        have := hadd 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      rw [h0, h00, map_zero]
    rw [hsi, hsu, Units.neg_smul, Units.neg_smul, one_smul, one_smul] at hsum
    rw [← hg, hsu, Units.neg_smul, one_smul]
    rw [← neg_add] at hsum
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.1 hsum)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivative
section
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.KFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem cptRep_lie (k : Kinf E a) (X : Lie E a) (ψ : Sm E a) :
    cptRep E a k (lie E a X ψ) =
      lie E a (toL ((Unitary.toUnits k).val * Matrix.of X * (Unitary.toUnits k)⁻¹.val)) (cptRep E a k ψ) := by
  set y : GL (Fin a) (Cinf E) := Unitary.toUnits k with hy
  set Z : Lie E a := toL (y.val * Matrix.of X * y⁻¹.val) with hZ
  refine Subtype.ext (funext fun g => ?_)
  change lieD X ψ.1 (g * infGL E a y) = lieD Z (fun x => ψ.1 (x * infGL E a y)) g
  rw [← chart_val (lieD X ψ.1) g y, chart_lieD ψ.2 X g (val_mem_invSet y), lieD, chart_rt_inf]
  have e1 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul (Matrix.of (toL y.val))
  rw [fderiv_comp _ (by rw [e1]; exact (contDiffAt_chart ψ.2 g (val_mem_invSet y)).differentiableAt (by simp))
    (rmul (toL y.val)).differentiableAt, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, e1]
  congr 1
  change (y.val : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of X = (y.val * Matrix.of X * y⁻¹.val) * (y.val : Matrix (Fin a) (Fin a) (Cinf E))
  rw [mul_assoc, Units.inv_mul, mul_one]

theorem kfin_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Lie E a) (φ : Sm E a)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k (lie E a X φ))) := by
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  let b := Module.finBasis ℝ (Lie E a)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, V.map (lie E a (b i))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe]
  change cptRep E a k (lie E a X φ) ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cptRep_lie, ← b.sum_repr (toL _), map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem i
    (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)))

end GlobalTheory.CuspRep.KFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm

namespace GlobalTheory.CompactHarm

variable {m k l : ℕ}

theorem omE_pp {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = true) (hv : linePos v = true)
    (P : Pol p q r s) :
    omE u v P = X u * pderiv v P + (if u = v then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, hu, hv, if_true]
  split_ifs <;> simp

theorem omE_nn {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (P : Pol p q r s) :
    omE u v P = -(X v * pderiv u P) - (if u = v then (1 / 2 : ℂ) else 0) • P := by
  have : omE u v P = -(pderiv u (X v * P)) + (if u = v then (1 / 2 : ℂ) else 0) • P := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, pderiv_X_mul']
  split_ifs
  · module
  · simp

end GlobalTheory.CompactHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockLoweringPartEqSubFockOperators
section
noncomputable section
namespace GlobalTheory.FockLowDiff
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

def ixSign {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal ixSign := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, ixSign, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem omAct_kron_diagonal {p q r s : ℕ} (Z : Mat p q) (t : Ix r s → ℂ) (P : Pol p q r s) :
    omAct p q r s (Matrix.kroneckerMap (· * ·) Z (Matrix.diagonal t)) P =
      ∑ a, ∑ b, ∑ c, (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P := by
  rw [omAct_apply, Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (f := fun b c => (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P),
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro d _ hd
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hd)]
  · simp

theorem lowering_eq_diff : ∀ (p q r s : ℕ) (Z : Mat p q), IsPC Z → ∀ P : Pol p q r s, omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)) P - omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q * Z) (Jm r s)) P = (2 : ℂ) • minusPart (fockAct1 p q r s Z) P := by
  intro p q r s Z hZ P
  rw [((GlobalTheory.FockParts.explicit_parts p q r s).1 Z hZ P).2, Jm_eq_diagonal, Jm_eq_diagonal,
    ← Matrix.diagonal_one, omAct_kron_diagonal, omAct_kron_diagonal, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.diagonal_mul, ← sub_smul]
  by_cases hab : sameBlock a b
  · simp [hZ a b hab]
  · rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [sameBlock] at hab <;>
      simp [ixSign, linePos, omE, raiB, lowB, two_smul, add_smul, add_comm]

end GlobalTheory.FockLowDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeLower
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.SchurIrreducible (IrrGK)
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts (delta wtK wtExt wtH IsLowestType IsKIntw)
open GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors (Place eulerProd dPart quadSign SatakeBound)
open scoped TensorProduct

namespace GlobalTheory.BlockSizes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rowsP (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) : ℕ := ⌊DV.aPlusQ D j τ i⌋₊

def rowsM (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) : ℕ :=
  ⌊DV.aMinusQ D j τ ((D.R.sigW j).2 - 1 - i)⌋₊

variable {D : D7} (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

def WindowsLe (L : SizeData₂ D) : Prop := L.etaSz ≤ L.sc.b ∧ L.Sc ≤ L.sc.b

end GlobalTheory.BlockSizes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbedding
section
open NumberField IsDedekindDomain IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

set_option linter.style.haveILetI false

namespace GlobalTheory.FrobEmb

theorem exists_frob_all (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (hc : ∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) (p : ℕ) (hp : p.Prime) :
    ∃ σ : E ≃ₐ[ℚ] E, ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨σ, fun Q _ _ => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have := hσ.conj t
  rwa [hc t σ, mul_inv_cancel_right] at this

theorem isArithFrobAt_frobG (D : D7) (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : IsArithFrobAt ℤ (D.host.sigmaOf (frobG D p)) P := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have h : ∃ g : D.R.GG, ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P := by
    obtain ⟨σ, hσ⟩ := exists_frob_all D.host.E (fun a b =>
      (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])) p hp
    obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
    have hg' : D.host.sigmaOf g = σ := hg
    exact ⟨g, hg' ▸ hσ⟩
  unfold frobG
  rw [dite_eq_left h]
  exact h.choose_spec P

end GlobalTheory.FrobEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPeriodsNaturalAlongCoveredMorphism
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isPeriod_pull1_eq_comap : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂), X₁.IsSeparated → X₂.IsSeparated → ∀ (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ p : Tot I₁ g₁, p.1 ∈ F₁.V → u₁.E p ≫ φ = u₂.E (b p.1, M p.2)) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), IsPeriod u₂ c per₂ → IsPeriod u₁ (m.pull1 c) per₁ → ∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l)) := by
  intro I₁ _ g₁ Λ₁ _ F₁ B₁ _ X₁ s₁ σ₁ I₂ _ g₂ Λ₂ _ F₂ B₂ _ X₂ s₂ σ₂ u₁ u₂ h₁ h₂ b hb hbV M A hτ β φ m hσ hE
    c per₂ per₁ hp₂ hp₁ l
  obtain ⟨K₁, K₂, κ, hR, hs₁, hs₂, hW, hle⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map u₁ u₂ b hb hbV M A hτ
  obtain ⟨r₁, hr₁, -⟩ := _root_.GlobalTheory.AnPer.exists_real_isFor u₁ h₁ K₁ hs₁
  obtain ⟨r₂, hr₂, -⟩ := _root_.GlobalTheory.AnPer.exists_real_isFor u₂ h₂ K₂ hs₂
  have hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k) := fun k p hp ↦
    ((hb _ (K₁.base k p hp)).comp analyticAt_fst).prod
      (((LinearMap.toContinuousLinearMap M).analyticAt p.2).comp analyticAt_snd)
  have hx : ∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ := by
    intro k
    refine _root_.GlobalTheory.AnPer.point_hol_ext_of_isSeparated (K₁.W k) h₂ _ _ fun p hp ↦ ?_
    have e : (Hol.ev p hp).toRingHom.comp (Hol.comap _ (hΦ k) (hW k)).toRingHom =
        (Hol.ev ((b p.1, M p.2) : Tot I₂ g₂) (hW k p hp)).toRingHom := by
      refine RingHom.ext fun f ↦ ?_
      change Hol.ev p hp (Hol.comap _ (hΦ k) (hW k) f) = Hol.ev _ (hW k p hp) f
      rw [Hol.ev_apply, Hol.ev_apply, Hol.fn_comap _ _ _ f hp]
    rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, e, hr₂ (κ k) _ (hW k p hp), hr₁ k p hp,
      hE p (K₁.base k p hp)]
  let per : Λ₁ →+ Hol F₁.V :=
    ((Hol.comap b hb hbV).toRingHom.toAddMonoidHom.comp per₂).comp A
  have key := _root_.GlobalTheory.AnPer.CmpCore.period_pullback_eq_of_chartMap_class_alt b hb hbV M A hτ K₁ K₂ κ hΦ hW hle r₁ r₂ β φ m hσ hx c per₂ per (fun _ ↦ rfl)
    (hp₂ K₂ r₂ hr₂)
  have := GlobalTheory.T.periodClass_injective_of_rich_charts K₁ hR per₁ per ((hp₁ K₁ r₁ hr₁).symm.trans key)
  rw [this]
  rfl

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechPer.isPer_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ x q' → q = q' := by
  intro A _ g L u x q q' hq hq'
  have h := ((_root_.GlobalTheory.CechPer.periods_linear A g L u).1 x x q q' hq hq').2
  rw [sub_self] at h
  exact sub_eq_zero.mp (_root_.GlobalTheory.CechPer.zero_periods_eq_zero A g L u _ h)
end

