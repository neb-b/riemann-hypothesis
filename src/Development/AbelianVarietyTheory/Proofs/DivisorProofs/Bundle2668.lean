module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesBaseDatumAdelicFormMultiple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionProperties
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.NVRules

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem unitAt_zpow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℤ) : UnitAt x (f ^ n) := by
  have hm : Units.mk0 f h.ne_zero ∈ unitsAt x := by
    change UnitAt x ((Units.mk0 f h.ne_zero : X.functionFieldˣ) : X.functionField)
    rwa [Units.val_mk0]
  have := zpow_mem hm n
  change UnitAt x (((Units.mk0 f h.ne_zero ^ n : X.functionFieldˣ)) : X.functionField) at this
  rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0] at this

theorem regAt_pow {x : X} {f : X.functionField} (h : RegAt x f) (n : ℕ) : RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_of_pow {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n)
    (h : UnitAt x (f ^ n)) : UnitAt x f := by
  have hne : f ≠ 0 := fun e => h.ne_zero (by rw [e, zero_pow (by omega)])
  refine (unitAt_iff hne).2 ⟨hf, ?_⟩
  have e : f⁻¹ = f ^ (n - 1) * (f ^ n)⁻¹ := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), one_mul]
  rw [e]
  exact (regAt_pow hf _).mul h.inv.regAt

theorem unitAt_pow_iff {x : X} {f : X.functionField} (hf : RegAt x f) {n : ℕ} (hn : 1 ≤ n) :
    UnitAt x (f ^ n) ↔ UnitAt x f :=
  ⟨unitAt_of_pow hf hn, fun h => by simpa using unitAt_zpow h (n : ℤ)⟩

theorem unitAt_ratio {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {x : X} {i j : L.ι}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : UnitAt x ((r i : X.functionField) / r j) := by
  have h := gen_mem (memInf hi hj)
  rw [hr i j h, mul_div_cancel_right₀ _ (Units.ne_zero _)]
  exact unitAt_fnOf (memInf hi hj) h (L.g i j)

theorem loc_eq_mul (P : Pair p) (a b : ℤ) (f : X.functionField) (i i' : P.L.B.ι) (j j' : P.A.B.ι) :
    P.loc a b f i j = P.loc a b f i' j' *
      (((P.r i : X.functionField) / P.r i') ^ a * ((P.r' j : X.functionField) / P.r' j') ^ b) := by
  have h1 : ((P.r i' : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j' : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc, div_zpow]
  field_simp

theorem unitAt_loc_of (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i i' : P.L.B.ι} {j j' : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hi' : x ∈ P.L.B.U i') (hj : x ∈ P.A.B.U j) (hj' : x ∈ P.A.B.U j')
    (h : UnitAt x (P.loc a b f i' j')) : UnitAt x (P.loc a b f i j) := by
  rw [loc_eq_mul P a b f i i' j j']
  exact h.mul ((unitAt_zpow (unitAt_ratio P.hr hi hi') a).mul (unitAt_zpow (unitAt_ratio P.hr' hj hj') b))

theorem mem_NV_iff (P : Pair p) (a b : ℤ) (f : X.functionField) {x : X} {i : P.L.B.ι} {j : P.A.B.ι}
    (hi : x ∈ P.L.B.U i) (hj : x ∈ P.A.B.U j) : x ∈ NV P a b f ↔ UnitAt x (P.loc a b f i j) :=
  ⟨fun h => h i j hi hj, fun h _ _ hi' hj' => unitAt_loc_of P a b f hi' hi hj' hj h⟩

theorem div_eq_loc_div (P : Pair p) (a b : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    f / g = P.loc a b f i j / P.loc a b g i j := by
  have h1 : ((P.r i : X.functionField)) ^ a ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have h2 : ((P.r' j : X.functionField)) ^ b ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  simp only [Pair.loc]
  rw [mul_assoc f, mul_assoc g, mul_div_mul_right _ _ (mul_ne_zero h1 h2)]

theorem loc_pow (P : Pair p) (a b : ℤ) (g : X.functionField) (n : ℕ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (n * a) (n * b) (g ^ n) i j = P.loc a b g i j ^ n := by
  simp only [Pair.loc, mul_pow]
  rw [mul_comm (n : ℤ) a, mul_comm (n : ℤ) b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

end GlobalTheory.HSAmp.NVRules


open GlobalTheory.HSAmp.NVRules in
theorem GlobalTheory.HSAmp.nv_rules : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) ∧ (genericPoint X ∈ NV P a b g ↔ g ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → NV P (n * a) (n * b) (g ^ n) = NV P a b g) ∧ (∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g))) ∧ ∀ f ∈ P.H a b, ∀ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ NV P a b g → P.nu a b σ y f = ‖ratVal (f / g) y‖ * P.nu a b σ y g ∧ 0 < P.nu a b σ y g := by
  intro k _ X _ p P a b g hg
  have cL := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.L.isLB x
  have cA := fun x : X => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart P.A.isLB x
  have h4 : ∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g)) := by
    intro f hf z hz
    obtain ⟨i, hi⟩ := cL z
    obtain ⟨j, hj⟩ := cA z
    have hu := (mem_NV_iff P a b g hi hj).1 hz
    rw [div_eq_loc_div P a b f g i j, mem_NV_iff P a b f hi hj]
    refine ⟨(hf z i j hi hj).mul hu.inv.regAt, fun h => h.mul hu.inv, fun h => ?_⟩
    have := h.mul hu
    rwa [div_mul_cancel₀ _ hu.ne_zero] at this
  refine ⟨?_, ?_, ?_, h4, ?_⟩
  · refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    obtain ⟨V, hV, hVu⟩ := ((mem_NV_iff P a b g hi hj).1 hx).exists_nhds
    refine ⟨((V ⊓ P.L.B.U i ⊓ P.A.B.U j : X.Opens) : Set X), fun y hy => ?_, Opens.isOpen _, ⟨⟨hV, hi⟩, hj⟩⟩
    obtain ⟨⟨hyV, hyi⟩, hyj⟩ := hy
    exact (mem_NV_iff P a b g hyi hyj).2 (hVu y hyV)
  · obtain ⟨i, hi⟩ := cL (genericPoint X)
    obtain ⟨j, hj⟩ := cA (genericPoint X)
    rw [mem_NV_iff P a b g hi hj]
    refine ⟨fun h e => h.ne_zero (by rw [e]; simp [Pair.loc]), fun h => unitAt_genericPoint ?_⟩
    simp only [Pair.loc]
    exact mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (Units.ne_zero _))) (zpow_ne_zero _ (Units.ne_zero _))
  · intro n hn
    ext x
    obtain ⟨i, hi⟩ := cL x
    obtain ⟨j, hj⟩ := cA x
    rw [mem_NV_iff P _ _ _ hi hj, mem_NV_iff P a b g hi hj, loc_pow]
    exact unitAt_pow_iff (hg x i j hi hj) hn
  · intro f hf σ y hy
    have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    have hu := (mem_NV_iff P a b g hi hj).1 hy
    have hq := (h4 f hf _ hy).1
    have e : P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
        f / g * P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
      rw [div_eq_loc_div P a b f g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y), div_mul_cancel₀ _ hu.ne_zero]
    refine ⟨?_, ?_⟩
    · rw [Pair.nu, Pair.nu, e, ratVal_mul hq hu.regAt, norm_mul, mul_assoc]
    · rw [Pair.nu]
      exact mul_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) (Real.exp_pos _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointEqFinrankQuotients
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section

open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace

namespace GlobalTheory.GenericResidueDegree

theorem residue_generic_bijective (X : Scheme.{0}) [IsIntegral X] :
    Function.Bijective (X.residue (genericPoint X)).hom :=
  ⟨RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom, X.residue_surjective _⟩

theorem residueDegree_eq_finrank_closure {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (h : genericPoint X ∈ π ⁻¹ᵁ U) (E : Subfield X.functionField)
    (hE : E = Subfield.closure (Set.range fun s : Γ(Y, U) =>
      (X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) : X.functionField))) :
    π.residueDegree (genericPoint X) = Module.finrank E X.functionField := by
  let e : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom (residue_generic_bijective X)
  let ψ : Y.residueField (π (genericPoint X)) →+* X.functionField :=
    e.symm.toRingHom.comp (π.residueFieldMap (genericPoint X)).hom
  have hψ : ∀ a : Y.presheaf.stalk (π (genericPoint X)),
      ψ (Y.residue _ a) = π.stalkMap (genericPoint X) a := fun a => by
    apply e.injective
    have := congrArg (fun φ => φ.hom a) (Scheme.residue_residueFieldMap π (genericPoint X))
    exact (e.apply_symm_apply _).trans this
  have hg : ∀ s : Γ(Y, U), ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) =
      X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) := fun s => by
    rw [hψ]
    exact π.germ_stalkMap_apply U _ h s
  have hr : ψ.fieldRange = E := by
    subst hE
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := Y.residue_surjective _ b
      letI := Y.presheaf.algebra_section_stalk (⟨π (genericPoint X), h⟩ : U)
      have hl := hU.isLocalization_stalk ⟨π (genericPoint X), h⟩
      obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (hU.primeIdealOf ⟨π (genericPoint X), h⟩).asIdeal.primeCompl a
      have hu := IsLocalization.map_units (Y.presheaf.stalk (π (genericPoint X))) t
      have h1 : ψ (Y.residue _ a) * ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) =
          ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) := by
        rw [← map_mul, ← map_mul]
        exact congrArg (fun z => ψ (Y.residue _ z)) hst
      have h2 : ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) ≠ 0 :=
        ((hu.map (Y.residue _).hom).map ψ).ne_zero
      rw [eq_div_of_mul_eq h2 h1, hg, hg]
      exact Subfield.div_mem _ (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
    · rintro _ ⟨s, rfl⟩
      exact ⟨_, hg s⟩
  clear hE
  subst hr
  letI := (π.residueFieldMap (genericPoint X)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  refine Algebra.finrank_eq_of_equiv_equiv ψ.rangeRestrictFieldEquiv e.symm ?_
  ext a
  rfl

theorem residueDegree_eq_finrank_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → π (genericPoint X) = genericPoint (PSpace k D) → π.residueDegree (genericPoint X) = Module.finrank (Subfield.closure (Set.range (GlobalTheory.toFunctionField p) ∪ Set.range fun j : Fin D => x j.succ / x 0)) X.functionField := by
  intro k _ X _ p D _ π hπ x hx ⟨h, hj⟩ _
  refine residueDegree_eq_finrank_closure π _ (ProjSpace.isAffineOpen_chart k D 0) h _ ?_
  let g : Γ(X, π ⁻¹ᵁ ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h).hom
  have hc : ∀ a : k, g ((baseRingHom (π ≫ PSpace.str k D) (π ⁻¹ᵁ ProjSpace.chart k D 0)).hom a) =
      GlobalTheory.toFunctionField p a := fun a => by
    rw [hπ]
    exact X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) h
      (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a))
  have key : ∀ q : MvPolynomial (Fin (D + 1)) k,
      g (π.app _ (MvPolynomial.aeval (R := k) (ProjSpace.ratio k D 0) q)) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) q := fun q => by
    have e₁ := congrArg (fun t => g (t q))
      (ProjSpace.appLE_comp_aeval_ratio (φ := π) (i := 0) (hi := le_rfl))
    rw [Scheme.Hom.app_eq_appLE]
    refine e₁.trans ?_
    rw [MvPolynomial.map_eval₂Hom]
    congr 2
    · exact RingHom.ext hc
    · exact funext hj
  refine le_antisymm (Subfield.closure_le.2 ?_) (Subfield.closure_le.2 ?_)
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.C a)).trans (MvPolynomial.eval₂Hom_C _ _ _)⟩
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.X j.succ)).trans (MvPolynomial.eval₂Hom_X' _ _ _)⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨q, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 s
    refine Set.mem_of_eq_of_mem (key q) ?_
    rw [SetLike.mem_coe]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add q q' h1 h2 =>
      rw [map_add (f := _)]
      exact Subfield.add_mem _ h1 h2
    | mul_X q j h1 =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine Subfield.mul_mem _ h1 ?_
      refine Fin.cases ?_ (fun j => Subfield.subset_closure (Or.inr ⟨j, rfl⟩)) j
      rw [div_self hx]
      exact Subfield.one_mem _

end GlobalTheory.GenericResidueDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigAlongBox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open GlobalTheory.UnifPullRig

theorem rigAlong_box : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {S S₀ : Scheme.{0}} (u : S ⟶ T) (u₁ : S ⟶ T₁) (u₂ : S ⟶ T₂) (s : S ⟶ S₀) {eG : S₀ ⟶ G} {eG₁ : S₀ ⟶ G₁} {eG₂ : S₀ ⟶ G₂} {eB : S₀ ⟶ B} {eB₁ : S₀ ⟶ B₁} {eB₂ : S₀ ⟶ B₂} (rL : LB.Gen (L.pull eG)) (rL₁ : LB.Gen (L₁.pull eG₁)) (rL₂ : LB.Gen (L₂.pull eG₂)) (rM : LB.Gen (M.pull eB)) (rM₁ : LB.Gen (M₁.pull eB₁)) (rM₂ : LB.Gen (M₂.pull eB₂)), u ≫ h₁ = u₁ → u ≫ h₂ = u₂ → u ≫ f = s ≫ eG → u ≫ p = s ≫ eB → u₁ ≫ f₁ = s ≫ eG₁ → u₁ ≫ p₁ = s ≫ eB₁ → u₂ ≫ f₂ = s ≫ eG₂ → u₂ ≫ p₂ = s ≫ eB₂ → IsBoxGen wL (𝟙 S₀) (𝟙 S₀) rL rL₁ rL₂ → IsBoxGen wM (𝟙 S₀) (𝟙 S₀) rM rM₁ rM₂ → GlobalTheory.UnifPullRig.RigAlong we₁ u₁ s rL₁ rM₁ → GlobalTheory.UnifPullRig.RigAlong we₂ u₂ s rL₂ rM₂ → GlobalTheory.UnifPullRig.RigAlong we u s rL rM := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂
    hL hL₁ hL₂ hpb₁ hpb₂ hfg₁ hfg₂ we hQ S S₀ u u₁ u₂ s eG eG₁ eG₂ eB eB₁ eB₂ rL rL₁ rL₂ rM rM₁ rM₂ hu₁ hu₂
    hf hp hf₁ hp₁ hf₂ hp₂ bL bM H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => s ≫ eB) (fun _ => qM ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eB) (x := s y)).1 (a₃ hy))
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => s ≫ eG) (fun _ => qL ⟨⟩)
    (fun _ _ _ => rfl) (fun _ => (mem_pull (F := eG) (x := s y)).1 (a₂ hy))
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at hL₂ y
  have m₁ : (u ≫ p) ≫ b₁ = s ≫ eB₁ := by rw [Category.assoc, hpb₁, ← Category.assoc, hu₁, hp₁]
  have m₂ : (u ≫ p) ≫ b₂ = s ≫ eB₂ := by rw [Category.assoc, hpb₂, ← Category.assoc, hu₂, hp₂]
  have n₁ : (u ≫ f) ≫ g₁ = s ≫ eG₁ := by rw [Category.assoc, hfg₁, ← Category.assoc, hu₁, hf₁]
  have n₂ : (u ≫ f) ≫ g₂ = s ≫ eG₂ := by rw [Category.assoc, hfg₂, ← Category.assoc, hu₂, hf₂]
  have Q := hQ S u y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  rw [m₁, m₂, n₁, n₂, hu₁, hu₂, hp, hf] at Q
  have HM := bM S s y J₁ J₂ J hJ₁ hJ₂ hJ
  have HL := bL S s y N₁ N₂ N hN₁ hN₂ hN
  simp only [Category.comp_id] at HM HL
  have E₁ := H₁.stalk hf₁ hp₁ (𝟙 S) y (J₁ (s ≫ eB₁)) (N₁ (s ≫ eG₁))
    ((pt_of_eq hp₁ y).symm ▸ hJ₁ (s ≫ eB₁)) ((pt_of_eq hf₁ y).symm ▸ hN₁ (s ≫ eG₁))
  have E₂ := H₂.stalk hf₂ hp₂ (𝟙 S) y (J₂ (s ≫ eB₂)) (N₂ (s ≫ eG₂))
    ((pt_of_eq hp₂ y).symm ▸ hJ₂ (s ≫ eB₂)) ((pt_of_eq hf₂ y).symm ▸ hN₂ (s ≫ eG₂))
  simp only [Category.id_comp] at E₁ E₂
  have key := rel_alg (K := PUnit) (fun _ => 1) (fun _ => om wM y J₁ J₂ J (s ≫ eB))
    (fun _ => om wL y N₁ N₂ N (s ≫ eG)) (fun _ => gw we u y (J (s ≫ eB)) (fun _ => N (s ≫ eG)))
    (fun _ => gw we₁ u₁ y (J₁ (s ≫ eB₁)) (fun _ => N₁ (s ≫ eG₁)))
    (fun _ => gw we₂ u₂ y (J₂ (s ≫ eB₂)) (fun _ => N₂ (s ≫ eG₂))) (fun _ => Q) HM HL
    (by rw [Fintype.prod_unique, zpow_one]; exact E₁.symm) (by rw [Fintype.prod_unique, zpow_one]; exact E₂.symm)
  rw [Fintype.prod_unique, zpow_one, val_of rM s y J qM (fun k => eJ k), val_of rL s y N qL (fun k => eN k),
    eJ ⟨⟩, eN ⟨⟩] at key
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  simp only [Category.id_comp]
  exact key.symm

end GlobalTheory.ProdUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem loc_continuousOn_holo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  intro k _ X _ p P a b σ f hf i j
  have key : ∀ y ∈ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j), ∃ (W : X.Opens) (hW : genericPoint X ∈ W)
      (g : Γ(X, W)), y ∈ ptsIn p σ W ∧ P.loc a b f i j = fnOf W hW g := by
    intro y hy
    have hr : RegAt (under y) (P.loc a b f i j) := hf _ i j (mem_ptsIn.1 hy.1) (mem_ptsIn.1 hy.2)
    obtain ⟨W, hx, g, e⟩ := hr.exists_fnOf
    exact ⟨W, gen_mem hx, g, mem_ptsIn.2 hx, e.symm⟩
  refine ⟨fun y hy => ?_, fun D c => ?_⟩
  · obtain ⟨W, hW, g, hy', e⟩ := key y hy
    have hc : ContinuousAt (ratVal (q := p) (σ := σ) (P.loc a b f i j)) y := by
      refine ((continuousOn_ev (p := p) (σ := σ) g).continuousAt ((isOpen_ptsIn W).mem_nhds hy')).congr ?_
      filter_upwards [(isOpen_ptsIn W).mem_nhds hy'] with z hz
      rw [e, ratVal_fnOf hz]
    exact hc.continuousWithinAt
  · intro v hv
    obtain ⟨W, hW, g, hy', e⟩ := key _ hv.2
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W) :=
      c.e.isOpen_inter_preimage_symm (isOpen_ptsIn W)
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W := ⟨hv.1, hy'⟩
    have hd := (c.holo W g).differentiableAt (hO.mem_nhds hm)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hO.mem_nhds hm] with w hw
    rw [e, ratVal_fnOf hw.2]
    rfl

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericPointIntegralSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_generic_point_integral_section : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp R)) ⟶ G) (l : FractionRing R) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), IntTerm.Ext U x h → (∀ (z : (TF (R := R) (FractionRing R)).left) (JA : ((TF (R := R) (FractionRing R)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := R) (FractionRing R)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := R) (FractionRing R)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := R) (FractionRing R)) ≫ h).left) (fun _ => JA x.left)).val * (val (Z := (TF (R := R) (FractionRing R)).left) e (𝟙 _) z JA).val = GlobalTheory.UT.cst (FractionRing R) z l * (val f (toUnit (TF (R := R) (FractionRing R))).left z JG).val) → ∀ (k : ℕ) (s : SecA A (FractionRing R) k) (σ' : U.SecGF (FractionRing R) k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) (FractionRing R)) A.A).left (U.genF (FractionRing R)).left s (UnifPre.gFK (G := G) (FractionRing R)) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → FractionRing R) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) (FractionRing R)) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) (FractionRing R)) (fun i => scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) → ∀ xs : Fin n → R, (∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val) → ∀ v : FractionRing R, ValAt s x e v → v * l ^ k = ∑ i, c i * algebraMap R (FractionRing R) (xs i) := by
  first | exact @GlobalTheory.Poinc.IntEval.value_at_section | exact GlobalTheory.Poinc.IntEval.value_at_section | (intros; apply GlobalTheory.Poinc.IntEval.value_at_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointCongruentTermSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_integral_point_congruent_term_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1))) (e k : ℕ), GlobalTheory.Poinc.IntEval.TRel U h g.b f t e → ∀ (σ : H0 U.LG.L k) (fs : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt e k σ fs → ∀ x : R, (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval σ (r ≫ h.left) z J = Geo.Tor.cst r z x * (val f r z J ^ k).val) → ∀ a : D.toPre.X → R, (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → sval (fs α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) → ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed | exact GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed | (intros; apply GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalar
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp


open GlobalTheory.VolBr.NuEq in
theorem val_frame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ y f = θ * (ratVal (P.loc a b f i j) y * (Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
  intro k _ X _ p P a b σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have hL : CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG
  have hA : CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG'
  set gL := CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y with hgL
  set gA := CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y with hgA
  have hG : gL ^ a * gA ^ b ≠ 0 := mul_ne_zero (zpow_ne_zero _ hL) (zpow_ne_zero _ hA)
  have hGn : (‖gL ^ a * gA ^ b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hG)
  refine ⟨(‖gL ^ a * gA ^ b‖ : ℂ) / (gL ^ a * gA ^ b), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hG)]
  intro f hf
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have hrv : ratVal (P.loc a b f i j) y =
      gL ^ a * gA ^ b * ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y := by
    rw [hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
      ratVal_zpow' uG, ratVal_zpow' uG', eG, eG']
    rfl
  have c0 : 0 < ‖gL‖ := norm_pos_iff.2 hL
  have c0' : 0 < ‖gA‖ := norm_pos_iff.2 hA
  have hexp : Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) =
      ‖gL ^ a * gA ^ b‖⁻¹ * Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) := by
    rw [(P.L.φ σ).trans i _ y hi hi₀, (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_zpow, norm_zpow,
      ← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
      Real.log_pow, Real.log_pow, ← hgL, ← hgA, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [val, hrv, hexp]
  push_cast
  field_simp

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesBaseDatumAdelicFormMultipleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortSeries_baseDatum_adelicForm_multiple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → adForm R i (cuspTo hT.p fw i F₀) (fun ρ => w ρ) = D.what₂.embLL c • singleSeries R i ω φ' h ((O i).c0' y) w := by
  first | exact @GlobalTheory.ExactBase.short_series_base | exact GlobalTheory.ExactBase.short_series_base | (intros; apply GlobalTheory.ExactBase.short_series_base <;> assumption)
end

