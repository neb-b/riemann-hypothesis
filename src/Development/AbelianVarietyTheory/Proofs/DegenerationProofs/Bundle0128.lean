module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfCompatibleThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFOver
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcExt
open GlobalTheory.TorusExt

theorem exists_arcF_over : Laws → BrGtSt → BrWpSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), (∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ A : ArcF D R F, ∃ A' : ArcF D R F', A'.D₀ = A.D₀ ∧ A.Over f A' := by
  intro hL hGt hWp E _ _ _ H D R _ _ F F' _ _ _ _ _ _ _ f hf₀ A
  have hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext hf₀
  obtain ⟨J', hg, hJ₀⟩ := exists_gauge f A.D₀.P.isLB A.ν.good
  obtain ⟨N', ν', e₁, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R A.D₀ A.even A.bimult F' J' hg A.ν.th A.ν.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = A.ν.J ψ := e₁ ▸ hJ₀
  have G := (hGt R A.D₀ A.even A.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R A.D₀ A.even A.bimult F' N' ν').2.2.2.2
  let I := numHom f hf A.ν ν' hJ hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt A.D₀ F k) (z : F), WeilQkIs A.D₀ F k p p' z →
      WeilQkIs A.D₀ F' k (qkExt A.bimult f hf p) (qkExt A.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt A.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt A.bimult f hf p')
    have a := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq hr
    have a' := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq' hr'
    rw [hWp R A.D₀ A.even A.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (_root_.GlobalTheory.Ex.NumD.hom_transport F F' f A.N N' I).2.2.2.1 k q q' r r' a.1 a.2 a'.1 a'.2,
      (hWp R A.D₀ A.even A.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (a : D.La) => ((G' n).1 (qkExt A.bimult f hf (A.I.ev n a))).exists
  refine ⟨{ D₀ := A.D₀, oa := A.oa, even := A.even, bimult := A.bimult, w0 := A.w0, ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf A.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq', closed := inferInstance },
    rfl, I, rfl, fun _ _ => rfl, fun a y => ?_, fun n a _ => ?_⟩
  · obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
    obtain ⟨n, h₁, h₂⟩ := A.det τ
    have := A.D₀.P.isAb.smooth
    refine ⟨n, ?_, h₂.trans (by
      by_cases h : τ H.rt = A.ρ
      · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
      · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
    have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
        spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
      rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hf]
    rw [e]
    exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁
  · refine ν'.eX.injective ((eX_numHom f hf A.ν ν' hJ hth _).trans ?_)
    show A.ν.eX (A.ν.eX.symm _) = ν'.eX (ν'.eX.symm (a • ν'.eX (I.e y)))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, eX_numHom]
  · have h := numHom_qPt f hf A.bimult A.ν ν' hJ hth (A.hq n a) (hq' n a)
    exact ⟨q' n a, h.1, h.2, ⟨0, by simp, by simp⟩⟩

end GlobalTheory.ArcExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_cExt :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  intro W _ _ _ K _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπm : π ∈ IsLocalRing.maximalIdeal W := hmax ▸ Ideal.mem_span_singleton_self π
  obtain ⟨C, i1, i2, i3, i4, i5, h1, h2⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hπ.ne_zero hπm
      (r := 1 / 2) (by norm_num) (by norm_num)
  have hle : ∀ r : W, ‖algebraMap (FractionRing W) C (algebraMap W _ r)‖ ≤ 1 :=
    fun r => (h1 _).2 ⟨r, rfl⟩
  let g : K →ₐ[FractionRing W] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨C, i1, i2, i3, i4, i5, g.toRingHom, fun x => g.commutes x, hle, fun r hr => ?_⟩
  rw [hmax, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_mul, norm_mul, h2]
  have := hle s
  linarith

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDimensionalFieldDegenerationValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FiniteValues
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_finset_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (B : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType B.hom] (p : TF (R := R) F ⟶ B) :
    ∃ S : Finset F, ∀ K : IntermediateField (FractionRing R) F, (S : Set F) ⊆ K →
      ∃ l : TF (R := R) K ⟶ B, extMap (R := R) (algebraMap K F) rfl ≫ l = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p.left (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(B.left, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p.left := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p.left ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(B.left, U), Spec.map g = hU.fromSpec ≫ B.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf, Spec.map_comp]
      exact Over.w p)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(B.left, U) := g.hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType R Γ(B.left, U) from hft).out
  refine ⟨s.image f.hom, fun K hK => ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (s : Set Γ(B.left, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hK (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(B.left, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Over.homMk (Spec.map f' ≫ hU.fromSpec) ?_, Over.OverMorphism.ext ?_⟩
  · change (Spec.map f' ≫ hU.fromSpec) ≫ B.hom = Spec.map _ ≫ Spec.map _
    rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hV r
  · change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
    rw [← hf, ← Spec.map_comp_assoc]
    rfl

theorem exists_finite_field_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  intro R _ _ D F _ _ _ N ν T hT
  haveI := D.P.isAb.proper
  choose S hS using fun x : N.A => exists_finset_point D.P.A (ν.eA x)
  let s : Set F := ⋃ x ∈ T, (S x : Set F)
  haveI : Finite s := (hT.biUnion fun x _ => (S x).finite_toSet).to_subtype
  let K := IntermediateField.adjoin (FractionRing R) s
  let f : K →+* F := algebraMap K F
  have hf : f.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) F := rfl
  let Φ : (TF (R := R) K ⟶ D.P.A) →* N.A :=
    MonoidHom.mk' (fun x => ν.eA.symm (extMap f hf ≫ x)) fun x y => by rw [MonObj.comp_mul, map_mul]
  have hΦ : ∀ x, ν.eA (Φ x) = extMap f hf ≫ x := fun x => ν.eA.apply_symm_apply _
  let J : (Sp K ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (spMap f ≫ ψ)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ) := fun ψ z _ => by
    have h := ν.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F))
    rw [Subsingleton.elim (α := PrimeSpectrum K) z (spMap f (IsLocalRing.closedPoint F))]
    exact h
  have hJ' : ∀ ψ, ν.J (spMap f ≫ ψ) = J ψ := fun _ => rfl
  have hm : ∀ a : K, f a ∈ K := fun a => a.2
  have hv : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), vF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [vF_ext f hJ hJ']; exact hm _
  have hw : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Sec (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), sF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [sF_ext f hJ hJ']; exact hm _
  have hrig : rigVal ν ∈ K := by
    rw [rigVal, ← Over.w (extMap (R := R) f hf)]
    exact hv _ _
  refine ⟨K, Φ.range, IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun x hx => ?_, fun χ => ?_, ?_, ?_, ?_, fun χ => ?_⟩
  · obtain ⟨l, hl⟩ := hS x K ((Set.subset_biUnion_of_mem (u := fun x => (S x : Set F)) hx).trans
      (IntermediateField.subset_adjoin _ _))
    exact ⟨l, ν.eA.injective ((hΦ l).trans hl)⟩
  · exact ⟨DegPre.cF D K (ν.eX χ), ν.eA.injective ((hΦ _).trans ((DVR.comp_cP D _ _).trans (ν.c_eq χ).symm))⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨u, rfl⟩
    rw [ν.θ_eq, hΦ, hΦ, hΦ, ← comp_lift, ← comp_lift]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    rw [ν.σ_eq, hΦ]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
    rw [eq_div_of_mul_eq h0 (ν.th_eq (Φ x)), hΦ]
    exact div_mem (hw _ _) hrig
  · rw [ν.ψ_eq]
    refine mul_mem ?_ hrig
    rw [← (extMap_jFK (R := R) f hf).trans (Category.id_comp _)]
    exact hv _ _

end GlobalTheory.FiniteValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetFactor
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.PointDescentFactorization

theorem exists_finset_factor {R Ω : Type} [CommRing R] [Field Ω] (g : ℚ →+* R) (hg : g.FiniteType)
    (φ : R →+* Ω) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range β →
      ∃ ψ : R →+* k, β.comp ψ = φ := by
  classical
  letI : Algebra ℚ R := g.toAlgebra
  have hft : Algebra.FiniteType ℚ R := hg
  obtain ⟨t, ht⟩ := hft.out
  refine ⟨t.image φ, fun k _ β hs => ?_⟩
  have hq : ∀ q : ℚ, φ (g q) ∈ β.fieldRange := by
    intro q
    have h := map_ratCast (φ.comp g) q
    rw [Rat.cast_id, RingHom.comp_apply] at h
    rw [h]
    exact SubfieldClass.ratCast_mem _ q
  have hall : ∀ x : R, φ x ∈ β.fieldRange := by
    intro x
    have hx : x ∈ Algebra.adjoin ℚ (t : Set R) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap q => exact hq q
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨(β.rangeRestrictFieldEquiv.symm.toRingHom).comp (φ.codRestrict β.fieldRange hall), ?_⟩
  ext x
  have h := β.rangeRestrictFieldEquiv.apply_symm_apply ⟨φ x, hall x⟩
  exact congrArg Subtype.val h

theorem point_descends {Ω : Type} [Field Ω] {X : Scheme}
    (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℚ) [LocallyOfFiniteType p]
    (a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ X) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range (⇑β : k → Ω) →
      ∃ b : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k ⟶ X, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β ≫ b = a := by
  let x₀ : (Spec (CommRingCat.of Ω)) := IsLocalRing.closedPoint Ω
  obtain ⟨R, j, hj, hx⟩ : ∃ (R : CommRingCat.{0}) (j : Spec R ⟶ X), IsOpenImmersion j ∧
      a x₀ ∈ Set.range j := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := a x₀) (U := ⊤) trivial
    exact ⟨_, hU.fromSpec, inferInstance, by rw [hU.range_fromSpec]; exact hxU⟩
  have hr : Set.range a ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    have : y = x₀ := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [this]; exact hx
  let a' := IsOpenImmersion.lift j a hr
  have ha' : a' ≫ j = a := IsOpenImmersion.lift_fac j a hr
  obtain ⟨φ, hφ⟩ := Spec.map_surjective a'
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ p)
  have hl : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
  have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp hl
  obtain ⟨s, hs⟩ := exists_finset_factor g.hom hft φ.hom
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hs k β hβ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ j, ?_⟩
  rw [← ha', ← hφ, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  exact hψ

end GlobalTheory.PointDescentFactorization
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericRel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericIso


open GlobalTheory.RigidGeneric GlobalTheory.SecRingIso ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_genericRel : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j → ∃ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w := by
  intro hL R _ _ I hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j _ en
  obtain ⟨w, v, hw, hv, -, lf⟩ := exists_compare U
  obtain ⟨w', v', hw', hv', e', lf'⟩ := exists_compare U'
  have jac : I ≤ Ideal.jacobson ⊥ := by
    have := hI.2.2.2
    exact IsAdicComplete.le_jacobson_bot I
  have := hI.1
  have := hG.smooth
  have := hG'.smooth
  have := hG.geomConnected
  have := hG'.geomConnected
  let Ag : ∀ k, H0 U'.LG.L k → H0 U.LG.L k → Prop := fun k σ' σ => ∀ e,
    Agr (W := (thickObj R I e G').left) (Idx := D.toPre.P.L.ι × D'.toPre.P.L.ι)
      ((j e).hom.left ≫ (fstG I e G).left) (fstG I e G').left
      (fun y i => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2)
      (fun Z r z i jL => Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z i.1 (fun _ => jL))
      (fun Z r z i jL => Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z i.1 i.2 * Geo.Tor.gw (U'.w e) r z i.2 (fun _ => jL))
      σ σ'
  have ov : ∀ e, ((j e).hom.left ≫ (fstG I e G).left) ≫ G.hom = (fstG I e G').left ≫ G'.hom := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((j e).hom.left ≫ ·) (Over.w (fstG I e G))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) (Over.w (j e).hom))).trans
        (Over.w (fstG I e G')).symm))
  have cov : ∀ e (y : (thickObj R I e G').left), ∃ i : D.toPre.P.L.ι × D'.toPre.P.L.ι,
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2 := fun e y => by
    obtain ⟨a, ha⟩ := exists_chart D.toPre.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y))
    obtain ⟨b, hb⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left y)
    exact ⟨(a, b), ha, hb⟩
  obtain ⟨Φ, w₀, h₀, H⟩ := exists_iso_of_rel hL G.hom G'.hom U.LG.isLB U'.LG.isLB A A' (gen_over' U) (gen_over' U')
    (gen_injective U) (gen_injective U') hv hv' lf lf' Ag
    (fun k c s' s t' t d' d h h' f' f e => (h e).comb (ov e) (h' e) f f')
    (fun n m s' s t' t d' d h h' f' f e => (h e).mul (h' e) f f')
    (fun k s' s h => ⟨fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G).1 _
        (linComb_isLB _ U.LG.isLB _ _) s fun e J => by
          have : IsIso (j e).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (j e).hom))
          exact (ConcreteCategory.bijective_of_isIso ((j e).hom.left.app _)).1
            (((h e).zero U'.LG.isLB (cov e) f J).trans (map_zero _).symm)),
      fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G').1 _
        (linComb_isLB _ U'.LG.isLB _ _) s' fun e J => (h e).symm.zero U.LG.isLB (cov e) f J)⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).1 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).2 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
  obtain ⟨u, hu, K⟩ := exists_move U.LG.isLB U'.LG.isLB A.isLB A'.isLB (gen_inv U') hv h₀ hw' e'
    ((U'.gen ≪≫ Φ ≪≫ U.gen.symm).hom.left ≫ pullback.fst G.hom (jK R))
    ((Category.assoc _ _ _).trans (congrArg (U'.gen.hom.left ≫ ·) (Category.assoc _ _ _)))
  refine ⟨U'.gen ≪≫ Φ ≪≫ U.gen.symm, u, hu, fun k hk σ' σ h => ?_⟩
  obtain ⟨a, ha⟩ := exists_pulls U.LG.isLB A.isLB hv σ
  obtain ⟨a', ha'⟩ := exists_pulls U'.LG.isLB A'.isLB hv' σ'
  exact K k σ σ' a a' ha
    (H k hk σ' σ a' a (fun e Z r z i a b hC => h e Z r z i.1 i.2 a b hC.1 hC.2) ha' ha) ha'

end GlobalTheory.GenericIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F}

def HomF (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Prop :=
  φ.hom ≫ fst _ _ = fst _ _ ∧ ∀ (Z : Over (Sp R)) (t : Z ⟶ TF (R := R) F) (x y : Z ⟶ D.P.A),
    lift t (x * y) ≫ φ.hom ≫ snd _ _ = (lift t x ≫ φ.hom ≫ snd _ _) * (lift t y ≫ φ.hom ≫ snd _ _)

abbrev BunIso (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Type :=
  LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)

def Carries (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (x : N.A) (x' : N'.A) : Prop :=
  lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν'.eA x')

def wVal (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A} (w : BunIso φ)
    (f : N.A → N'.A) (x : N.A) : F :=
  valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _
    (w.s (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left)).val

def AllIso (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N N' : NumD F} (_ : NumOf D F N) (_ : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A},
    BunIso φ → (N.A → N'.A) → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (w : BunIso φ) (f : N.A → N'.A), HomF φ → w.IsGen → (∀ x, Carries ν ν' φ x (f x)) → P ν ν' w f

def TorsMap {O : Type} [CommRing O] (B B' : NumB O) (m : ℕ) (c : O) (ρ : B.A → B'.A) : Prop :=
  (∀ b b', b ^ m ^ 2 = 1 → b' ^ m ^ 2 = 1 →
    ρ (b * b') = ρ b * ρ b' ∧ B'.weil (m ^ 2) (ρ b) (ρ b') = B.weil (m ^ 2) b b') ∧
  ∀ b, b ^ m ^ 2 = 1 → ρ b ^ m ^ 2 = 1 ∧ B'.uth m (ρ b) 1 = c * B.uth m b 1

def IsFib (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q : PolAV (Sp F))
    (Φ : Q.A.left ⟶ D.P.A.left) : Prop :=
  IsGrpPullback Q.A D.P.A (TF (R := R) F).hom Φ ∧ LBIso Q.L (D.P.L.pull Φ) ∧ Q.g = D.P.g

theorem exists_isFib (hB : PolBaseChangeSt) (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ Q Φ, IsFib D F Q Φ := by
  obtain ⟨P', φ, hφ, hg, hm, ht⟩ := hB _ _ (TF (R := R) F).hom D.P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ht, hg⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

end GlobalTheory.Ex.AbPartIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem GlobalTheory.LN.exists_polAV_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)), PolAt t (jK R) → letI := H.starRing; ∃ (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (gen : (Over.pullback (jK R)).obj t.G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ ∀ x, (Over.pullback (jK R)).map (t.act.act x) ≫ gen.hom = gen.hom ≫ oA.act x := by
  intro _ _ E _ _ _ H R _ _ t ⟨hp, hA, hK⟩
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK R))
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom (jK R))).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  refine ⟨GenericPol.toPolAV t' g hg hp hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t'.G)), ?_,
    fun a => ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
end

