module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0060
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMin
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem half_sup_at_ortho_frame : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hrows hL2 hn hlast σ hσ f hf hsup
  have hfs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf
  have hRS := (hL.unf j hj σ hσ).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f hfs
  unfold Formalism.L2.Pj.supN at hsup ⊢
  have hStop : Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≠ ⊤ := by
    intro h
    rw [h] at hsup
    simp at hsup
  have hSpos : 0 < Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) :=
    (ENNReal.toReal_pos_iff.mp hsup).1
  have hhalf := ENNReal.half_lt_self hSpos.ne' hStop
  have hhalf' := hhalf
  unfold Formalism.L2.Pj.supE at hhalf'
  obtain ⟨⟨k, x, hx⟩, hp⟩ := lt_iSup_iff.mp hhalf'
  have hB := (hRS k).2.1
  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((T.U j σ).X k) hx
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((T.U j σ).X k) hx hb
  have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((T.U j σ).X k) hx
  have hpn := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
    (rdU (T.U j σ) f k) hB x hx _ hb
  have hu1 : ∀ τ i, ‖dmin ((T.U j σ).X k).Gm
      (rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((T.U j σ).X k) x)) τ i‖ = 1 :=
    fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((T.U j σ).X k) ho τ i
  have hpu := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((T.U j σ).X k)
    (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) hu1
  have hrd := Formalism.L2.Pj.rdU_mem (T.U j σ) f k hy
  have hlt := (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hStop two_ne_zero)
    ENNReal.ofReal_ne_top).mpr hp
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal'] at hlt
  have hlt' : (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal / 2 <
      max (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x) 0 := by
    simpa using hlt
  have hm : 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x := by
    rcases lt_max_iff.mp (lt_trans (half_pos hsup) hlt') with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  rw [max_eq_left hm.le] at hlt'
  have hle : ∀ z ∈ ((T.U j σ).X k).dom,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z ≤
        (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal := by
    intro z hz
    have h1 : ENNReal.ofReal (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z) ≤
        Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le (⟨k, ⟨z, hz⟩⟩ : Formalism.L2.Pj.FPt (T.U j σ).X) le_rfl
    exact (ENNReal.ofReal_le_iff_le_toReal hStop).mp h1
  refine ⟨k, ⟨_, hy⟩, hu1, ho, ?_, ?_⟩
  · rw [← hrd, ← hpu, hpn]
    linarith
  · exact _root_.GlobalTheory.RunIn.firstMin_at_halfMax D T hL hG large₂ j hj w hrows hL2 hn σ hσ f hf k _ hy
      (fun z hz => by rw [hpn]; linarith [hle z hz]) (by rw [hpn]; exact hm)

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverDescent

theorem eq_of_geometric_points {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rw [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this
  exact this

theorem isReduced_of_smooth_algebra (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] : _root_.IsReduced S := by
  have hs : Smooth (spMap (algebraMap R S)) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 ‹_›)
  have : IsReduced (Sp S) := GlobalTheory.isReduced_of_smooth_of_isReduced (spMap (algebraMap R S))
  exact (affine_isReduced_iff (CommRingCat.of S)).1 this


open scoped TensorProduct in
theorem exists_lift_geometric (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.FaithfullyFlat R S] (k : Type) [Field k] [IsAlgClosed k]
    (χ : R →+* k) : ∃ χ' : S →+* k, χ'.comp (algebraMap R S) = χ := by
  letI : Algebra R k := χ.toAlgebra
  haveI : Nontrivial (k ⊗[R] S) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := inferInstance
  let g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩
  ext x
  have e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
    rfl
  change g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x
  rw [e]
  exact g.commutes (χ x)


open scoped TensorProduct in
theorem exists_preimage_of_geometric (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S] (w : S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ₁ χ₂ : S →+* k),
      χ₁.comp (algebraMap R S) = χ₂.comp (algebraMap R S) → χ₁ w = χ₂ w) :
    ∃ u : R, algebraMap R S u = w := by
  haveI := isReduced_of_smooth_algebra R S
  haveI := isReduced_of_smooth_algebra S (S ⊗[R] S)
  have key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w := by
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    refine h k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_
    ext x
    change χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact (Algebra.IsEffective.of_faithfullyFlat R S w).1 (by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])

theorem exists_affine_lift {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f]
    (R : Type) [CommRing R] (t : Sp R ⟶ X) :
    ∃ (S : Type) (_ : CommRing S) (φ : R →+* S) (t' : Sp S ⟶ Y),
      φ.Finite ∧ φ.Smooth ∧ φ.FaithfullyFlat ∧ t' ≫ f = spMap φ ≫ t := by
  let Z := pullback f t
  let g : Z ⟶ Sp R := pullback.snd f t
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ g)
  have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have h4 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  refine ⟨Γ(Z, ⊤), inferInstance, φ.hom, Z.isoSpec.inv ≫ pullback.fst f t,
    (IsFinite.SpecMap_iff φ).1 h1, (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h2, ?_, ?_⟩
  · rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).1 h3, h4.surj⟩
  · change _ = Spec.map φ ≫ t
    rw [hφ, Category.assoc, pullback.condition, Category.assoc]

section Eval
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_of_test (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (f : Rul Xo c) (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F) (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
    (z : FrPt Xo c S) (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have ht : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left ht]
  exact hWD f hf S _ p _ φ _ y z ht.choose_spec.choose_spec.choose_spec h

theorem evR_baseChange (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hT : AllTest Xo c)
    (f : Rul Xo c) (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [_root_.IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T) (h : FrMap ψ y z) :
    evR Xo c f z = ψ (evR Xo c f y) := by
  obtain ⟨p, φ, y0, h0⟩ := hT S y
  rw [evR_of_test hWD f hf p φ y0 y h0, evR_of_test hWD f hf p (ψ.comp φ) y0 z
    (((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 _ _ _ φ ψ y0 y z h0).1 h)]
  rfl

theorem exists_cover_point {l₂ : Level H} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂} (hc : c.F = c₂.F)
    (r : Xo₂.X ⟶ Xo.X) (rF : Xo₂.XF c₂ ⟶ Xo.XF c)
    (h1 : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h2 : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom)
    [IsFinite rF] [Etale rF] [Surjective rF]
    (R : Type) [CommRing R] [Algebra c.F R] (x : Sp R ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c R) :
    ∃ (S : Type) (_ : CommRing S) (φ : R →+* S) (j : c₂.F →+* S) (x₂ : Sp S ⟶ Xo₂.X),
      φ.Finite ∧ φ.Smooth ∧ φ.FaithfullyFlat ∧
      j.comp (IntermediateField.inclusion hc.le).toRingHom = φ.comp (algebraMap c.F R) ∧
      x₂ ≫ r = spMap φ ≫ x ∧
      x₂ ≫ Xo₂.s = spMap (j.comp (IntermediateField.inclusion c₂.le).toRingHom) := by
  let t : Sp R ⟶ Xo.XF c := pullback.lift x (spMap (algebraMap c.F R)) (by
    rw [hx, sOf, ← Spec.map_comp]; rfl)
  obtain ⟨S, _, φ, t', f1, f2, f3, ht⟩ := exists_affine_lift rF R t
  obtain ⟨j, hj⟩ := Spec.map_surjective (R := CommRingCat.of c₂.F) (S := CommRingCat.of S)
    (t' ≫ pullback.snd _ _)
  refine ⟨S, inferInstance, φ, j.hom, t' ≫ pullback.fst _ _, f1, f2, f3, ?_, ?_, ?_⟩
  · have e : Spec.map j ≫ spMap (IntermediateField.inclusion hc.le).toRingHom =
        spMap φ ≫ spMap (algebraMap c.F R) := by
      rw [hj, Category.assoc, ← h2, ← Category.assoc, ht, Category.assoc, pullback.lift_snd]
    rw [← Spec.map_comp, ← Spec.map_comp] at e
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  · rw [Category.assoc, ← h1, ← Category.assoc, ht, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ← hj, ← Spec.map_comp]
    rfl

end Eval

theorem shortValue_descends : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), EvalWD (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) → AllTest d.Xo₂ d.c₂ → @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃! u : p.R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (χ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z → ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v → χ u = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
  intro hL hC E _ _ _ H Dw l Xo c n d hWD hAT hN hlev hA _ hnab hph Λ N hU hTr hLv a P hP x0 β p y
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := _root_.GlobalTheory.shortThetaValue_existsUnique_natural hL hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n Λ N hU hTr hLv a P hP
    (d.w x0) β
  have hinv := GlobalTheory.T.cover_mul_shortThetaSeries_indep_of_framed_lift hL hC E H Dw l Xo c n d hN hlev hA hnab hph Λ N hU hTr hLv a P hP x0 β
  have hbc := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c
  have hbc₂ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂
  have hcomp := (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1
  obtain ⟨hdvd, hM, -, -, -, -, hlift, hsec, -⟩ := id hlev
  obtain ⟨r, jK, m, -, -, he, heA, -, hF⟩ := hN l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h1, h2, _, _, _, -⟩ := hF c d.c₂ d.hF.symm
  have hEta : DeltaDat.EtaOK { d with r := r, m := m } := by
    refine ⟨fun b => ?_, heA⟩
    have := he b
    rwa [hM, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)] at this
  obtain ⟨hov1, hov2, -⟩ := _root_.GlobalTheory.frames_lift_to_cover hL E H Dw l Xo c n { d with r := r, m := m }
  obtain ⟨S, _, φ, j, x₂, f1, f2, f3, hj, hx, hx'⟩ :=
    exists_cover_point d.hF.symm r rF h1 h2 p.R y.x y.x_over
  letI : Algebra p.R S := φ.toAlgebra
  letI : Algebra c.F S := (φ.comp (algebraMap c.F p.R)).toAlgebra
  letI : Algebra d.c₂.F S := j.toAlgebra
  haveI : Module.Finite p.R S := f1
  haveI : Algebra.Smooth p.R S := f2
  haveI : Module.FaithfullyFlat p.R S := f3
  haveI := isReduced_of_smooth_algebra p.R S
  have hS : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := fun a =>
    RingHom.congr_fun hj a
  let φa : p.R →ₐ[c.F] S := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := hbc p.R S φa y
  obtain ⟨y₂, -, hy₂⟩ := hov1 S hS y' x₂ (hx.trans hy'.1.symm) hx'
  obtain ⟨v₀, hv₀, -⟩ := hval S y₂
  have core : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (χ' : S →+* k), χ'.comp φ = χ.toRingHom →
      ∀ (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
      ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v →
        χ' (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
    intro k _ _ _ _ hk χ χ' hχ z z₂ hz hz₂ v hv
    have c1 : ∀ a : c.F, χ' (algebraMap c.F S a) = algebraMap c.F k a := fun a =>
      (RingHom.congr_fun hχ (algebraMap c.F p.R a)).trans (χ.commutes a)
    let ψ : S →ₐ[c.F] k := { χ' with commutes' := c1 }
    let ψ₂ : S →ₐ[d.c₂.F] k := { χ' with
      commutes' := fun b => by
        obtain ⟨a, rfl⟩ := d.eF.surjective b
        exact (congrArg χ' (hS a)).trans ((c1 a).trans (hk a).symm) }
    have hψ : ψ.comp φa = χ := AlgHom.ext fun x => RingHom.congr_fun hχ x
    have hz' : FrMap ψ y' z := (hcomp _ _ _ φa ψ y y' z hy').2 (by rw [hψ]; exact hz)
    obtain ⟨w₂, hw₂⟩ := hbc₂ S k ψ₂ y₂
    have hw := hov2 S hS k hk ψ ψ₂ rfl y' y₂ z w₂ hy₂ hz' hw₂
    obtain ⟨v', hv', -⟩ := hval k w₂
    rw [hinv r m hEta k hk z z₂ w₂ hz₂ hw v v' hv hv', ← hnat S k ψ₂ y₂ w₂ hw₂ v₀ v' hv₀ hv',
      evR_baseChange hWD hAT d.cδ hsec.1 ψ₂ y₂ w₂ hw₂]
    exact map_mul χ' _ _
  have pts : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : p.R →+* k),
      ∃ (_ : Algebra c.F k) (_ : Algebra d.c₂.F k) (χa : p.R →ₐ[c.F] k) (z : FrPt Xo c k)
        (z₂ : FrPt d.Xo₂ d.c₂ k) (v : k),
        (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) ∧ χa.toRingHom = χ ∧
        FrMap χa y z ∧ FrOver d z₂ z ∧ ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v := by
    intro k _ _ χ
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    letI i2 : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
      congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hbc p.R k χa y
    obtain ⟨z₂, hz₂⟩ := hlift k hk z
    obtain ⟨v, hv, -⟩ := hval k z₂
    exact ⟨i1, i2, χa, z, z₂, v, hk, rfl, hz, hz₂, hv⟩
  obtain ⟨u, hu⟩ := exists_preimage_of_geometric p.R S (evR d.Xo₂ d.c₂ d.cδ y₂ * v₀) (by
    intro k _ _ χ₁ χ₂ h12
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k (χ₁.comp φ)
    exact (core k hk χa χ₁ hχ.symm z z₂ hz hz₂ v hv).trans
      (core k hk χa χ₂ (h12.symm.trans hχ.symm) z z₂ hz hz₂ v hv).symm)
  refine ExistsUnique.intro u ?_ ?_
  · intro k _ _ _ _ hk χ z z₂ hz hz₂ v hv
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ.toRingHom
    rw [← core k hk χ χ' hχ' z z₂ hz hz₂ v hv, ← hu]
    exact (RingHom.congr_fun hχ' u).symm
  · intro u' hu'
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    obtain ⟨_, _, χa, z, z₂, v, hk, hχ, hz, hz₂, hv⟩ := pts k χ
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ
    subst hχ
    have e := core k hk χa χ' hχ' z z₂ hz hz₂ v hv
    rw [← hu] at e
    exact (hu' k hk χa z z₂ hz hz₂ v hv).trans (e.symm.trans (RingHom.congr_fun hχ' u))

end GlobalTheory.CoverDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

namespace GlobalTheory.UpperModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_pos (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  refine mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _

theorem isBddSec_sum (X : Data E r) {la : Wt X.Ψ r} {m : ℕ} {f : Fin m → Frame X.Ψ r → ℂ}
    (hf : ∀ q, X.IsBddSec la (f q)) (u : Fin m → ℂ) : X.IsBddSec la fun x => ∑ q, u q * f q x := by
  refine ⟨⟨DifferentiableOn.fun_sum fun q _ => (hf q).1.1.const_mul _, fun x hx b hb => ?_,
    fun γ hγ x hx => ?_⟩, ?_⟩
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.1 x hx b hb]; ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.2 γ hγ x hx]; ring
  · choose C hC using fun q => (hf q).2
    refine ⟨∑ q, ‖u q‖ * C q, fun x hx => ?_⟩
    have hN : 0 ≤ ∏ τ, ∏ i : Fin r,
        ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by positivity
    calc X.pnorm la (fun x => ∑ q, u q * f q x) x
        ≤ (∑ q, ‖u q * f q x‖) * _ := mul_le_mul_of_nonneg_right (norm_sum_le _ _) hN
      _ = ∑ q, ‖u q‖ * X.pnorm la (f q) x := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => by rw [norm_mul, mul_assoc]; rfl
      _ ≤ _ := Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hC q x hx) (norm_nonneg _)

theorem s_xs {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 :=
  (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, LeadJets.nmat_zero_mem_Bor X, by
      rw [LeadJets.rmul_nmat_zero, LeadJets.lact_one]⟩ k

theorem zero_mem_OmF {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) : (0 : V (nd X)) ∈ OmF X x := by
  show cpt X x 0 ∈ X.dom
  rw [LeadJets.cpt_zero]; exact hx

theorem exists_s_ne {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) :
    ∃ k, ∃ x ∈ X.dom, Fl.s k x ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, -⟩ := Xa.et_ne
  obtain ⟨j, -⟩ := (Fl.S_eq x hx).1 fun k => h k x hx
  apply Fl.coord j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds (zero_mem_OmF (Fl.xs_mem j))] with z hz
    ext k
    simp [h k _ hz]
  rw [hev.fderiv_eq, fderiv_const_apply]
  have hn := Xa.n_ge
  haveI : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have := LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis
  simpa [ContinuousLinearMap.det] using this

theorem exists_comb {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (e m : ℕ)
    (f : Fin m → Frame X.Ψ r → ℂ) (hf : ∀ q, DifferentiableOn ℂ (f q) X.dom)
    (hm : Fl.δ * (e + nd X).choose (nd X) < m) :
    ∃ u : Fin m → ℂ, u ≠ 0 ∧ ∀ j, (fun z : V (nd X) => ∑ q, u q * f q (cpt X (Fl.xs j) z))
      =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by
  classical
  have hj := fun q => LeadJets.jets (T := e) (a0 := e + 1) (U := fun j => OmF X (Fl.xs j))
    (f := fun j z => f q (cpt X (Fl.xs j) z))
    (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z))
    (t := fun j _ k => if k = j then 1 else 0) le_rfl
    (fun j => OntoB.isOpen_OmF X _)
    (fun j => zero_mem_OmF (Fl.xs_mem j))
    (fun j => OntoB.hol_comp X _ (hf q))
    (fun j => OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (Fl.s_van k).1.1.1.1)
    (fun j k => differentiableOn_const _)
    (fun j => by simpa only [LeadJets.cpt_zero] using Fl.w0_ne j)
    (fun j k => by simpa only [LeadJets.cpt_zero] using s_xs Fl j k)
    Fl.coord
    (fun v => ⟨v, fun j => by simp⟩)
  choose cc hcc using hj
  let v : Fin m → (Fin Fl.δ × multiLt (nd X) (e + 1) → ℂ) := fun q p => cc q p.2.1 p.1
  have hdep : ¬ LinearIndependent ℂ v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe, ManyForms.card_multiLt_succ] at this
    omega
  obtain ⟨u, hu, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hu' : ∀ α ∈ multiLt (nd X) (e + 1), ∀ k, ∑ q, u q * cc q α k = 0 := fun α hα k => by
    simpa [v] using congrFun hu (k, ⟨α, hα⟩)
  refine ⟨u, fun h => hi (by simp [h]), fun j => ?_⟩
  have hz : ∀ (s : Fin (nd X) → ℂ) (w : ℂ) (t : Fin Fl.δ → ℂ),
      ∑ q, u q * LeadJets.leadVal s w t e (e + 1) (cc q) = 0 := fun s w t => by
    unfold LeadJets.leadVal
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [← mul_assoc, ← Finset.sum_mul, hu' α hα k, zero_mul]
  have hsum := IsBigO.sum (s := Finset.univ) fun q _ => (hcc q j).const_mul_left (u q)
  refine hsum.congr_left fun z => ?_
  simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, hz, sub_zero]

theorem exists_mul_ne {X : Data E r} {f g : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom)
    (hg : DifferentiableOn ℂ g X.dom) (hf0 : ∃ x ∈ X.dom, f x ≠ 0) (hg0 : ∃ x ∈ X.dom, g x ≠ 0) :
    ∃ x ∈ X.dom, f x * g x ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, hfx⟩ := hf0
  obtain ⟨y, hy, hgy⟩ := hg0
  exact hgy (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hf hg h hx hfx y hy)

theorem upper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, X.IsBddSec (Xa.Fp + Xa.T • Xa.L) (f q)) → (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) → m ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) := by
  intro E _ _ _ r X Xa Fl m f hf hind
  by_contra hm
  obtain ⟨u, hu, hO⟩ := exists_comb Fl (Xa.T + nd X + 6) m f (fun q => (hf q).1.1) (by
    rw [show Xa.T + nd X + 6 + nd X = Xa.T + 2 * nd X + 6 by ring]; omega)
  have hg := isBddSec_sum X hf u
  have hg0 : ∃ x ∈ X.dom, ∑ q, u q * f q x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (hind u h)
  obtain ⟨k, hk⟩ := exists_s_ne Fl
  have d1 := hg.1.1
  have d2 := Xa.secondTheta_vanishes.1.1.1.1
  have d3 := Xa.firstTheta_vanishes.1.1.1.1
  have d4 := Xa.et_sec.1
  have d5 := (Fl.s_van k).1.1.1.1
  obtain ⟨x, hx, hne⟩ := exists_mul_ne (((d1.mul d2).mul d3).mul d4) d5
    (exists_mul_ne ((d1.mul d2).mul d3) d4 (exists_mul_ne (d1.mul d2) d3
      (exists_mul_ne d1 d2 hg0 Xa.secondTheta_ne_zero) Xa.firstTheta_ne_zero) Xa.et_ne) hk
  simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or] at hne
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
  obtain ⟨x0, hx0, hs0, hpos, hmax⟩ := GlobalTheory.T.normQuotientThetaFlat_attains_sup_off_common_zeros E r X Xa Fl _ hg hO ⟨x, hx, by
    have p1 := pnorm_pos X (Xa.Fp + Xa.T • Xa.L) (P := fun x => ∑ q, u q * f q x) hx h1
    have p2 := pnorm_pos X ((nd X + 4) • Xa.L - Xa.Fp) hx h2
    have p3 := pnorm_pos X (2 • Xa.L - Xa.de) hx h3
    have p4 := pnorm_pos X ((Xa.i * (Xa.g0 / 2)) • Xa.de) hx h4
    have p5 : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (pnorm_pos X _ hx h5) 2⟩
    positivity⟩
  exact GlobalTheory.T.quotient_no_positive_max_off_common_zeros E r X Xa Fl _ hg.1 x0 hx0 hs0 hpos hmax

end GlobalTheory.UpperModel
end

