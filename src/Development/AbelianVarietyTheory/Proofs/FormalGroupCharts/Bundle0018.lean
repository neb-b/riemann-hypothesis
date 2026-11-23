module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DetJacobianFormalMulNEqPowMulUnitStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_jacobian_formalMulN_eq_pow_mul_unit : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ), ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d => MvPowerSeries.pderiv (R := R) ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by
  first | exact @GlobalTheory.MulJacobian.det_jac_mulF | exact GlobalTheory.MulJacobian.det_jac_mulF | (intros; apply GlobalTheory.MulJacobian.det_jac_mulF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniversalThickeningStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_thickening_of_finite_points : ∀ (k : Type) [Field k] (K : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType K.hom], (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite (Over.mk t ⟶ K)) → ∀ e : Chart.sp (R₀ := k) k ⟶ K, ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ) (io : Chart.sp (R₀ := k) A ⟶ K), RingHom.ker aug ^ (M + 1) = ⊥ ∧ Chart.spMap aug ≫ io = e ∧ ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ), RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : Chart.sp (R₀ := k) Q ⟶ K, Chart.spMap augQ ≫ z = e → ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = Chart.spMap a ≫ io := by
  first | exact @GlobalTheory.IsolPt.exists_universal_thickening | exact GlobalTheory.IsolPt.exists_universal_thickening | (intros; apply GlobalTheory.IsolPt.exists_universal_thickening <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFormalGroupLawOfChartOfJetChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartJLaw

variable {T : Type} [CommRing T] {d : ℕ}

theorem psJet_eq_toJet {n : ℕ} (m : ℕ) (f : PS T n d) (hf : MvPowerSeries.constantCoeff f = 0) :
    psJet m f = JetSer.toJet m f := by
  symm
  refine (JetSer.toJet_eq_mk_iff m f _).2 fun e he => ?_
  rw [MvPowerSeries.coeff_trunc]
  split_ifs with hlt
  · rfl
  · have hle : e ≤ Finsupp.equivFunOnFinite.symm fun _ => m + 1 := fun i => by
      have := Finsupp.le_degree i e
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      omega
    have heq : e = Finsupp.equivFunOnFinite.symm fun _ => m + 1 := by
      by_contra h
      exact hlt (lt_of_le_of_ne hle h)
    have h0 : e = 0 := by
      ext i
      exfalso
      have h1 := Finsupp.le_degree i e
      have h2 : e i = m + 1 := by rw [heq]; simp
      omega
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

theorem substJ_zR {n : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (q : Fin 1 × Fin d) : substJ m φ hφ (zR m q) = JetSer.toJet m (φ q.2) := by
  rw [← psJet_eq_toJet m _ (hφ q.2)]
  show MvPolynomial.aeval (fun q : Fin 1 × Fin d => psJet m (φ q.2)) (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]

theorem constantCoeff_ev {k n : ℕ} (a : Fin k → Pt T n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS T k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h1) h1 hf

theorem read_pt {G : Over (Sp T)} {A B C D : Type} [CommRing A] [Algebra T A] [CommRing B] [Algebra T B]
    [CommRing C] [Algebra T C] [CommRing D] [Algebra T D] (x : algOver T A ⟶ G) (x0 : Chart.sp (R₀ := T) B ⟶ G)
    (ρ : A →ₐ[T] B) (h : x0.left = spMap (ρ : A →+* B) ≫ x.left) (S : A →ₐ[T] C) (Φ : C →ₐ[T] D) (ψ : B →ₐ[T] D)
    (hψ : ψ.comp ρ = Φ.comp S) :
    (Chart.spMap ψ ≫ x0 : Chart.sp (R₀ := T) D ⟶ G) = algOverHom Φ ≫ algOverHom S ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, h, Chart.spMap_left, algOverHom, Over.homMk_left, ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg (fun f : A →ₐ[T] D => (f : A →+* D)) hψ

theorem isLawOf_of_isChartJ : ∀ (T : Type) [CommRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 → (∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left) → GlobalTheory.JetSer.IsLawOf x0 F.F := by
  intro T _ G _ _ d F x hx x0 _ ⟨ρ, hρ1, hρ2⟩
  refine ⟨F.const, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt T n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  have hF : ∀ j, MvPowerSeries.constantCoeff (addOf F.F a b j) = 0 :=
    fun j => constantCoeff_ev _ hab _ (F.const j)
  refine ⟨hF, fun m => ?_⟩
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg T (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d)
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt T n d) p.1 p.2) (fun p => hab p.1 p.2) m
  obtain ⟨ψ, hψ⟩ := JetSer.exists_jetHom (addOf F.F a b) hF m
  have key : ∀ (i : Fin 2) (χ : Chart.JetR T (Fin d) m →ₐ[T] Chart.JetR T (Fin n × Fin d) m),
      (∀ j, χ (Chart.zR m j) = JetSer.toJet m ((![a, b] : Fin 2 → Pt T n d) i j)) →
      χ.comp (ρ m) = Φ.comp (jetPt (d := d) i m) := by
    intro i χ hχ
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hχ, jetPt, substJ_zR, JetSer.toJet_X, hΦ]
  have keyF : ψ.comp (ρ m) = Φ.comp (substJ m F.F F.const) := by
    refine Chart.jet_ext fun q => ?_
    obtain ⟨q0, j⟩ := q
    obtain rfl : q0 = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hρ1, hψ, substJ_zR, hsub Φ hΦ]
    rfl
  refine ⟨ψ, hψ, ?_⟩
  show y m * z m = _
  rw [read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψ keyF, hx.law m, MonObj.comp_mul, ha2, hb2,
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψa (key 0 ψa ha1),
    read_pt (x m) (x0 m) (ρ m) (hρ2 m) _ Φ ψb (key 1 ψb hb1)]

end GlobalTheory.ChartJLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsSeriesOfMorphismInChartsPowMulFormalGroupLaw
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem isMapOf_pow_mulF : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by
  intro R _ G _ d x hx F hF N
  induction N with
  | zero =>
    refine ⟨gp_zero₂, fun n a y h => ?_⟩
    have h0 := (repSt_of_jetAlgSt jetAlg R G d x hx (Fin n × Fin d)).2.2.2.1
    have e : comp1 (mulF F 0) a = 0 := evP_zero ![a] (single_point_zero_constant h.1)
    rw [e, pow_zero]
    simpa only [MonObj.comp_one] using h0
  | succ N ih =>
    refine ⟨gp_addOf F hF.1 _ _ ih.1 (gp_pt 0), fun n a y h => ?_⟩
    have e : comp1 (mulF F (N + 1)) a = addOf F (comp1 (mulF F N) a) a := by
      have e1 := evP_addOf ![a] (single_point_zero_constant h.1) F (mulF F N) (pt R d 0) ih.1 (gp_pt 0)
      rw [evP_pt _ (single_point_zero_constant h.1)] at e1
      exact e1
    rw [e, pow_succ]
    simpa only [MonObj.comp_mul, Category.comp_id] using hF.2 n _ _ _ _ (ih.2 n a y h) h

end GlobalTheory.JetSer
end

