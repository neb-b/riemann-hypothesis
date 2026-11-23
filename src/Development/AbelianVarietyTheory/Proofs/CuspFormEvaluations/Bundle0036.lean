module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHarmonicAndMemMinorSpan
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaSublatticeJetNeZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsExpansionOfEqSumThFr
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem hasSum_prod_of_fintype {J ι : Type*} [Fintype J] {f : J → ι → ℂ} {y : J → ℂ}
    (hf : ∀ j, Summable fun m => ‖f j m‖) (h : ∀ j, HasSum (f j) (y j)) :
    (Summable fun p : J × ι => ‖f p.1 p.2‖) ∧ HasSum (fun p : J × ι => f p.1 p.2) (∑ j, y j) := by
  have h1 : Summable fun p : J × ι => ‖f p.1 p.2‖ :=
    (summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨hf, Summable.of_finite⟩
  have h2 := h1.of_norm.hasSum
  exact ⟨h1, (h2.prod_fiberwise h).unique (hasSum_fintype y) ▸ h2⟩

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n) (hpq : X.p0 + q0 ≤ n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  have hm : P ∈ GaussGauge.minorSpan (Fin n) c c' :=
    GaussGauge.orbitSpan_le_minorSpan (add_comm X.p0 q0 ▸ hpq) c c'
      (Harm.rowHighest_eq_orbitSpan (add_comm X.p0 q0 ▸ hpq) c c' ℂ ▸ hP)
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) hm hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

variable {J : Type*} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
  {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ}

theorem isSec_of_eq_sum_thFr (hs : IsSympl X bas) (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Q (lact γ x) = X.χ (wtOf X hr c c' n) γ * Q x) :
    X.IsSec (wtOf X hr c c' n) Q := by
  refine ⟨DifferentiableOn.congr (DifferentiableOn.fun_sum fun j hj => ?_) hQ,
    fun x hx u hu => ?_, hΓ⟩
  · exact (differentiableOn_thFr idx hs hr n _ _
      (Harm.isHarmonic_of_mem_rowHighest (hP j hj))).const_mul _
  · rw [hQ _ (PerMove.rmul_mem_GG hx hu), hQ x hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by
      rw [thFr_rmul idx hr _ _ hs (hP j hj) hx hu, mul_left_comm]

theorem isModerate_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x) :
    X.IsModerate (wtOf X hr c c' n) Q := by
  obtain ⟨C, A, h⟩ := isModerate_sum_thFr idx hr hs hn s t a b hP
  exact ⟨C, A, fun x hx => by simpa only [Data.pnorm, hQ x hx] using h x hx⟩

theorem exists_expansion_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n) (hpq : X.p0 + q0 ≤ n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ (A : s × (Fin n → Fin g → ℤ) → ℂ) (ν : s × (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ u : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * u τ))
        (Q (X.flow ξ (fun τ => (u τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hpq hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine ⟨fun p => t p.1 * A p.1 p.2, fun p => ν p.1 p.2,
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1, fun u => ?_,
    fun p hp => h3 _ _ (right_ne_zero_of_mul hp)⟩
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

theorem mem_SS_of_eq_sum_thFr (hs : IsSympl X bas) (hn : Even n)
    (hc : (X.p0 + q0 ≤ n ∧ ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i) ∨ ∀ ξ, ¬ X.IsIso ξ)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Q (lact γ x) = X.χ (wtOf X hr c c' n) γ * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  obtain ⟨hpq, hc⟩ := hc.resolve_right fun h => h ξ hξ
  obtain ⟨A, ν, h1, h2, h3⟩ := exists_expansion_of_eq_sum_thFr idx hr s t a b hs hn hpq hc hP hQ hξ hx
  exact FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx A h1 ν h2 0 h3

end

end GlobalTheory.ThFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGenLiftOfIsNilpotent
section
noncomputable section

namespace GlobalTheory.NilGen

section General

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Z ⟶ X)} {ε' : K' → ℤ}

theorem exists_ratio (hL : L.IsLB) (p : Z ⟶ Y) (g : LB.Gen (LB.LinComb L φ' ε')) (hg : g.IsGen)
    (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') (u : LB.Sec (LB.LinComb L φ ε)) :
    ∃ h : Γ(Z, ⊤), ∀ y J, Good L y J → sval u p y J = gs (𝟙 Z) y ⊤ h * (val g (𝟙 Z) y J).val := by
  obtain ⟨t, ht⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (pullMulSec u p (LB.invGen L _ _ g) (DVR.invGen_isGen _ _ _ _ hg))
  have le : (⊤ : Z.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Z ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Z.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun y J hJ => ?_⟩
  have e := ht Z (𝟙 Z) y J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, Category.id_comp,
    sval_of t (𝟙 Z) y J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg₂ (· * ·) ((gs_res (𝟙 Z) y le trivial _).trans e).symm rfl)
  exact (Units.inv_mul_cancel_right _ _).symm

def ratioIdeal (p : Z ⟶ Y) (hp : Function.Surjective p.appTop.hom) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb L φ' ε')) : Ideal Γ(Z, ⊤) where
  carrier := {h | ∃ u : LB.Sec (LB.LinComb L φ ε),
    ∀ y J, Good L y J → sval u p y J = gs (𝟙 Z) y ⊤ h * (val g (𝟙 Z) y J).val}
  zero_mem' := ⟨DVR.SecOps.secZero, fun y J hJ => by
    rw [gs_zero (𝟙 Z) y ⊤ trivial, zero_mul]
    exact gs_zero p y _ (hJ.mem φ p)⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨DVR.SecOps.secAdd u v, fun y J hJ => ?_⟩
    rw [gs_add (𝟙 Z) y ⊤ trivial, add_mul, ← hu y J hJ, ← hv y J hJ]
    exact gs_add p y _ (hJ.mem φ p) _ _
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨c, rfl⟩ := hp c
    refine ⟨DVR.SecOps.secScale c u, fun y J hJ => ?_⟩
    rw [smul_eq_mul, gs_mul (𝟙 Z) y ⊤ trivial, mul_assoc, ← hu y J hJ]
    refine (gs_mul p y _ (hJ.mem φ p) _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    refine (gs_res p y le_top (hJ.mem φ p) c).trans ?_
    exact ((gs_pull (𝟙 Z) p y ⊤ trivial c).trans (by rw [Category.id_comp])).symm

theorem ratioIdeal_eq_top [IsAffine Y] [IsAffine Z] (hL : L.IsLB) (p : Z ⟶ Y)
    (hp : Function.Surjective p.appTop.hom) (g : LB.Gen (LB.LinComb L φ' ε')) (hg : g.IsGen)
    (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') : ratioIdeal p hp φ ε g = ⊤ := by
  have hM : (LB.LinComb L φ ε).IsLB := DVR.linComb_isLB _ hL _ _
  rw [← Ideal.span_eq (ratioIdeal p hp φ ε g), ← (isAffineOpen_top Z).iSup_basicOpen_eq_self_iff]
  refine top_unique fun y _ => ?_
  obtain ⟨k, hk⟩ := exists_chart hM (p y)
  obtain ⟨r, hr, hy⟩ := (isAffineOpen_top Y).exists_basicOpen_le (V := (LB.LinComb L φ ε).U k) ⟨p y, hk⟩ trivial
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_basicOpen hM r k hr
  obtain ⟨h, hh⟩ := exists_ratio hL p g hg hF u
  refine Opens.mem_iSup.2 ⟨⟨h, u, hh⟩, ?_⟩
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ y)
  have h₁ : IsUnit (sval u p y J) :=
    (mem_nonzeroLocus_iff_pull u p y (k := fun k => J (p ≫ φ k)) (Good.mem hJ φ p)).1 (hu.ge hy)
  rw [hh y J hJ] at h₁
  exact (isUnit_gs_iff (𝟙 Z) y ⊤ trivial h).1 (isUnit_of_mul_isUnit_left h₁)

theorem exists_gen_lift [IsAffine Y] [IsAffine Z] (hL : L.IsLB) (p : Z ⟶ Y)
    (hp : Function.Surjective p.appTop.hom) (hp' : Function.Surjective p) (g : LB.Gen (LB.LinComb L φ' ε'))
    (hg : g.IsGen) (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') :
    ∃ g' : LB.Gen (LB.LinComb L φ ε), g'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε g' p) g := by
  obtain ⟨u, hu⟩ : (1 : Γ(Z, ⊤)) ∈ ratioIdeal p hp φ ε g := by
    rw [ratioIdeal_eq_top hL p hp g hg hF]; trivial
  have hu' : ∀ y J, Good L y J → sval u p y J = (val g (𝟙 Z) y J).val := fun y J hJ => by
    rw [hu y J hJ, gs_eq (𝟙 Z) y ⊤ trivial, map_one, map_one, one_mul]
  have hn : ∀ x, x ∈ nonzeroLocus u := fun x => by
    obtain ⟨y, rfl⟩ := hp' x
    choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ y)
    refine (mem_nonzeroLocus_iff_pull u p y (k := fun k => J (p ≫ φ k)) (Good.mem hJ φ p)).2 ?_
    exact (congrArg IsUnit (hu' y J hJ)).mpr (Units.isUnit _)
  have hun : ∀ j, IsUnit (u.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    have := (mem_nonzeroLocus_iff_isUnit u hx).1 (hn x)
    rw [gs_eq (𝟙 Y) x _ hx] at this
    exact this
  refine ⟨⟨fun j => (hun j).unit⟩, fun i j => Units.ext (u.compat i j), corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, Category.id_comp]
  exact Units.ext ((gs_unit p y _ (hJ.mem φ p) _).symm.trans (hu' y J hJ))

theorem surjective_appTop_spMap {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π) :
    Function.Surjective (spMap π).appTop.hom := by
  have e : (spMap π).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom π ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2.comp hπ).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).2

theorem surjective_spMap {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π)) : Function.Surjective (spMap π) := fun x => by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha => by
    obtain ⟨n, hn⟩ := hn
    have h : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
    exact x.isPrime.mem_of_pow_mem n (h ▸ x.asIdeal.zero_mem)
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

end General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem exists_gen_lift_of_isNilpotent : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (K : Type) [Fintype K] (φ : K → (Sp A ⟶ X)) (ε : K → ℤ) (K' : Type) [Fintype K'] (φ' : K' → (Sp B ⟶ X)) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L φ' ε')), g.IsGen → (∀ (U : Type) [CommGroup U] (h : (Sp B ⟶ X) → U), ∏ k, h (spMap π ≫ φ k) ^ ε k = ∏ k, h (φ' k) ^ ε' k) → ∃ g' : LB.Gen (LB.LinComb L φ ε), g'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε g' (spMap π)) g :=
  fun _ _ hL _ _ _ _ π hπ hn _ _ _ _ _ _ _ _ g hg hF =>
    exists_gen_lift hL (spMap π) (surjective_appTop_spMap π hπ) (surjective_spMap π hπ hn) g hg hF

end GlobalTheory.NilGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevelTranslateJetNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem polyDeriv_const_mul_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {G : W → ℂ} (hG : Differentiable ℂ G) (x : W) :
    I2.polyDeriv P u (fun z => c * G z) x = c * I2.polyDeriv P u G x := by
  have := I2.polyDeriv_sum P u (Finset.univ : Finset Unit) (fun _ => c) (fun _ => G)
    (fun _ _ k => I2.contDiff_of_differentiable_fd hG k) x
  simpa using this

theorem polyDeriv_const_mul_of_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {T : W → ℂ}
    (hG : Differentiable ℂ fun z => c * T z) (x : W) :
    I2.polyDeriv P u (fun z => c * T z) x = c * I2.polyDeriv P u T x := by
  by_cases hc : c = 0
  · have := polyDeriv_const_mul_entire P u 0 hG x
    simpa [hc] using this
  · have h : T = fun z => c⁻¹ * (c * T z) := by
      funext z; field_simp
    conv_rhs => rw [h]
    rw [polyDeriv_const_mul_entire P u c⁻¹ hG x]
    field_simp

theorem exists_level_translate_jet_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ y : Matrix (Fin n) (Fin r) E, (∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ y' : Matrix (Fin n) (Fin r) E, (∀ b, y' b - y b ∈ L) → κ * thP X hr bas idx (heisG X bas y' v) P x ≠ 0 := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv θ κ hθ hm hκ P hP hdeg
  obtain ⟨F, hF, hFa, hFP⟩ := _root_.GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 P hP hdeg
  obtain ⟨s, cf, hs', hsum⟩ := GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv
    θ κ hθ hm hκ F hF hFa
  obtain ⟨hcomp, -, -, hdiff, hprod⟩ := fock_laws E r X g bas idx n hs hn x hd 1 θ
  have hprod' := hprod (fun _ => θ) κ v hv.1 hκ
  have hent : ∀ y : Matrix (Fin n) (Fin r) E,
      Differentiable ℂ fun z => κ * thA X bas idx (heisG X bas y v) x z := by
    intro y
    have : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
        fun z : Fin n → Fin g → ℂ => ∏ b, fock X bas idx x 1 (pv X idx x (y b)) θ (z b) :=
      funext fun z => (hprod' y z).symm
    rw [this]
    have hb : ∀ b, Differentiable ℂ fun z : Fin n → Fin g → ℂ =>
        fock X bas idx x 1 (pv X idx x (y b)) θ (z b) := fun b =>
      (hdiff hθ.1 (pv X idx x (y b))).comp (f := fun z : Fin n → Fin g → ℂ => z b) (differentiable_apply b)
    exact fun z => (HasFDerivAt.finsetProd (u := Finset.univ) fun b _ => (hb b z).hasFDerivAt).differentiableAt
  have hFe : F = fun z => ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := funext hsum
  rw [hFe, I2.polyDeriv_sum P _ s cf (fun y z => κ * thA X bas idx (heisG X bas y v) x z)
    (fun y _ k => I2.contDiff_of_differentiable_fd (hent y) k)] at hFP
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hFP
  refine ⟨y, hs' y hy, fun y' hy' => ?_⟩
  have hne' := right_ne_zero_of_mul hne
  have hrow : ∀ b, ∃ c : ℂ, fock X bas idx x 1 (pv X idx x (y b)) θ =
      c • fock X bas idx x 1 (pv X idx x (y' b)) θ := by
    intro b
    have h1 := hθ.2 _ (hy' b)
    have h2 := hcomp (pv X idx x (y b)) (pv X idx x (y' b - y b))
    have h3 : pv X idx x (y b) + pv X idx x (y' b - y b) = pv X idx x (y' b) := by
      funext j
      have := congrFun (per_add X x (y b) (y' b - y b)) (idx j)
      rw [add_sub_cancel] at this
      exact this.symm
    rw [h3] at h2
    have h4 : ∀ (e : ℂ) (a : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ),
        fock X bas idx x 1 a (e • φ) = e • fock X bas idx x 1 a φ := by
      intro e a φ
      funext z
      simp only [fock, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨_, by conv_lhs => rw [← h1, h4, h2, smul_smul]⟩
  choose c hcc using hrow
  have hfun : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
      fun z => (∏ b, c b) * (κ * thA X bas idx (heisG X bas y' v) x z) := by
    funext z
    rw [← hprod' y z, ← hprod' y' z, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => by rw [hcc b]; rfl
  rw [hfun, polyDeriv_const_mul_entire P _ _ (hent y'), polyDeriv_const_mul_of_entire P _ _ (hent y')] at hne'
  exact right_ne_zero_of_mul hne'

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VtBaseChange

theorem exists_mulTwist {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (N : ℕ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L 1 T)} {s' : LB.Sec (LPow A L 1 T')}
    (hs : IsPullSec A L 1 (h ▷ A) (whiskerRight_snd _ _) s s')
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])} (g₀ : α₀.IsGen)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1])}
    (cα : LB.Gen.Corr L _ _ _ _ α (LB.pullGen L _ _ α₀ (snd T A).left))
    {s₁ : LB.Sec (LPow A L ((N : ℤ) ^ 2) T)}
    (tw : IsTwistPull A L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁) :
    ∃ α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, (snd T' A ^ N).left] ![(N : ℤ) ^ 2, -1]),
      LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α₀ (snd T' A).left) ∧
      IsTwistPull A L (mulT A T' N) (snd T' A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α' s'
        (GlobalTheory.VVRank.pullS A ((N : ℤ) ^ 2) h s₁) := by
  have e1 : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := GlobalTheory.VVRank.whisker_snd_left A h
  have e2 : (snd T' A).left ≫ (mulA A N).left = (snd T' A ^ N).left := by
    unfold mulA
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hm0 : mulT A T' N ≫ (h ▷ A) = (h ▷ A) ≫ mulT A T N := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [mulT]
    · simp [mulT, MonObj.comp_pow]
  have hm : (mulT A T' N).left ≫ (h ▷ A).left = (h ▷ A).left ≫ (mulT A T N).left := by
    rw [← Over.comp_left, hm0, Over.comp_left]
  obtain ⟨α', gα', vα'⟩ := GlobalTheory.VVRank.exists_gen_pullTo (φ' := ![(snd T' A).left, (snd T' A ^ N).left])
    α₀ g₀ (snd T' A).left (by intro k; fin_cases k; exacts [Category.comp_id _, e2])
  refine ⟨α', ?_, ?_⟩
  · refine corr_of_val hL fun y J hJ => ?_
    rw [vα' _ (𝟙 _) y J hJ, val_pull hJ]
  · obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A 1 h hs
    refine GlobalTheory.VVRank.isTwistPull_of_sv A hL gα' fun y J hJ => ?_
    rw [GlobalTheory.VVRank.sv_pullS A _ h s₁ _ y hJ, GlobalTheory.VVRank.sv_of_isTwistPull A tw _ y hJ,
      GlobalTheory.VVRank.sv_pullS A _ h s _ y hJ, vα' _ (𝟙 _) y J hJ, val_corr hJ cα, val_pull hJ]
    simp only [Category.id_comp, e1, hm]

theorem isVtOver_isUUOver_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ) (I : Ideal (𝓞 E)) (T T' : Over Xo.X) (h : T' ⟶ T) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)) (s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) s s' → ∀ (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)) (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' → (∀ t : T ⟶ Xo.univ.t.G, IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s t F → IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s' (h ≫ t) F') ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s' (h ≫ x₁) (h ≫ x₂) F' := by
  intro E _ _ _ H Dw l Xo N I T T' h s s' hs F F' hF
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  refine ⟨fun t hV => ?_, fun x₁ x₂ hU => ?_⟩
  · unfold IsVtOver at hV ⊢
    obtain ⟨t₀, α₀, α, s₁, U, ht, hok, g₀, hnm, cα, tw, hsym, hact⟩ := hV
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U', -, -, hsym', hact'⟩ := _root_.GlobalTheory.ThetaPullback.exists_thetaGrp_pullback _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U
    refine ⟨h ≫ t₀, α₀, α', _, U', ?_, ?_, g₀, hnm, cα', tw', hsym' _ _ hsym,
      hact' _ _ _ _ hact (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) hF⟩
    · rw [← MonObj.comp_pow, ht]
    · unfold KilledBy at hok ⊢
      intro a ha
      rw [Category.assoc, hok a ha, MonObj.comp_one]
  · unfold IsUUOver at hU ⊢
    obtain ⟨α₀, α, s₁, s₂, U₁, U₂, g₀, hnm, cα, tw, hsym₁, hact₁, hsym₂, hact₂⟩ := hU
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U₁', -, -, hsym₁', hact₁'⟩ := _root_.GlobalTheory.ThetaPullback.exists_thetaGrp_pullback _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₁
    obtain ⟨U₂', -, -, hsym₂', hact₂'⟩ := _root_.GlobalTheory.ThetaPullback.exists_thetaGrp_pullback _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₂
    exact ⟨α₀, α', _, _, U₁', U₂', g₀, hnm, cα', tw', hsym₁' _ _ hsym₁,
      hact₁' _ _ _ _ hact₁ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂),
      hsym₂' _ _ hsym₂, hact₂' _ _ _ _ hact₂ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂) hF⟩

end GlobalTheory.VtBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_normalised_mulByNat_pullback_iso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧ IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ ∧ (∀ α₁, α₁.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₁ → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α₁ α₀) ∧ ∀ T : Over Xo.X, ∃ α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![(snd T Xo.univ.t.G).left, (snd T Xo.univ.t.G ^ N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd T Xo.univ.t.G).left) := by
  first | exact @GlobalTheory.moduli_univ_normMul | exact GlobalTheory.moduli_univ_normMul | (intros; apply GlobalTheory.moduli_univ_normMul <;> assumption)
end

