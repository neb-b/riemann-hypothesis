module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFrames
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSpan

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.GradedWeylDivisibility
open scoped Classical Pointwise Matrix

theorem coeff_mem_of_eval_mem {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A] (M : Submodule K A)
    (p : Polynomial A) (h : ∀ c : ℕ, p.eval (c : A) ∈ M) (k : ℕ) : p.coeff k ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set q : Polynomial K := ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (φ (p.coeff i)) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range (fun c : ℕ => (c : K))) ?_
      (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨c, rfl⟩
    have h1 := hφ _ (h c)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.eval_eq_sum_range, map_sum] at h1
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hq, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : p.coeff i * (c : A) ^ i = ((c : K) ^ i) • p.coeff i := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  by_cases hk : k ≤ p.natDegree
  · have := congrArg (fun r => r.coeff k) hq0
    simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range,
      Polynomial.coeff_zero] at this
    rwa [if_pos (by omega)] at this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem eval_rowGen {K : Type} [Field K] {r n : ℕ} (a b : Fin r) (c : K) (f : MvPolynomial (Fin r × Fin n) K) :
    (rowGen K a b f).eval (C c) = rowAct K (1 + Matrix.single b a c) f := by
  induction f using MvPolynomial.induction_on with
  | C x => simp [rowGen, rowAct]
  | add f g hf hg => simp only [map_add (f := _), Polynomial.eval_add, hf, hg]
  | mul_X f v hf =>
    simp only [map_mul, Polynomial.eval_mul, hf]
    congr 1
    simp only [rowGen, rowAct, aeval_X, Matrix.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib,
      Polynomial.eval_add, Polynomial.eval_C]
    congr 1
    · rw [Finset.sum_eq_single v.1]
      · simp
      · intro x _ hx
        simp [Matrix.one_apply, Ne.symm hx]
      · simp
    · rw [Finset.sum_eq_single a]
      · by_cases hv : v.1 = b
        · simp only [hv, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
            Matrix.single_apply_same]
        · simp [hv, Matrix.single, Ne.symm hv]
      · intro x _ hx
        simp [Matrix.single, Ne.symm hx]
      · simp

theorem isUnit_elem {K : Type} [Field K] [CharZero K] {r : ℕ} (a b : Fin r) (c : ℕ) :
    IsUnit (1 + Matrix.single b a (c : K)) := by
  by_cases h : a = b
  · subst h
    have hc : (1 + c : K) ≠ 0 := by exact_mod_cast (by omega : 1 + c ≠ 0)
    refine IsUnit.of_mul_eq_one (1 + Matrix.single a a (-(c : K) / (1 + c))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_same, add_assoc,
      ← Matrix.single_add, ← Matrix.single_add]
    have : -(c : K) / (1 + c) + (c + c * (-(c : K) / (1 + c))) = 0 := by field_simp; ring
    rw [this]; simp
  · refine IsUnit.of_mul_eq_one (1 + Matrix.single b a (-(c : K))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ h, add_zero,
      add_assoc, ← Matrix.single_add]
    simp

def trGL {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) : GL (Fin r) K := inside₂ K r g⁻¹

theorem trGL_coe {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) :
    (trGL g : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ := by
  simp [trGL, inside₂]

theorem rowDiv_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  unfold rowDiv
  refine coeff_mem_of_eval_mem M _ (fun c => ?_) k
  have h1 := eval_rowGen a b (c : K) f
  rw [map_natCast] at h1
  rw [h1]
  obtain ⟨u, hu⟩ := isUnit_elem (K := K) a b c
  rw [← hu]
  exact hst u f hf

theorem applyWord_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) (w : List (Fin r × Fin r × ℕ)) : applyWord K w f ∈ M := by
  unfold applyWord
  induction w with
  | nil => rw [List.foldr_nil]; exact hf
  | cons x w ih => rw [List.foldr_cons]; exact rowDiv_mem_of_stable M hst _ _ _ _ ih

theorem rowAct_one {K : Type} [Field K] {r m : ℕ} :
    rowAct K (n := m) (1 : Matrix (Fin r) (Fin r) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem orbit_stable {K : Type} [Field K] {r m : ℕ} (v : MvPolynomial (Fin r × Fin m) K) (u : GL (Fin r) K)
    (f : MvPolynomial (Fin r × Fin m) K)
    (hf : f ∈ Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v)) :
    rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈
      Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    refine Submodule.subset_span ⟨trGL u * g, ?_⟩
    have := DFunLike.congr_fun
      (rowActMul K r m (u : Matrix (Fin r) (Fin r) K) (g : Matrix (Fin r) (Fin r) K)ᵀ) v
    rw [AlgHom.comp_apply] at this
    beta_reduce
    rw [this, Units.val_mul, trGL_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem dualWeyl_le_span_orbit (K : Type) [Field K] [CharZero K] {r m : ℕ} (hm : m ≤ r) (ν : Fin m → ℕ)
    (hν : Antitone ν) :
    dualWeyl K r m ν ≤ Submodule.span K (Set.range fun g : GL (Fin r) K =>
      rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ (hw K hm ν)) := by
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K hm ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  generalize hw K hm ν = v
  refine applyWord_mem_of_stable _ (orbit_stable v) v (Submodule.subset_span ⟨1, ?_⟩) w
  beta_reduce
  rw [Units.val_one, Matrix.transpose_one, rowAct_one, AlgHom.id_apply]

theorem prod_mem_span_prod {K A ι : Type} [Field K] [CommRing A] [Algebra K A] (s : Finset ι) (S : ι → Set A)
    (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (S i)) : ∏ i ∈ s, x i ∈ Submodule.span K (∏ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty => exact Submodule.subset_span (by simp)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← Submodule.span_mul_span]
    exact Submodule.mul_mem_mul (hx a) ih

theorem trAct_ten {K : Type} [Field K] {Ix : Type} [Fintype Ix] {n : ℕ} (g : Ix → GL (Fin n) K)
    (f : Ix → MvPolynomial (Fin n × Fin n) K) :
    trAct g (ten f) = ten fun t => rowAct K (g t : Matrix (Fin n) (Fin n) K)ᵀ (f t) := by
  unfold trAct ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun t _ =>
    (blockActTensor K K Ix n n (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᵀ)).1 t (f t)

theorem VV_eq_span_orbit (K : Type) [Field K] [CharZero K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) :
    VV K lam = Submodule.span K
      (Set.range fun g : Ix → GL (Fin n) K => actP lam g (ten fun t => extremal K n (lam t))) := by
  apply le_antisymm
  · rw [VV, tensorLat, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 := prod_mem_span_prod (K := K) Finset.univ
      (fun t => blockEmb K t '' (Set.range fun g : GL (Fin n) K =>
        rowAct K (g : Matrix (Fin n) (Fin n) K)ᵀ (extremal K n (lam t))))
      (fun t => blockEmb K t (F t)) (fun t => by
        have := dualWeyl_le_span_orbit K le_rfl (lam t).natW (Formalism.L2.Col.natW_anti (lam t)) (hF t)
        exact Submodule.apply_mem_span_image_of_mem_span (blockEmb K t).toLinearMap this)
    refine Submodule.span_le.mpr ?_ h1
    intro y hy
    rw [Set.mem_fintype_prod] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    choose w hw hw' using hz
    choose g hg using hw
    have hd : detTwK lam g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => Units.ne_zero _
    have h2 : ∏ t, z t = (detTwK lam g)⁻¹ • actP lam g (ten fun t => extremal K n (lam t)) := by
      simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, inv_mul_cancel₀ hd, one_smul,
        trAct_ten]
      unfold ten
      exact Finset.prod_congr rfl fun t _ => by rw [← hw', ← hg]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine polyAction_mem_VV lam g (Submodule.subset_span ⟨_, fun t => ?_, rfl⟩)
    exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (Formalism.L2.Col.natW_anti (lam t)) (Submodule.subset_span ⟨[], rfl⟩)

end GlobalTheory.OrbitSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_faithfullyFlat_isVtOver :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b) := by
  intro hL E _ _ _ H Dw l Xo c S _ _ y n x
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hpow : ∀ {R : Type} [CommRing R] (x0 : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x0 a ^ l.M = 1 := by
    intro R _ x0 a
    rw [levPt, ← MonObj.comp_pow, (moduli_univ_eta_killed hL E H Dw l Xo a).2.2, MonObj.comp_one]
  have hkill : ∀ {R : Type} [CommRing R] (x0 : Sp R ⟶ Xo.X) (a : Dw.La),
      KilledBy Xo l.Mb (levPt Xo x0 a) := by
    intro R _ x0 a b hb
    rw [levPt, Category.assoc, (moduli_univ_eta_killed hL E H Dw l Xo a).1 b hb, MonObj.comp_one]
  obtain ⟨B, _, φ, w, hφ, hw⟩ := _root_.GlobalTheory.exists_faithfullyFlat_roots hL E H Dw l Xo S y.x l.M l.M hM hM (Fin n)
    (fun b => levPt Xo y.x (x b)) (fun b => hpow _ _)
  letI : Algebra c.F B := (φ.comp (algebraMap c.F S)).toAlgebra
  let ψ : S →ₐ[c.F] B := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := _root_.GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S B ψ y
  have hx : spMap φ ≫ y.x = y'.x := hy'.1.symm
  have hroot : ∀ (x0 : Sp B ⟶ Xo.X), spMap φ ≫ y.x = x0 → ∀ b, ∃ v : ptO Xo x0 ⟶ Xo.univ.t.G,
      v ^ l.M = levPt Xo x0 (x b) := by
    rintro _ rfl b
    refine ⟨w b, ?_⟩
    let g : ptO Xo (spMap φ ≫ y.x) ⟶ ptO Xo y.x := Over.homMk (spMap φ) rfl
    have hg : levPt Xo (spMap φ ≫ y.x) (x b) = g ≫ levPt Xo y.x (x b) := by
      rw [levPt, levPt, ← Category.assoc, comp_toUnit]
    rw [hg]
    exact Over.OverMorphism.ext (hw b)
  have hF : ∀ b, ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s
      (levPt Xo y'.x (x b)) F := by
    intro b
    obtain ⟨v, hv⟩ := hroot _ hx b
    obtain ⟨t', ht', hk⟩ := (exists_root_killedBy_pow E H Dw l Xo _ _ v l.M hM (hkill _ _) hv).2 rfl
    refine (_root_.GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo l.M l.odd (ptO Xo y'.x) y'.s).1 _ _ t' ht' ?_ hk
    rw [pow_two, pow_mul, ht', hpow]
  choose F hF using hF
  exact ⟨B, inferInstance, inferInstance, ψ, y', F, hφ, hy', hF⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesOfFormalChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory


set_option maxHeartbeats 1600000 in
theorem exists_frames_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), IsChartG t x0 d G.F A.act tg uvec x → ∃ (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e ∧ IsPrimG t wP ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e ∧ (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ Rig0G t x0 d x A.act e wP := by
  intro E _ _ _ H X0 t S _ x0 d G A κ _ tg uvec x hc

  obtain ⟨e, hgen, htr, hax⟩ :=
    _root_.GlobalTheory.ChartFrames.exists_frames E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc

  obtain ⟨ph1, h1⟩ :=
    _root_.GlobalTheory.exists_firstPartialLaw_series_of_frames E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax
  obtain ⟨ph2, h2⟩ :=
    _root_.GlobalTheory.SecondPartialLaw.exists_second_partial_law E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨sy, hsy⟩ :=
    _root_.GlobalTheory.exists_symmetry_series_of_frames E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨ad, hadc, had⟩ :=
    _root_.GlobalTheory.FrameAdjSeries.exists_ad E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax

  obtain ⟨wP, hP⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP t
  exact ⟨e, wP, ph1, ph2, sy, ad, ⟨hgen, h1, h2, hsy, had⟩, hP, htr, hax, hadc,
    _root_.GlobalTheory.ThetaVal.rig_of_frAxes E H X0 t S x0 d G.F A.act κ tg uvec x G.const A.const hc e hgen htr hax wP hP⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameLetterGLActionRepresentationKeepsHarmonic
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.FrameRead

open GlobalTheory.Harm Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)}

noncomputable def IsEnum.idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : Ix :=
  ((h.2 t.1).1 t.2).choose


omit [Fintype Ix] in
theorem IsEnum.pl_idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : pl (h.idx t) = t.1 :=
  ((h.2 t.1).1 t.2).choose_spec

theorem rename_letAct (h : IsEnum H pl) {K : Type} [Field K] (g : Ix → GL (Fin n) K)
    (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K g P) =
      colSubst (fun t => (g (h.idx t) : Matrix (Fin n) (Fin n) K)ᵀ)
        (fun t => (((g (h.idx t))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)
        (rename (thetaLetterEquiv Dw n) P) := by
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp (letAct Dw pl K g) =
    (colSubst _ _).comp (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with hτ | ⟨τ, hτ, rfl⟩
  · have h1 : ∃ t, pl t = τ := (h.2 τ).1 hτ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dite_eq_left h1, thetaLetterEquiv_of_mem Dw hτ, colSubst_X_xVar, xForm_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw hτ]
    rfl
  · have h1 : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun h1 =>
      ((not_mem_hostType_iff H τ).2 ((h.2 _).2 h1)) hτ
    have h2 : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ :=
      ⟨h.idx ⟨τ, hτ⟩, by rw [h.pl_idx]⟩
    have h3 : h2.choose = h.idx ⟨τ, hτ⟩ := h.1 (by
      rw [h.pl_idx]
      exact (ComplexEmbedding.involutive_conjugate E).injective h2.choose_spec)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dite_eq_right h1, dite_eq_left h2, thetaLetterEquiv_conjugate Dw hτ, colSubst_X_yVar, yForm_apply,
      map_sum, h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw hτ]
    rfl

theorem letAct_mul_one_mem_HHa :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (K : Type) [Field K] [CharZero K] (a : (E →+* ℂ) × ℕ → ℕ), (∀ g g' : Ix → GL (Fin n) K, letAct Dw pl K (g * g') = (letAct Dw pl K g).comp (letAct Dw pl K g')) ∧ letAct Dw pl K (1 : Ix → GL (Fin n) K) = AlgHom.id K _ ∧ ∀ (g : Ix → GL (Fin n) K), ∀ P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), letAct Dw pl K g P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw n Ix _ pl h _ K _ _ a
  have hinj := rename_injective (R := K) _ (thetaLetterEquiv Dw n).injective
  refine ⟨fun g g' => AlgHom.ext fun P => hinj ?_, AlgHom.ext fun P => hinj ?_, fun g P hP => ?_⟩
  · rw [AlgHom.comp_apply, rename_letAct Dw h, rename_letAct Dw h, rename_letAct Dw h,
      ← AlgHom.comp_apply (colSubst _ _) (colSubst _ _), colSubst_comp]
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, transpose_mul]
  · rw [rename_letAct Dw h]
    simp only [Pi.one_apply, inv_one, Units.val_one, transpose_one, colSubst_one, AlgHom.id_apply]
  · have key := mem_HHa_iff_rename (Ψ := InPsi H) (dim := Dw.mult) (n := n) (K := K)
      (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) (fun τ i => a (τ, i))
    obtain ⟨h₁, h₂, h₃⟩ := (key P).1 hP
    refine (key _).2 ?_
    have e := rename_letAct Dw h g P
    unfold thetaLetterEquiv at e
    rw [e]
    exact ⟨h₁.colSubst fun t => by rw [← transpose_mul, Units.inv_mul, transpose_one],
      fun t r => colSubst_isWeightedHomogeneous _ _ _ (h₂ t r),
      fun t r r' hr s => by rw [rowAdd_colSubst _ _ t hr.isLeft_eq, h₃ t r r' hr]⟩

end GlobalTheory.FrameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InPsiOrInPsiConjugate
section
set_option autoImplicit false

namespace GlobalTheory.CMTypeOrConjugate

open NumberField

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exfalso
    obtain ⟨x, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h2 : x ^ 2 = -(d : ℝ) := by exact_mod_cast hz
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg x]
  · exact h

theorem inPsi_or_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    Formalism.L2.Pj.InPsi H τ ∨ Formalism.L2.Pj.InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hz : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hE, map_neg, map_natCast]
  unfold Formalism.L2.Pj.InPsi
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, conj_eq_neg_of_sq H.d_prime.pos hz, h, neg_neg]

end GlobalTheory.CMTypeOrConjugate
end

