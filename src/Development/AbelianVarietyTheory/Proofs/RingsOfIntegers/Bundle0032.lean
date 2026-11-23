module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitDetOfProductMapNeZero
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceExtField

open IsDedekindDomain

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem vV_unit (u : Vˣ) : vV V (algebraMap V K' u) = 0 := by
  have : valV V (algebraMap V K' u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]

theorem vV_pos {a : V} (ha : a ≠ 0) (hu : ¬ IsUnit a) : 0 < vV V (algebraMap V K' a) := by
  have h0 : algebraMap V K' a ≠ 0 := by simpa using ha
  have : valV V (algebraMap V K' a) < 1 := by
    rw [valV, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hu
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 this
  simp only [vV]; simp at this; omega

theorem vV_irr {a : V} (ha : Irreducible a) : vV V (algebraMap V K' a) = 1 := by
  have : valV V (algebraMap V K' a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem exists_index {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (j : V →+* V') [IsLocalHom j] (i : K' →+* K'')
    (hi : ∀ v, i (algebraMap V K' v) = algebraMap V' K'' (j v)) :
    ∃ r : ℕ, 0 < r ∧ ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have inj : ∀ v, v ≠ 0 → algebraMap V' K'' (j v) ≠ 0 := fun v hv => by
    rw [← hi]; simpa using hv
  have pos : 0 < vV V' (algebraMap V' K'' (j p)) :=
    vV_pos (fun h => inj p hp.ne_zero (by simp [h])) (fun h => hp.not_isUnit (isUnit_of_map_unit j p h))
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le pos.le
  have key : ∀ v : V, v ≠ 0 → vV V' (i (algebraMap V K' v)) = (r : ℤ) * vV V (algebraMap V K' v) := by
    intro v hv
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hp
    have h1 : algebraMap V K' p ≠ 0 := by simpa using hp.ne_zero
    have h2 : algebraMap V K' u ≠ 0 := by simp
    rw [hi, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
      vV_mul (inj _ u.ne_zero) (pow_ne_zero _ (inj p hp.ne_zero)), vV_mul h2 (pow_ne_zero _ h1),
      vV_pow (inj p hp.ne_zero), vV_pow h1, vV_unit, vV_irr hp, hr]
    have := vV_unit (K' := K'') (Units.map j.toMonoidHom u)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this
    rw [this]; ring
  refine ⟨r, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hb1 : algebraMap V K' b ≠ 0 := by simpa using hb0
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a := div_mul_cancel₀ _ hb1
  have e1 := vV_mul (V := V) hx hb1
  have e2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb1)
  rw [← map_mul, e, key a ha0, key b hb0] at e2
  rw [e] at e1
  rw [e1] at e2
  linarith

end Val

theorem exists_cdvr_finite_extension : ∀ (T : CDVR) (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L], ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (ψ : L ≃+* T'.Fr) (φ : T.V →+* T'.V), 0 < e ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iT a) ∧ (∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ (T.FinRes → T'.FinRes) := by
  intro T L _ _ _
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  let iT : T.Fr →+* FractionRing W := ψ.toRingHom.comp (algebraMap T.Fr L)
  have hφ : ∀ a, iT (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change (FractionRing.algEquiv W L).symm (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, AlgEquiv.commutes]
  obtain ⟨e, he, hv⟩ := exists_index (algebraMap T.V W) iT hφ
  refine ⟨T', iT, e, ψ, algebraMap T.V W, he, hv, fun a => rfl, fun a => (hφ a).symm, fun h => ?_⟩
  haveI : Finite (ResidueField T.V) := h
  exact Module.finite_of_finite (ResidueField T.V) (M := ResidueField W)

end GlobalTheory.PlaceExtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsTraceEqFormMulDiagonal
section
namespace GlobalTheory.TraceDiagonal

open IsLocalRing
open scoped TensorProduct

theorem exists_trace_eq_of_isUnit_det {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {d : ℕ} (b : Module.Basis (Fin d) A R) (M : Matrix (Fin d) (Fin d) A)
    (h : ∀ x : R, (∑ i, ∑ j, M i j • TensorProduct.tmul A (b i) (b j)) *
      (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) = 0) (hu : IsUnit M.det) :
    ∃ lam : R →ₗ[A] A, ∀ x : R,
      Algebra.trace A R x = lam (x * ∑ i, ∑ j, M i j • (b i * b j)) := by
  have hΦ : ∀ f : R →ₗ[A] A, ∑ i, ∑ j, (M i j * f (b i)) • b j
      = b.equivFun.symm (Matrix.vecMul (fun i => f (b i)) M) := by
    intro f
    rw [b.equivFun_symm_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.vecMul, dotProduct, Finset.sum_smul, mul_comm]
  set J : R := ∑ i, ∑ j, M i j • (b i * b j) with hJ
  let lam : R →ₗ[A] A := b.constr A (Matrix.vecMul (b.equivFun 1) M⁻¹)
  have h1 : ∑ i, ∑ j, (M i j * lam (b i)) • b j = 1 := by
    have e : (fun i => lam (b i)) = Matrix.vecMul (b.equivFun 1) M⁻¹ :=
      funext fun i => b.constr_basis A _ i
    rw [hΦ, e, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one,
      LinearEquiv.symm_apply_apply]
  have h2 : ∑ i, ∑ j, (M i j * (lam ∘ₗ LinearMap.mulRight A J) (b i)) • b j = J := by
    have := annihilator_diagonal_form_swap b M h lam J
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
    rw [this]
    simp only [← smul_mul_assoc, ← Finset.sum_mul]
    rw [h1, one_mul]
  have h3 := annihilator_diagonal_trace b M h
  rw [← hJ, ← h2, hΦ, hΦ] at h3
  have h4 := congrArg (fun v => Matrix.vecMul v M⁻¹) (b.equivFun.symm.injective h3)
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] at h4
  have h5 : Algebra.trace A R = lam ∘ₗ LinearMap.mulRight A J := b.ext fun i => congrFun h4 i
  exact ⟨lam, fun x => by rw [h5]; rfl⟩

end GlobalTheory.TraceDiagonal

namespace GlobalTheory

open IsLocalRing

theorem exists_trace_eq_form_mul_diagonal : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (Δ : TensorProduct A R R) (ε : R →+* ResidueField A), ε.comp (algebraMap A R) = residue A → (∀ x : R, ε x = 0 → ∃ m : ℕ, x ^ m ∈ (maximalIdeal A).map (algebraMap A R)) → (∀ x : R, (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) * Δ = 0) → (∀ (s : Finset (R × R)), Δ = ∑ p ∈ s, TensorProduct.tmul A p.1 p.2 → ∀ lift : ResidueField A → A, (∀ z, residue A (lift z) = z) → ∑ p ∈ s, lift (ε p.1) • p.2 ∉ (maximalIdeal A).map (algebraMap A R)) → ∃ lam : R →ₗ[A] A, ∀ x : R, Algebra.trace A R x = lam (x * Algebra.TensorProduct.lmul' (S := R) A Δ) := by
  intro A R _ _ _ _ _ _ Δ ε hε hnil hΔ hne
  classical
  let b := Module.finBasis A R
  let M : Matrix (Fin (Module.finrank A R)) (Fin (Module.finrank A R)) A :=
    Matrix.of fun i j => (b.tensorProduct b).repr Δ (i, j)
  have hM : Δ = ∑ i, ∑ j, M i j • TensorProduct.tmul A (b i) (b j) := by
    conv_lhs => rw [← (b.tensorProduct b).sum_repr Δ, Fintype.sum_prod_type]
    simp [M]
  have hJ : Algebra.TensorProduct.lmul' (S := R) A Δ = ∑ i, ∑ j, M i j • (b i * b j) := by
    rw [hM]; simp
  rw [hJ]
  refine TraceDiagonal.exists_trace_eq_of_isUnit_det b M (fun x => by rw [← hM, mul_comm, hΔ]) ?_
  let k := ResidueField A
  let I : Ideal R := (maximalIdeal A).map (algebraMap A R)
  letI : Algebra k (R ⧸ I) := Ideal.Quotient.algebraQuotientMapQuotient
  haveI : IsScalarTower A k (R ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨lift, hlift⟩ := (residue_surjective (R := A)).hasRightInverse
  have hεa : ∀ a, ε (algebraMap A R a) = residue A a := fun a => RingHom.congr_fun hε a
  let ev : R →ₐ[A] k := { ε with commutes' := hεa }
  have hev : ∀ x, ev x = ε x := fun _ => rfl
  let n : Ideal R := Ideal.span (Set.range fun i => b i - algebraMap A R (lift (ε (b i))))
  obtain ⟨N, hN⟩ : ∃ N, n ^ N ≤ I := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact hnil _ (by rw [map_sub, hεa, hlift, sub_self])
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset Δ
  rw [← Matrix.det_transpose]
  refine DiscrJacobian.isUnit_det_of_productMap_ne_zero (C := R ⧸ I) b n N hN ev ?_ ?_
    (Ideal.Quotient.mkₐ A I) (Algebra.TensorProduct.comm A R R Δ) M.transpose ?_ ?_ ?_
  · intro w hw
    have : n ≤ RingHom.ker ev := Ideal.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, hev]
      rw [map_sub, hεa, hlift, sub_self])
    exact this hw
  · intro w
    refine ⟨∑ i, b.repr w i * lift (ε (b i)), ?_⟩
    have e : w - algebraMap A R (∑ i, b.repr w i * lift (ε (b i)))
        = ∑ i, algebraMap A R (b.repr w i) * (b i - algebraMap A R (lift (ε (b i)))) := by
      conv_lhs => lhs; rw [← b.sum_repr w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib, Algebra.smul_def]
    rw [e]
    exact n.sum_mem fun j _ => n.mul_mem_left _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [hM, Finset.sum_comm]
    simp
  · intro x
    have := congrArg (Algebra.TensorProduct.comm A R R) (hΔ x)
    rw [map_mul, map_sub, map_zero, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.comm_tmul] at this
    linear_combination -this
  · intro h0
    refine hne s hs lift hlift (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, hs, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : algebraMap k (R ⧸ I) (ε p.1) = Ideal.Quotient.mk I (algebraMap A R (lift (ε p.1))) := by
      conv_lhs => rw [← hlift (ε p.1)]
      rfl
    rw [Algebra.smul_def, map_mul, ← e, mul_comm]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FrameTieHolds
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceInt.FrameTie

open GermD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cube_points {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (a : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (m : ℕ)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (a p.2)) ≫ x m)
    (I : ULift.{0} (Finset (Fin 2))) :
    (x m).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (Formalism.L2.Pj.homAt x0 (sL m a)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
  have hpt : (fun i => x m ≫ (![𝟙 t.G, t.act.act H.w0] : Fin 2 → (t.G ⟶ t.G)) i) =
      fun i => Formalism.L2.Pj.homAt x0 (sL m a) ≫
        (![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] : Fin 2 → (jOG x0 d m 2 ⟶ t.G)) i := by
    funext i
    fin_cases i
    · show x m ≫ 𝟙 t.G = Formalism.L2.Pj.homAt x0 (sL m a) ≫ Formalism.L2.Pj.homAt x0 (jetCopy d m (0 : Fin 2)) ≫ x m
      rw [Category.comp_id, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, sL_copy0, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id, Category.id_comp]
    · show x m ≫ t.act.act H.w0 =
        Formalism.L2.Pj.homAt x0 (sL m a) ≫ Formalism.L2.Pj.homAt x0 (jetCopy d m (1 : Fin 2)) ≫ x m
      rw [← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, sL_copy1, ha]
  simp only [cφG, ← Over.comp_left]
  refine congrArg (fun f => Over.Hom.left f) ?_
  refine (psum_hom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (x m)) _ I.down).trans
    (Eq.trans ?_ (psum_hom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (Formalism.L2.Pj.homAt x0 (sL m a))) _ I.down).symm)
  exact congrArg (fun f => psum t.G f I.down) hpt

theorem prod_points {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (a : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (m : ℕ)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (a p.2)) ≫ x m)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 1).left ⟶ t.G.left) → U) :
    (∏ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), h ((x m).left ≫ primφ t k) ^ primε k) *
      ∏ I : ULift.{0} (Finset (Fin 2)), h ((Formalism.L2.Pj.homAt x0 (sL m a)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) ^ cε 2 I = h (x m).left := by
  simp only [Fintype.prod_sum_type, primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
    cube_points t x0 d x a m ha]
  rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
  simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one, zpow_one]

theorem val_eLG_tie {X0 X1 : Scheme.{0}} (t : SAB H X0) (t' : SAB H X1) {S S' : Type} [CommRing S] [CommRing S']
    (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X1) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t'.G)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (act' : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S')
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' x1 d x' m) (wP : PrimTyG t) (wP' : PrimTyG t')
    (φ : t'.G.left ⟶ t.G.left) (w : LB.Iso t'.PP.L (t.PP.L.pull φ)) (m : ℕ)
    (ha : x' m ≫ t'.act.act H.w0 =
      Formalism.L2.Pj.homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act' H.w0 p.2)) ≫ x' m)
    (c : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' x1 d x' m (0 : Fin 2),
      jptG t' x1 d x' m (1 : Fin 2)] J ≫ φ) (cε 2)))
    (hc : LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' x1 d x' m (0 : Fin 2),
      jptG t' x1 d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L φ _ _ c))
    (cP : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ φ) primε))
    (hP₁ : LB.Gen.Corr t.PP.L _ _ _ _ cP (LB.pullGen t.PP.L _ _ wP φ))
    (hP₂ : LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L φ _ _ cP))
    {Z : Scheme.{0}} (r : Z ⟶ (jOG x1 d m 1).left) (s : Z ⟶ (jOG x0 d m 1).left) (z : Z)
    {J : (Z ⟶ t.G.left) → t.PP.L.ι} {J' : (Z ⟶ t'.G.left) → t'.PP.L.ι} (hJ : Good t.PP.L z J)
    (hJ' : Good t'.PP.L z J') (hx : s ≫ (x m).left = (r ≫ (x' m).left) ≫ φ)
    (he : val (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε := cε 2) (e m)
        (s ≫ (Formalism.L2.Pj.homAt x0 (sL m (act H.w0))).left) z J =
      val c (r ≫ (Formalism.L2.Pj.homAt x1 (sL m (act' H.w0))).left) z J) :
    val (eLG t x0 d x act e wP m) s z J =
      Geo.Tor.gw w (r ≫ (x' m).left) z (J ((r ≫ (x' m).left) ≫ φ)) (J' (r ≫ (x' m).left)) *
        val (eLG t' x1 d x' act' e' wP' m) r z J' := by
  have p₁ := (congrArg (fun q => val wP q z J) hx).trans ((val_pull hJ wP φ _).symm.trans
    ((val_corr hJ hP₁ _).symm.trans (GlobalTheory.RigOriginPull.val_tie w _ _ wP' cP hP₂ _ z hJ hJ')))
  have p₂ := he.trans (GlobalTheory.RigOriginPull.val_tie w _ _ (e' m) c hc _ z hJ hJ')
  have q := prod_points t' x1 d x' (act' H.w0) m ha
    (fun f => Geo.Tor.gw w (r ≫ f) z (J ((r ≫ f) ≫ φ)) (J' (r ≫ f)))
  refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans p₁)
    ((val_pull hJ _ _ _).trans p₂)).trans ((_root_.mul_mul_mul_comm _ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)) q
    · exact congrArg (fun f => Geo.Tor.gw w f z (J (f ≫ φ)) (J' f) ^ primε k) (Category.assoc _ _ _)
    · exact congrArg (fun f => Geo.Tor.gw w f z (J (f ≫ φ)) (J' f) ^ cε 2 k) (Category.assoc _ _ _)
  · exact ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _) (val_pull hJ' _ _ _))).symm

theorem exists_frame {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (m : ℕ) (he : (e m).IsGen) (hP : wP.IsGen)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act H.w0 p.2)) ≫ x m) :
    ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left) fun _ => (1 : ℤ)),
      τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι),
        Good t.PP.L z J → val τ r z J = val (eLG t x0 d x act e wP m) r z J := by
  refine exists_gen t.PP.isLB ?_ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hP _) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ he _))
  intro U _ hU
  rw [Fintype.prod_sum_type, Fin.prod_univ_one, zpow_one]
  exact prod_points t x0 d x (act H.w0) m ha hU

theorem act_of_map {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S))
    (mp : SABMap t' t x0) {A : Type} [CommRing A] [Algebra S A] (x : overAt x0 A ⟶ t.G)
    (x' : overAt (𝟙 (Sp S)) A ⟶ t'.G) (hx : x'.left ≫ mp.φ = x.left) (a : 𝓞 E) (σ : A →ₐ[S] A)
    (h : x ≫ t.act.act a = Formalism.L2.Pj.homAt x0 σ ≫ x) :
    x' ≫ t'.act.act a = Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ ≫ x' := by
  apply Over.OverMorphism.ext
  refine mp.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have h' : x.left ≫ (t.act.act a).left = (Formalism.L2.Pj.homAt x0 σ).left ≫ x.left := congrArg (fun q => q.left) h
  have hx' : x'.left ≫ mp.cm.F = x.left := hx
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, mp.act a, ← Category.assoc, hx']
  exact h'

end GlobalTheory.PlaceInt.FrameTie


open GlobalTheory.PlaceInt.FrameTie GermD in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PlaceInt.frameTie_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ _ Tc io yI C
  letI := io.toAlgebra
  obtain ⟨⟨-, hact, -⟩, x', hx2, hx1, ⟨e', he'⟩, wP', hPg, ⟨cP₂, hP₂, hP₂'⟩, cP₁, hP₁, hP₁'⟩ := C.gen
  have ha : ∀ m, x' m ≫ C.I.t'.act.act H.w0 = Formalism.L2.Pj.homAt (𝟙 (Sp Tc.Fr))
      (jetSubstP m fun p : Fin 1 × Fin C.ch.d => psTrunc m (C.ch.B.A.act H.w0 p.2)) ≫ x' m := fun m =>
    act_of_map Xo.univ.t yI.1.x C.I.t' C.I.m1 (C.ch.x m) (x' m) (hx1 m) H.w0 _ (C.ch.chart.act m H.w0)
  choose τ _ hτ using fun m => exists_frame C.I.t' (𝟙 (Sp Tc.Fr)) C.ch.d x' C.ch.B.A.act e' wP' m (he' m).1 hPg (ha m)
  refine ⟨x', hx1, hx2, τ, fun m Z r z J J' J'' hJ hJ' hJ'' => ?_⟩
  obtain ⟨-, ⟨c₂, hc₂, hc₂'⟩, c₁, hc₁, hc₁'⟩ := he' m
  rw [Category.comp_id, hτ m Z r z J' hJ']
  constructor
  · refine val_eLG_tie Xo.univ.t C.I.t' yI.1.x (𝟙 (Sp Tc.Fr)) C.ch.d C.ch.x x' C.ch.B.A.act C.ch.B.A.act C.ch.e e'
      C.ch.wP wP' C.I.m1.φ C.I.w1 m (ha m) c₁ hc₁' cP₁ hP₁ hP₁' r r z hJ hJ' ?_ (val_corr hJ hc₁ _).symm
    exact (congrArg (r ≫ ·) (hx1 m).symm).trans (Category.assoc _ _ _).symm
  · refine val_eLG_tie C.I.G C.I.t' (𝟙 (Sp Tc.V)) (𝟙 (Sp Tc.Fr)) C.ch.d C.xT x' C.actT C.ch.B.A.act C.eT e'
      C.wPT wP' C.I.m2.φ C.I.w2 m (ha m) c₂ hc₂' cP₂ hP₂ hP₂' r _ z hJ'' hJ' ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (hx2 m).symm).trans (Category.assoc _ _ _).symm)
    · refine Eq.symm ((val_corr hJ'' hc₂ _).trans ((val_pull hJ'' _ _ _).trans ?_))
      refine congrArg (fun q => val (C.eT m) q z J'') ?_
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine congrArg (r ≫ ·) (GlobalTheory.ChartRigBC.subst_jetCoef (algebraMap Tc.V Tc.Fr) (𝟙 _)
        (spMap (algebraMap Tc.V Tc.Fr)) C.ch.d m 2 1 _ _ ?_)
      rintro ⟨i, j⟩
      fin_cases i
      · exact (MvPolynomial.map_X _ _).symm
      · exact (congrArg (psIn C.ch.d m ![0]) (hact H.w0 j)).trans (GlobalTheory.RawChartGermBC.map_psIn _ C.ch.d m _ _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProducts
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem chBound_of_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  intro E _ _ _ H Dw l Xo c _ _ T io y C e ρ w n h k
  unfold nuLocC
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun f => le_iInf fun hf => ?_
  exact (GlobalTheory.RamChartCmp.bound_all_iff_bound_prod C e k P _).2 (h k P hP) f hf

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem hv_eq_chartVal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (k n : ℕ) (F : Fin n → SecN Xo y.x k) (f : Fin n → PS S 1 C.d), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k F P = chartVal C k f P := by
  intro E _ _ _ H Dw l Xo c _ hst nab hnab S _ _ _ y C k n F f hf w P hP
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 S y
  choose f₀ hf₀ using fun b => hex k (F b)
  have e₀ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₀.B.nabVal S C₀.h H.w0 k (f₀ b) C₀.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)
  obtain ⟨N, hN, hA, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c w n P hP
  have h := _root_.GlobalTheory.ChartField.chartVal_indep E H Dw l Xo c hst S y C₀ C k n F f₀ f hf₀ hf w _ hA
  have hu : IsUnit (algebraMap c.F S (N : c.F)) :=
    (IsUnit.mk0 (N : c.F) (Nat.cast_ne_zero.2 hN.ne')).map _
  simp only [chartVal, hs, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc, ← Finset.mul_sum] at h
  simp only [hv, chartVal, e₀]
  exact hu.mul_left_cancel h

end GlobalTheory.PlaceInt
end

