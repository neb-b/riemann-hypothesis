module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsThroughZeroLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factors_through_zero_locus : ∀ (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg)) (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)), (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔ ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  first | (exact @GlobalTheory.FormsLocus.factors_quot_iff) | (exact GlobalTheory.FormsLocus.factors_quot_iff) | (intros; apply GlobalTheory.FormsLocus.factors_quot_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

namespace GlobalTheory.CompHt.PointLow

set_option autoImplicit false in
open MvPolynomial in
private lemma natDegree_aeval_le_totalDegree_of_natDegree_le_one {R S σ : Type} [CommRing R] [CommRing S] [Algebra R S]
    (p : MvPolynomial σ R) (s : σ → Polynomial S) (hs : ∀ i, (s i).natDegree ≤ 1) :
    (MvPolynomial.aeval s p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Polynomial.natDegree_mul_le.trans ?_
  have h0 : (algebraMap R (Polynomial S) (p.coeff d)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add, Finsupp.prod]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hs i)


set_option autoImplicit false in
open MvPolynomial in
theorem _root_.GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K)
    (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → _root_.GlobalTheory.ChowHt.IsChowFormInt (_root_.GlobalTheory.CompHt.coneIdeal K y) 0 δ f →
    Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  intro K _ _ N δ y j f hyj hf
  classical
  set E := IntermediateField.adjoin K (Set.range y) with hE
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [← AlgHom.card K E (AlgebraicClosure K)]
  let yE : Fin N → E := fun k => ⟨y k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩
  let pt : (E →ₐ[K] AlgebraicClosure K) → Fin N → AlgebraicClosure K := fun σ k => σ (yE k)
  have hpj : ∀ σ, pt σ j = 1 := by
    intro σ
    have : yE j = 1 := Subtype.ext hyj
    simp only [pt, this, map_one]
  have hzero : ∀ σ, ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, MvPolynomial.aeval (pt σ) g = 0 := by
    intro σ g hg
    have hy := _root_.GlobalTheory.CompHt.aeval_eq_zero_of_mem_coneIdeal hg
    have hE0 : MvPolynomial.aeval yE g = 0 := by
      apply Subtype.ext
      have := MvPolynomial.comp_aeval_apply yE E.val g
      show E.val (MvPolynomial.aeval yE g) = E.val 0
      rw [this, map_zero]
      exact hy
    have := MvPolynomial.comp_aeval_apply yE σ g
    rw [hE0, map_zero] at this
    exact this.symm
  have hinj : Function.Injective pt := by
    intro σ τ h
    refine IntermediateField.adjoin_algHom_ext K fun x hx => ?_
    obtain ⟨k, rfl⟩ := hx
    exact congrFun h k
  set fΩ := MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f with hfΩ
  have hfΩ0 : fΩ ≠ 0 := by
    intro h
    exact hf.ne_zero (MvPolynomial.map_injective _ (algebraMap K (AlgebraicClosure K)).injective
      (by rw [← hfΩ, h, map_zero]))
  let lin : (E →ₐ[K] AlgebraicClosure K) → (E →ₐ[K] AlgebraicClosure K) →
      MvPolynomial (Fin (0 + 1) × Fin N) (AlgebraicClosure K) :=
    fun σ τ => ∑ k, X (0, k) * C (pt σ k - pt τ k)
  have hlin_eval : ∀ σ τ (a : Fin (0 + 1) × Fin N → AlgebraicClosure K),
      eval a (lin σ τ) = ∑ k, a (0, k) * pt σ k - ∑ k, a (0, k) * pt τ k := by
    intro σ τ a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [lin, map_sum, eval_mul, eval_X, eval_C, ← Finset.sum_sub_distrib, mul_sub]
  set pairs := Finset.univ.filter fun st : (E →ₐ[K] AlgebraicClosure K) × (E →ₐ[K] AlgebraicClosure K) =>
    st.1 ≠ st.2 with hpairs
  set Q := fΩ * ∏ st ∈ pairs, lin st.1 st.2 with hQ
  have hQ0 : Q ≠ 0 := by
    refine mul_ne_zero hfΩ0 (Finset.prod_ne_zero_iff.mpr fun st hst => ?_)
    have hne : st.1 ≠ st.2 := (Finset.mem_filter.mp hst).2
    have hpne : pt st.1 ≠ pt st.2 := fun h => hne (hinj h)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hpne
    intro h0
    have := congrArg (eval (Pi.single (0, k) 1)) h0
    rw [hlin_eval, map_zero] at this
    simp only [Pi.single_apply, Prod.mk.injEq, true_and, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact hk (sub_eq_zero.mp this)
  obtain ⟨a, ha⟩ : ∃ a, eval a Q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  have hfa : eval a fΩ ≠ 0 := fun h => ha (by rw [hQ, eval_mul, h, zero_mul])
  let c : (E →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun σ => ∑ k, a (0, k) * pt σ k
  have hdist : Function.Injective c := by
    intro σ τ h
    by_contra hne
    apply ha
    rw [hQ, eval_mul, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (σ, τ))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) ?_)
    rw [hlin_eval]
    exact sub_eq_zero.mpr h
  let s : Fin (0 + 1) × Fin N → Polynomial (AlgebraicClosure K) :=
    fun ik => Polynomial.C (a ik) + if ik.2 = j then Polynomial.X else 0
  set g := MvPolynomial.aeval s f with hg
  have heval : ∀ t, g.eval t = MvPolynomial.aeval (fun ik => a ik + if ik.2 = j then t else 0) f := by
    intro t
    have := MvPolynomial.comp_aeval_apply s
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K) f
    rw [hg, ← Polynomial.coe_aeval_eq_eval, show (Polynomial.aeval t) (MvPolynomial.aeval s f) =
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K)
        (MvPolynomial.aeval s f) from rfl, this]
    refine congrArg (fun v => MvPolynomial.aeval v f) (funext fun ik => ?_)
    simp only [s]
    split_ifs <;> simp
  have hg0 : g ≠ 0 := by
    intro h
    have := heval 0
    rw [h, Polynomial.eval_zero] at this
    have h2 : (fun ik : Fin (0 + 1) × Fin N => a ik + if ik.2 = j then (0 : AlgebraicClosure K) else 0) = a := by
      funext ik; split_ifs <;> simp
    rw [h2] at this
    apply hfa
    rw [hfΩ, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this.symm
  have hroot : ∀ σ, g.eval (-c σ) = 0 := by
    intro σ
    rw [heval]
    refine (hf.zero_iff _).mpr
      ⟨pt σ, fun h => by simpa [hpj σ] using congrFun h j, hzero σ, fun i => ?_⟩
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hpj σ, mul_one]
    simp [c]
  have hcard : Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun σ => -c σ) (fun σ _ => ?_) ?_
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hg0]
      exact hroot σ
    · intro σ _ τ _ h
      exact hdist (neg_injective h)
  have hhom := ((_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.mp
    hf.homog).isHomogeneous)
  have htot : f.totalDegree = δ := by
    rw [hhom.totalDegree hf.ne_zero]
    simp
  calc Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := hcard
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ f.totalDegree := natDegree_aeval_le_totalDegree_of_natDegree_le_one f s fun ik => by
        simp only [s]
        split_ifs
        · exact (Polynomial.natDegree_add_le _ _).trans (by simp)
        · simp
    _ = δ := htot

end GlobalTheory.CompHt.PointLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicGLMemIntegralCofinitePlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)), {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite := by
  first | exact @GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | exact GlobalTheory.GLFinPlaces.gl_mem_int_cofinite | (intros; apply GlobalTheory.GLFinPlaces.gl_mem_int_cofinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsion
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory

namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
attribute [local instance] zuAlgebra

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

theorem val_splitTorusPoint (t : Multiplicative X →* kˣ) (b : X) :
    SplitTorus.val (splitTorusPoint t) b =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd b) : k) := by
  have h : (torusIso k X).hom.appTop.hom (chi X b) =
      (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k X))).inv.hom (AddMonoidAlgebra.single b 1) := by
    have := torusGamma_chi k X b
    rw [torusGamma, CommRingCat.comp_apply] at this
    rw [← this]
    simp
  rw [SplitTorus.val_eq, splitTorusPoint_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h,
    SplitTorus.specMap_appTop_apply]
  simp [torusEval_single]

theorem splitTorusPoint_comp_torusMap (t : Multiplicative X →* kˣ) (φ : X →+ X) :
    splitTorusPoint t ≫ SplitTorus.torusMap (Sp k) φ =
      splitTorusPoint (t.comp (AddMonoidHom.toMultiplicative φ)) :=
  SplitTorus.hom_ext fun b => by
    rw [SplitTorus.val_comp_torusMap, val_splitTorusPoint, val_splitTorusPoint]
    rfl

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

theorem finite_of_isClosed_torusZariski_of_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X]
    (hdiv : ∀ r : O, r ≠ 0 → ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : O)) {π : O} (hπ0 : π ≠ 0)
    (hπ : ¬ IsUnit π) {H : Subgroup (Multiplicative X →* kˣ)}
    (hH : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)))
    (hstab : ∀ (a : O), ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom X a)) ∈ H)
    (htors : ∀ s ∈ H,
      s.comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom X π)) = 1 → s = 1) :
    Finite H := by
  let K : Submodule O X :=
    { carrier := {x | ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1}
      add_mem' := fun {a b} ha hb s hs => by rw [ofAdd_add, map_mul, ha s hs, hb s hs, _root_.mul_one]
      zero_mem' := fun s _ => map_one s
      smul_mem' := fun a x hx s hs => hx _ (hstab a s hs) }
  have hK : ∀ x, x ∈ K ↔ ∀ s ∈ H, s (Multiplicative.ofAdd x) = 1 := fun x => Iff.rfl
  let N : Submodule O X := K ⊔ Ideal.span {π} • ⊤
  have hπN : ∀ x : X, π • x ∈ N := fun x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial)
  haveI : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  have hN : (⊤ : Submodule O X) ≤ N := by
    intro x _
    by_contra hx
    obtain ⟨m, hm0, c, hc⟩ := hdiv π hπ0
    have hmQ : ∀ q : X ⧸ N, m • q = 0 := fun q => by
      obtain ⟨y, rfl⟩ := N.mkQ_surjective q
      rw [← Int.cast_smul_eq_zsmul O, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        hc, mul_smul]
      exact hπN _
    have hmQ' : ∀ q : Multiplicative (X ⧸ N), q ^ m.natAbs = 1 := fun q => by
      have h1 : (m.natAbs : ℤ) • q.toAdd = 0 := by
        rcases Int.natAbs_eq m with h | h
        · rw [← h]; exact hmQ _
        · rw [show (m.natAbs : ℤ) = -m by omega, neg_smul, hmQ, neg_zero]
      rw [natCast_zsmul] at h1
      exact congrArg Multiplicative.ofAdd h1
    haveI : Module.Finite ℤ (X ⧸ N) :=
      Module.Finite.of_surjective N.mkQ.toAddMonoidHom.toIntLinearMap N.mkQ_surjective
    haveI : Finite (X ⧸ N) := Module.finite_of_fg_torsion _ fun q =>
      ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm0⟩, hmQ q⟩
    have hexp : Monoid.exponent (Multiplicative (X ⧸ N)) ≠ 0 := Monoid.exponent_ne_zero_of_finite
    haveI : NeZero ((Monoid.exponent (Multiplicative (X ⧸ N)) : ℕ) : k) := ⟨Nat.cast_ne_zero.2 hexp⟩
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Multiplicative (X ⧸ N)) k (a := Multiplicative.ofAdd (N.mkQ x))
      (by simpa using hx)
    let t : Multiplicative X →* kˣ := φ.comp (AddMonoidHom.toMultiplicative N.mkQ.toAddMonoidHom)
    have ht : ∀ y, t y = φ (Multiplicative.ofAdd (N.mkQ y.toAdd)) := fun y => rfl
    have htH : t ∈ H := mem_of_isClosed_torusZariski hH fun y hy => by
      have : N.mkQ y.toAdd = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_left ((hK _).2 hy)
      rw [ht, this, ofAdd_zero, map_one]
    have ht1 : t = 1 := htors t htH (MonoidHom.ext fun y => by
      have : N.mkQ (π • y.toAdd) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hπN _
      change t (Multiplicative.ofAdd (π • y.toAdd)) = 1
      rw [ht, toAdd_ofAdd, this, ofAdd_zero, map_one])
    exact hφ (by simpa [ht] using DFunLike.congr_fun ht1 (Multiplicative.ofAdd x))
  obtain ⟨r, hr, hrK⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {π}) (N := K) (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl hN
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hπ
    rw [zero_sub, Ideal.mem_span_singleton] at hr
    exact isUnit_of_dvd_one ((dvd_neg).1 hr)
  obtain ⟨m, hm0, c, hc⟩ := hdiv r hr0
  have hmK : ∀ x : X, m • x ∈ K := fun x => by
    rw [← Int.cast_smul_eq_zsmul O, hc, mul_smul]
    exact hrK (Submodule.smul_mem_pointwise_smul _ r ⊤ trivial)
  have hmH : ∀ s ∈ H, s ^ m.natAbs = 1 := fun s hs => by
    have h1 : s ^ m = 1 := MonoidHom.ext fun y => by
      have := (hK _).1 (hmK y.toAdd) s hs
      rw [ofAdd_zsmul, map_zpow, ofAdd_toAdd] at this
      rw [MonoidHom.zpow_apply, this, MonoidHom.one_apply]
    exact pow_natAbs_eq_one.2 h1
  exact (finite_setOf_pow_eq_one_torus (R := k) (X := X) (Int.natAbs_ne_zero.2 hm0)).subset
    (t := (H : Set (Multiplicative X →* kˣ))) fun s hs => hmH s hs

end TorusPiTorsion
end GlobalTheory

namespace GlobalTheory
namespace TorusPiTorsion

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

theorem exists_int_dvd (E : Type) [Field E] [NumberField E] (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ r ∣ (m : 𝓞 E) := by
  refine ⟨(Ideal.absNorm (Ideal.span {r}) : ℤ), ?_, ?_⟩
  · rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hr
  · rw [Int.cast_natCast, ← Ideal.mem_span_singleton]
    exact Ideal.absNorm_mem _

theorem finite_of_isClosed_of_no_pi_torsion :
    ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (act : OAct (𝓞 E) (splitTorus (Sp k) X)) (π : 𝓞 E), π ≠ 0 → ¬ IsUnit π →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) →
        Finite C := by
  intro E _ _ k _ _ _ X _ _ _ act π hπ0 hπ C Z hZ hC hstab htors
  have hφ : ∀ a, ∃ φ : X →+ X, act.act a = SplitTorus.torusMap (Sp k) φ := fun a => by
    haveI := act.hom a
    exact SplitTorus.exists_eq_torusMap _
  choose φ hφ using hφ
  have hinj : ∀ {ψ ψ' : X →+ X}, SplitTorus.torusMap (Sp k) ψ = SplitTorus.torusMap (Sp k) ψ' →
      ψ = ψ' := fun h => SplitTorus.torusMap_injective h
  have hone : φ 1 = AddMonoidHom.id X := hinj (by rw [← hφ, act.one, SplitTorus.torusMap_id])
  have hmul : ∀ a b, φ (a * b) = (φ a).comp (φ b) := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_comp, ← hφ, ← hφ, act.mul])
  have hadd : ∀ a b, φ (a + b) = φ a + φ b := fun a b =>
    hinj (by rw [← hφ, SplitTorus.torusMap_add, ← hφ, ← hφ, act.add])
  let ρ : 𝓞 E →+* AddMonoid.End X :=
    { toFun := φ
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        have h' : φ 0 = 0 := by simpa using h.symm
        exact h'
      map_add' := hadd }
  letI : Module (𝓞 E) X := Module.compHom X ρ
  have hsmul : ∀ (a : 𝓞 E) (x : X), a • x = φ a x := fun a x => rfl
  let e := splitTorusPointEquiv (k := k) (X := X)
  have hpt : ∀ (s : Multiplicative X →* kˣ) (a : 𝓞 E), e s ≫ act.act a =
      e (s.comp (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom X a))) := by
    intro s a
    rw [hφ a]
    exact splitTorusPoint_comp_torusMap s (φ a)
  let H := C.comap e.toMonoidHom
  have hcl : IsClosed[torusZariski k X] (H : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_smul (k := k) (O := 𝓞 E) (X := X)
    (exists_int_dvd E) hπ0 hπ hcl
    (fun a s hs => by
      change e _ ∈ C
      rw [← hpt]
      exact hstab a _ hs)
    (fun s hs h1 => e.injective (by
      rw [map_one]
      refine htors _ hs ?_
      change e s ≫ act.act π = 1
      rw [hpt, h1, map_one]))
  have e' : H ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h

end TorusPiTorsion
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicBoundedPolynomials
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_bounded_polynomials : ∀ (K : Type) [Field K] [NumberField K] (d D : ℕ) (B : ℝ), 0 < D → {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧ ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  first | (exact @GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (exact GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral) | (intros; apply GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedImageInFinitelyGeneratedSubgroupStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup : ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Φ : V →+ E), (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) → ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) → ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  first | (exact @GlobalTheory.finite_of_bounded_image_closure_finset) | (exact GlobalTheory.finite_of_bounded_image_closure_finset) | (intros; apply GlobalTheory.finite_of_bounded_image_closure_finset  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (D' : PLat D.O D.inv) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : D'.La →+ (Fin D.g → ℂ)), IsPeriod D' ρ Q → ∀ τ : D.F →+* ℂ, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ) + Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) ((starRingEnd ℂ).comp τ)) = D.m * D.n := by
  first | exact @GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | exact GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | (intros; apply GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHomStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntV_one_tmul : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  first | (exact @GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (exact GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually) | (intros; apply GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermConstantsEqAlongAffineSpaceSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_constants_eq_along_affineSpace_square : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  first | (exact @GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (exact GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C) | (intros; apply GlobalTheory.FormsLocus.germ_cstT_eq_germ_ringOf_C <;> assumption)
end

