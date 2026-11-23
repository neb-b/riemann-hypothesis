module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecomposition
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace IsotropicPrimary

theorem exists_primary_complement (Z : Type) [CommGroup Z] [Finite Z] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ P Q : Subgroup Z, (∀ u, u ∈ P ↔ ∃ j : ℕ, u ^ (ℓ ^ j) = 1) ∧ Nat.Coprime (Nat.card Q) ℓ ∧
      (Function.Bijective fun y : P × Q => (y.1 : Z) * (y.2 : Z)) ∧
      Nat.card P = ℓ ^ (Nat.card Z).factorization ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨S⟩ : Nonempty (Sylow ℓ Z) := inferInstance
  haveI : (S : Subgroup Z).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime (N := (S : Subgroup Z)) S.card_coprime_index
  refine ⟨S, Q, fun u => ⟨fun hu => ?_, fun hu => ?_⟩, ?_, hQ, S.card_eq_multiplicity⟩
  · obtain ⟨k, hk⟩ := S.isPGroup' ⟨u, hu⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · obtain ⟨j, hj⟩ := hu
    have hp : IsPGroup ℓ (Subgroup.zpowers u) :=
      IsPGroup.of_card_dvd_pow (n := j) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hj)
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    letI := Sylow.unique_of_normal S ‹_›
    have hTS : T = S := Subsingleton.elim _ _
    subst hTS
    exact hT (Subgroup.mem_zpowers u)
  · rw [← hQ.symm.index_eq_card]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 S.not_dvd_index)

theorem epi_spMap_of_fields {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  letI : Algebra K k := β.toAlgebra
  have hff : (CommRingCat.ofHom β).hom.FaithfullyFlat := by
    change Module.FaithfullyFlat K k
    infer_instance
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom β)).2 hff
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def zhSubgroup (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N) (T : Over Xo.X) :
    Subgroup (Fin n → (T ⟶ Xo.univ.t.G)) :=
  have hone : InZh Xo Λ N (1 : Fin n → (T ⟶ Xo.univ.t.G)) := by
    refine ⟨fun b => one_pow _, fun mu _ cm _ i => List.prod_eq_one fun x hx => ?_⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    have := Xo.univ.t.act.hom (cm i j)
    exact MonObj.one_comp _
  have hpow : ∀ (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → ∀ k : ℕ, InZh Xo Λ N (a ^ k) := by
    intro a ha k
    induction k with
    | zero => rw [pow_zero]; exact hone
    | succ k ih => rw [pow_succ]; exact ZhStable.inZh_mul Xo Λ N _ _ ih ha
  { carrier := {a | InZh Xo Λ N a}
    one_mem' := hone
    mul_mem' := fun {a a'} ha ha' => ZhStable.inZh_mul Xo Λ N a a' ha ha'
    inv_mem' := fun {a} ha => by
      have h1 : a ^ (N ^ 2) = 1 := funext ha.1
      have h2 : a⁻¹ = a ^ (N ^ 2 - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hN 2), h1]
      change InZh Xo Λ N a⁻¹
      rw [h2]
      exact hpow a ha _ }

theorem enumeration_bijective (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hz : ∀ i, InZh Xo Λ N (z i))
    (hinj : GeoInj Xo x z) : Function.Injective z ∧ ∀ a, InZh Xo Λ N a → ∃ i, z i = a := by
  refine ⟨fun i j hij => ?_, fun a ha => ?_⟩
  · let g : ptO Xo (spMap (RingHom.id K) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (RingHom.id K)) rfl
    refine hinj K (RingHom.id K) g rfl ?_
    show (fun b => g ≫ z i b) = fun b => g ≫ z j b
    rw [hij]
  · let ψ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
    have hw : ∀ i, InZh Xo Λ N (fun b => g ≫ z i b) := fun i => ZhStable.inZh_comp Xo Λ N g (z i) (hz i)
    obtain ⟨i, hi⟩ := IsotropicEnum.exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x) Λ hΛ hN hle
      (fun i b => g ≫ z i b) hw (hinj (AlgebraicClosure K) ψ g rfl) (fun b => g ≫ a b)
      (ZhStable.inZh_comp Xo Λ N g a ha)
    refine ⟨i, funext fun b => ?_⟩
    haveI := epi_spMap_of_fields ψ
    have hb := congrArg CommaMorphism.left (congrFun hi b)
    simp only [Over.comp_left] at hb
    exact Over.OverMorphism.ext ((cancel_epi (spMap ψ)).1 hb)

end IsotropicPrimary


open IsotropicPrimary in
theorem isotropic_primary_decomposition :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x n Λ N M ℓ hΛ hlev hℓ z hz hinj
  have hN : 0 < N := hlev.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hlev.2.2.trans inf_le_left
  obtain ⟨hzinj, hzon⟩ := enumeration_bijective Xo x Λ hΛ hN hle z hz hinj
  let e : Fin (Λ.zCard N (Dw.p + Dw.q)) → zhSubgroup Xo Λ N hN (ptO Xo x) := fun i => ⟨z i, hz i⟩
  have he : Function.Bijective e :=
    ⟨fun i j h => hzinj (congrArg Subtype.val h), fun u => by
      obtain ⟨i, hi⟩ := hzon u.1 u.2
      exact ⟨i, Subtype.ext hi⟩⟩
  haveI : Finite (zhSubgroup Xo Λ N hN (ptO Xo x)) := Finite.of_surjective e he.2
  obtain ⟨P, Q, hP, hQ, hPQ, hcard⟩ := exists_primary_complement (zhSubgroup Xo Λ N hN (ptO Xo x)) ℓ hℓ
  refine ⟨P, Q, Fintype.ofFinite _, Fintype.ofFinite _, fun p => ((p : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    fun q => ((q : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    (Equiv.ofBijective _ hPQ).trans (Equiv.ofBijective e he).symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p p' h => Subtype.ext (Subtype.ext h)
  · intro u
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨(p : zhSubgroup Xo Λ N hN (ptO Xo x)).2, fun b => ?_⟩
      obtain ⟨j, hj⟩ := (hP _).1 p.2
      refine ⟨j, ?_⟩
      have := congrArg (fun w : zhSubgroup Xo Λ N hN (ptO Xo x) => w.1 b) hj
      simpa using this
    · rintro ⟨hu, hpow⟩
      choose j hj using hpow
      refine ⟨⟨⟨u, hu⟩, (hP _).2 ⟨∑ b, j b, Subtype.ext (funext fun b => ?_)⟩⟩, rfl⟩
      obtain ⟨c, hc⟩ : ℓ ^ j b ∣ ℓ ^ (∑ b, j b) :=
        pow_dvd_pow ℓ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
      rw [hc, pow_mul, hj b, one_pow]
  · refine ⟨Nat.card Q, hQ, fun i b => ⟨?_, ((i : zhSubgroup Xo Λ N hN (ptO Xo x)).2 : InZh Xo Λ N _).1 b⟩⟩
    have := congrArg (fun w : Q => (w : zhSubgroup Xo Λ N hN (ptO Xo x)).1 b) (pow_card_eq_one' (G := Q) (x := i))
    simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply] at this
    exact this
  · intro i i' b
    have h1 : e ((Equiv.ofBijective e he).symm ((i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)))) =
        (i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)) :=
      Equiv.ofBijective_apply_symm_apply e he _
    simp only [Equiv.trans_apply, Equiv.ofBijective_apply]
    exact congrFun (congrArg Subtype.val h1) b
  · rw [@Fintype.card_eq_nat_card P (Fintype.ofFinite P), hcard, ← Nat.card_eq_of_bijective e he, Nat.card_fin]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemRangeOfIsIntegral
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PushIntegral

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}

theorem push_letB (ga : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (v : Fin n → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v) = letB c σ i (ga.mulVec v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [letB, map_sum, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, GlobalTheory.PushHarm.push_X,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_range_of_isIntegral (T : CDVR) (io : c.F →+* T.Fr) {x : c.F} (hi : IsIntegral ℤ x) :
    ∃ y : T.V, algebraMap T.V T.Fr y = io x := by
  obtain ⟨p, hpm, hp⟩ := hi
  have hV : IsIntegral T.V (io x) := by
    refine ⟨p.map (Int.castRingHom T.V), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
      (io.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, hp, map_zero]
  exact IsIntegrallyClosed.isIntegral_iff.1 hV

theorem mem_range_of_smul (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V)) (σ : E →+* ℂ) {x : E}
    (hx : (k : E) * x ∈ (1 : Submodule (𝓞 E) E)) : ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ x) := by
  obtain ⟨s, hs⟩ := Submodule.mem_one.1 hx
  have hi : IsIntegral ℤ (embF c σ (algebraMap (𝓞 E) E s)) :=
    map_isIntegral_int (embF c σ) (NumberField.RingOfIntegers.isIntegral_coe s)
  obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io hi
  obtain ⟨u, hu⟩ := hk.exists_left_inv
  refine ⟨u * y, ?_⟩
  have h1 : algebraMap T.V T.Fr u * (k : T.Fr) = 1 := by
    rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hu, map_one]
  rw [map_mul, hy, hs, map_mul, map_mul, map_natCast, map_natCast, ← _root_.mul_assoc, h1, _root_.one_mul]

theorem coeff_mem (Λ : GenLat E n) (T : CDVR) (io : c.F →+* T.Fr) {k : ℕ} (hk : IsUnit (k : T.V))
    (ga : Matrix (Fin n) (Fin n) E) (hin : ∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ symO c Λ) (m : LtN Dw n →₀ ℕ) :
    (MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P)).coeff m ∈ (algebraMap T.V T.Fr).range := by
  have hle : symO (Dw := Dw) c Λ ≤
      (MvPolynomial.map (σ := LtN Dw n) (algebraMap T.V T.Fr)).range.comap
        ((MvPolynomial.map io).comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c ga).toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, v, hv, rfl⟩)
    · obtain ⟨y, hy⟩ := mem_range_of_isIntegral c T io o.2
      refine ⟨MvPolynomial.C y, ?_⟩
      simp [hy]
    · have h : ∀ j, ∃ y : T.V, algebraMap T.V T.Fr y = io (embF c σ (ga.mulVec v j)) := fun j =>
        mem_range_of_smul c T io hk σ (hin v hv j (Set.mem_univ j))
      choose y hy using h
      refine ⟨∑ j, MvPolynomial.C (y j) * MvPolynomial.X ⟨σ, i, j⟩, ?_⟩
      change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga (letB c σ i v))
      rw [push_letB]
      simp [letB, hy]
  obtain ⟨Q, hQ⟩ := hle hP
  change _ = MvPolynomial.map io (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c ga P) at hQ
  rw [← hQ, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

theorem push_one (P : MvPolynomial (LtN Dw n) c.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push c (1 : Matrix (Fin n) (Fin n) E) P = P := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c (1 : Matrix (Fin n) (Fin n) E) = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨σ, i, j⟩
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push, letB, Matrix.one_apply, apply_ite, ite_mul]
  rw [h]; rfl

theorem aeval_smul_of_degree {J K A : Type} [CommRing K] [CommRing A] [Algebra K A] (t : A) (f : J → A)
    (P : MvPolynomial J K) (d : ℕ) (hP : ∀ s ∈ P.support, (s.sum fun _ e => e) = d) :
    MvPolynomial.aeval (fun i => t * f i) P = t ^ d * MvPolynomial.aeval f P := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hP s hs]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem degree_eq_totalDegree {a : (E →+* ℂ) → ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : RowDeg Dw.mult n c.F a P) : ∀ s ∈ P.support, (s.sum fun _ e => e) = P.totalDegree := by
  classical
  have h : ∀ s ∈ P.support, (s.sum fun _ e => e) = ∑ σ : E →+* ℂ, ∑ i : Fin (Dw.mult σ), a σ i := by
    intro s hs
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP s hs σ i
  intro s hs
  refine le_antisymm (MvPolynomial.le_totalDegree hs) ?_
  exact Finset.sup_le fun s' hs' => ((h s' hs').trans (h s hs).symm).le

end

theorem map_pushL_mem_FFV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (T : CDVR) (io : c.F →+* T.Fr) (k : ℕ) (ga : Matrix (Fin n) (Fin n) E), IsUnit (k : T.V) → (∀ i j, ∑ b, IsCMField.complexConj E (ga b i) * ga b j = if i = j then 1 else 0) → (∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n) → MvPolynomial.map io (pushL c ga P) ∈ FFV (Dw := Dw) T w n ∧ pushL c 1 P = P ∧ ∀ m : ℕ, pushL c ((m : E) • ga) P = MvPolynomial.C ((m : c.F) ^ P.totalDegree) * pushL c ga P := by
  intro E _ _ _ H Dw l c n Λ w P hP T io k ga hk hu hin
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  have hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsUnitary ga := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hu i j
  have hr := GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n ga P (fun τ i => w (τ, i))
  refine ⟨⟨⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io (GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n ga P hU h1),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.rowInv_map io (hr.1 h2), ReciprocityTheory.ChartRestriction.G.PullbackSections.rowDeg_map io (hr.2 h3)⟩,
    coeff_mem c Λ T io hk ga hin h4⟩, push_one c P, fun m => ?_⟩
  rw [map_pow, pushL, pushL, ← aeval_smul_of_degree _ _ P _ (degree_eq_totalDegree c h3)]
  congr 2
  funext ℓ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [_root_.mul_assoc]

end GlobalTheory.PushIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
section
set_option autoImplicit false
open IsLocalRing

namespace GlobalTheory.PlaceInt

section
variable {V : Type} [CommRing V] [IsLocalRing V]

theorem mem_maximalIdeal_mvPowerSeries_iff {τ : Type} (f : MvPowerSeries τ V) :
    f ∈ maximalIdeal (MvPowerSeries τ V) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal V := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

variable [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V]

theorem isAdicComplete_mvPowerSeries_finite (τ : Type) [Finite τ] :
    IsAdicComplete (maximalIdeal (MvPowerSeries τ V)) (MvPowerSeries τ V) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin τ

  have ha : MvPowerSeries.HasSubst
      (fun i : Fin n => (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hb : MvPowerSeries.HasSubst
      (fun t : τ => (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hba : ∀ f : MvPowerSeries (Fin n) V,
      MvPowerSeries.substAlgHom (R := V) hb (MvPowerSeries.substAlgHom (R := V) ha f) = f := by
    intro f
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun i : Fin n => MvPowerSeries.substAlgHom (R := V) hb
        (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) = MvPowerSeries.X := by
      funext i
      rw [MvPowerSeries.substAlgHom_X, Equiv.apply_symm_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  have hab : ∀ g : MvPowerSeries τ V,
      MvPowerSeries.substAlgHom (R := V) ha (MvPowerSeries.substAlgHom (R := V) hb g) = g := by
    intro g
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun t : τ => MvPowerSeries.substAlgHom (R := V) ha
        (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) = MvPowerSeries.X := by
      funext t
      rw [MvPowerSeries.substAlgHom_X, Equiv.symm_apply_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  let E : MvPowerSeries (Fin n) V ≃+* MvPowerSeries τ V :=
    { toFun := MvPowerSeries.substAlgHom (R := V) ha
      invFun := MvPowerSeries.substAlgHom (R := V) hb
      left_inv := hba
      right_inv := hab
      map_mul' := map_mul _
      map_add' := map_add _ }
  have := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries V n
  exact GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv E

variable {σ τ : Type} [Finite σ] [Finite τ]

theorem exists_algHom_evC (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  refine (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, ?_⟩)).1 inferInstance V
  rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]
  exact ha j

private theorem mvPowerSeries_algHom_ext_of_X_eq (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ ψ' : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (h : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (h' : ∀ j, ψ' (MvPowerSeries.X j) = a j) : ψ = ψ' := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, by rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]; exact ha j⟩)).2
    inferInstance V ψ.toRingHom ψ'.toRingHom
    (fun t => by
      show ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)
      have hC : (MvPowerSeries.C t : MvPowerSeries σ V) = algebraMap V (MvPowerSeries σ V) t := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hC, ψ.commutes, ψ'.commutes]) h h'
  exact AlgHom.ext fun f => RingHom.congr_fun key f

theorem evC_eq_algHom (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (hψ : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (f : MvPowerSeries σ V) : evC a f = ψ f := by
  have h : ∃ φ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, φ (MvPowerSeries.X j) = a j :=
    ⟨ψ, hψ⟩
  rw [evC, dite_eq_left h, mvPowerSeries_algHom_ext_of_X_eq a ha h.choose ψ h.choose_spec hψ]

theorem constantCoeff_evC_mem (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) (f : MvPowerSeries σ V)
    (hf : MvPowerSeries.constantCoeff f ∈ maximalIdeal V) :
    MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
  rw [evC_eq_algHom a ha ψ hψ f]

  let χ₁ : MvPowerSeries σ V →+* ResidueField V :=
    (residue V).comp (MvPowerSeries.constantCoeff.comp ψ.toRingHom)
  let χ₂ : MvPowerSeries σ V →+* ResidueField V := (residue V).comp MvPowerSeries.constantCoeff
  have hC : ∀ t : V, ψ (MvPowerSeries.C t) = MvPowerSeries.C t := fun t => by
    have := ψ.commutes t
    rwa [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (ResidueField V) ⊥ σ (fun _ => 0)
    (fun _ => ⟨1, by simp⟩)).2 inferInstance V χ₁ χ₂
    (fun t => by simp [χ₁, χ₂, hC])
    (fun j => by
      simp only [χ₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψ]
      exact (residue_eq_zero_iff _).2 (ha j))
    (fun j => by simp [χ₂])
  have hf' := RingHom.congr_fun key f
  simp only [χ₁, χ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf'
  rw [← residue_eq_zero_iff, hf']
  exact (residue_eq_zero_iff _).2 hf

end

theorem evC_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  intro V _ _ _ _ _ σ τ ρ _ _ _ a ha
  refine ⟨?_, fun f hf => constantCoeff_evC_mem a ha f hf, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
    exact ⟨ψ, hψ, fun f => evC_eq_algHom a ha ψ hψ f⟩
  · intro h0 f
    have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    rw [evC_eq_algHom a ha (MvPowerSeries.substAlgHom (R := V) hs)
      (fun j => MvPowerSeries.substAlgHom_X hs j) f]
    exact MvPowerSeries.substAlgHom_apply hs f
  · intro b hb f
    obtain ⟨ψa, hψa⟩ := exists_algHom_evC a ha
    obtain ⟨ψb, hψb⟩ := exists_algHom_evC b hb
    have hc : ∀ j, MvPowerSeries.constantCoeff (evC b (a j)) ∈ maximalIdeal V :=
      fun j => constantCoeff_evC_mem b hb (a j) (ha j)

    rw [evC_eq_algHom (fun j => evC b (a j)) hc (ψb.comp ψa)
      (fun j => by rw [AlgHom.comp_apply, hψa, evC_eq_algHom b hb ψb hψb]) f,
      evC_eq_algHom a ha ψa hψa, evC_eq_algHom b hb ψb hψb, AlgHom.comp_apply]

end GlobalTheory.PlaceInt
end

