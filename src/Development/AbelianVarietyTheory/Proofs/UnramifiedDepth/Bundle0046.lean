module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusLiftEmbeddingsUnit
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0009
public import Formalism.DropLevelBounds.Statement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEmbeddingCongrIntegralCharacter
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ResidueChar

theorem exists_pow_of_finite_field {K k : Type} [Field K] [Finite K] [CommRing k] [IsDomain k]
    (l : ℕ) [Fact l.Prime] [CharP K l] (f g : K →+* k) :
    ∃ j : ℕ, ∀ y, g y = f y ^ l ^ j := by
  classical
  have := Fintype.ofFinite K
  have hmem : ∀ y, g y ∈ f.range := fun y => by
    have h1 : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) =
        ∏ a : K, (Polynomial.X - Polynomial.C a) := by
      have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
        Polynomial.monic_X_pow_sub (by
          rw [Polynomial.degree_X]; exact_mod_cast Fintype.one_lt_card)
      have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
        rw [FiniteField.roots_X_pow_card_sub_X,
          Polynomial.natDegree_X_pow_sub_X (R := K) Fintype.one_lt_card]
        rfl)
      rw [← this, FiniteField.roots_X_pow_card_sub_X]
      rfl
    have h2 := congrArg (Polynomial.eval₂RingHom f (g y)) h1
    rw [map_prod] at h2
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
    rw [← map_pow, FiniteField.pow_card, sub_self] at h2
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h2.symm
    exact ⟨a, (sub_eq_zero.1 ha).symm⟩
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩
  let s : K →+* K := e.symm.toRingHom.comp (g.codRestrict f.range hmem)
  have hs : ∀ y, f (s y) = g y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict f.range hmem y))
  let := ZMod.algebra K l
  let s' : K →ₐ[ZMod l] K := { s with
    commutes' := fun r => DFunLike.congr_fun
      (Subsingleton.elim (s.comp (algebraMap (ZMod l) K)) (algebraMap (ZMod l) K)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) K).2 s'
  refine ⟨j, fun y => ?_⟩
  have : s y = y ^ l ^ (j : ℕ) := by
    have h := DFunLike.congr_fun hj y
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h
    exact h.symm
  rw [← hs, this, map_pow]

theorem exists_eq_of_ker_le {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) [Fact l.Prime] [CharP k l] (φ : ZMod d → (O →+* k))
    (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (g : O →+* k) (hg : ∀ x, φ 0 x = 0 → g x = 0) :
    ∃ a, ∀ x, g x = φ a x := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← TeichSeq.frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  have : Finite (φ 0).range := hfin
  let : Field (φ 0).range := (Finite.isField_of_domain _).toField
  let g' : (φ 0).range →+* k :=
    (φ 0).rangeRestrict.liftOfSurjective (φ 0).rangeRestrict_surjective
      ⟨g, fun x hx => hg x (congrArg Subtype.val (RingHom.mem_ker.1 hx))⟩
  have hg' : ∀ x, g' ((φ 0).rangeRestrict x) = g x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  obtain ⟨j, hj⟩ := exists_pow_of_finite_field l (φ 0).range.subtype g'
  refine ⟨0 + (j : ZMod d), fun x => ?_⟩
  rw [TeichSeq.frob_iter l φ h, ← hg', hj]
  rfl


open TeichSeq in
theorem main : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, (∀ a, V.MM (em a x)) → V.MM (ψ x)) → ∃ a, ∀ x, V.MM (ψ x - em a x) := by
  intro C _ V O _ d _ em hint hfrob ψ hψ hker
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  let π : intRing V →+* intRing V ⧸ maxId V := Ideal.Quotient.mk _
  let e : ZMod d → (O →+* intRing V) := fun a => (em a).codRestrict (intRing V) (hint a)
  let φ : ZMod d → (O →+* intRing V ⧸ maxId V) := fun a => π.comp (e a)
  let p : O →+* intRing V := ψ.codRestrict (intRing V) hψ
  have hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w) := fun u w => Ideal.Quotient.eq
  have hπ0 : ∀ u : intRing V, π u = 0 ↔ V.MM (u : C) := fun u => Ideal.Quotient.eq_zero_iff_mem
  have hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l := fun a x => by
    show π (e (a + 1) x) = π (e a x) ^ V.l
    rw [← map_pow, hπ]
    exact hfrob a x
  have : CharP (intRing V ⧸ maxId V) V.l := by
    refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
    rw [← map_natCast π, hπ0]
    simpa using mm_of_ge_one V VF.ge_l
  obtain ⟨a, ha⟩ := exists_eq_of_ker_le V.l φ hφ (π.comp p) (fun x hx => by
    refine (hπ0 (p x)).2 (hker x fun a => (hπ0 (e a x)).1 ?_)
    have := frob_iter V.l φ hφ 0 x a.val
    rw [hx, zero_pow (pow_ne_zero _ V.l_prime.ne_zero)] at this
    show φ a x = 0
    simpa using this)
  exact ⟨a, fun x => (hπ (p x) (e a x)).1 (ha x)⟩

end GlobalTheory.ResidueChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfTorsionCharacters
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CharGerm

section Series

variable {R₀ κ : Type} [CommRing R₀]

end Series

section Torsion

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
      ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)





end Torsion

section Value

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)

lemma comp_χ_of_le {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ} (h : m ≤ n)
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  induction n, h using Nat.le_induction with
  | base => rw [torsion_hom_ext huv]
  | succ n hmn ih =>
    have h1 : (u ≫ torsion.ι G (p ^ m)) ^ (p ^ n) = 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, pow_mul, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, one_pow]
    rw [ih (torsionLift _ h1) (torsionLift_ι _ _).symm]
    exact χ.compat n _ _ _ (by rw [torsionLift_ι, huv])

lemma comp_χ_eq {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ}
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by
  rcases le_total m n with h | h
  · exact comp_χ_of_le χ h u v huv
  · exact (comp_χ_of_le χ h v u huv.symm).symm


end Value

end CharGerm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
section
noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.GaugeCocycle ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.RowVal

open MvPowerSeries

variable {C : Type} [Field C]

theorem mvExp_eq_subst [CharZero C] {σ : Type} {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    mvExp F = PowerSeries.subst F (PowerSeries.exp C) := by
  classical
  ext m
  have hS : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · show (∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C)) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    rw [Function.mem_support] at hk
    by_contra hk'
    apply hk
    have h1 : m.degree < k := by simpa using hk'
    have h0 : coeff m (F ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hF)
      exact_mod_cast h1
    rw [h0, smul_zero]

theorem mvExp_add [CharZero C] {σ : Type} {F G : MvPowerSeries σ C} (hF : constantCoeff F = 0)
    (hG : constantCoeff G = 0) : mvExp (F + G) = mvExp F * mvExp G := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst hG, mvExp_eq_subst (by rw [map_add (f := _), hF, hG, add_zero]),
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hF hG]

theorem mvExp_zero' [CharZero C] {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  rw [mvExp_eq_subst (map_zero _), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]

theorem mvExp_sum [CharZero C] {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C}
    (hF : ∀ i, constantCoeff (F i) = 0) : mvExp (∑ i ∈ s, F i) = ∏ i ∈ s, mvExp (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero']
  | insert a s ha ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert ha, Finset.prod_insert ha, mvExp_add (hF a) (by simp [map_sum, hF]), ih]

theorem cc_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (F : MvPowerSeries σ C) : constantCoeff (subst a F) = constantCoeff F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [e, subst_add hs, map_add (f := _), constantCoeff_subst_zero ha (by simp), subst_C]
  simp

theorem subst_mvExp [CharZero C] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    subst a (mvExp F) = mvExp (subst a F) := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst (by rw [cc_subst ha, hF]), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hF]

theorem intS_subst {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C} (hF : IntS V F) :
    IntS V (subst a F) :=
  (intS_iff_ig V _).2 (ig_subst (fun s => (intS_iff_ig V _).1 (hi s)) ha ((intS_iff_ig V _).1 hF))

theorem intS_X {V : VF C} {σ : Type} (s : σ) : IntS V (X s : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (ig_X s)

theorem intS_one {V : VF C} {σ : Type} : IntS V (1 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (one_mem _)

theorem intS_zero {V : VF C} {σ : Type} : IntS V (0 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (zero_mem _)

theorem intS_mul {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F) (hG : IntS V G) :
    IntS V (F * G) :=
  (intS_iff_ig V _).2 (mul_mem ((intS_iff_ig V _).1 hF) ((intS_iff_ig V _).1 hG))

theorem intS_prod {V : VF C} {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C} (hF : ∀ i, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) :=
  (intS_iff_ig V _).2 (prod_mem fun i _ => (intS_iff_ig V _).1 (hF i))

theorem intS_of_mul_eq_one {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F)
    (h1 : constantCoeff F = 1) (hFG : F * G = 1) : IntS V G := by
  obtain ⟨U, hU⟩ := RingHom.mem_range.1 ((intS_iff_ig V _).1 hF)
  have hU1 : constantCoeff U = 1 := by
    apply Subtype.ext
    have e := congrArg constantCoeff hU
    rw [constantCoeff_map, h1] at e
    exact e
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 := MvPowerSeries.mul_invOfUnit U 1 (by simp [hU1])
  have e : G = MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1) := by
    have h2 := congrArg (MvPowerSeries.map (σ := σ) (algebraMap (valRing V) C)) hinv
    rw [map_mul, map_one, hU] at h2
    calc G = G * (F * MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1)) := by
          rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, mul_comm G F, hFG, one_mul]
  rw [e]
  exact (intS_iff_ig V _).2 (ig_map _)

def logInt [CharZero C] (V : VF C) (σ : Type) : AddSubgroup (MvPowerSeries σ C) where
  carrier := {F | constantCoeff F = 0 ∧ IntS V (mvExp F)}
  zero_mem' := ⟨map_zero _, by rw [mvExp_zero']; exact intS_one⟩
  add_mem' := fun {F G} hF hG => ⟨by rw [map_add (f := _), hF.1, hG.1, add_zero], by
    rw [mvExp_add hF.1 hG.1]; exact intS_mul hF.2 hG.2⟩
  neg_mem' := fun {F} hF => ⟨by rw [map_neg, hF.1, neg_zero], by
    refine intS_of_mul_eq_one hF.2 ?_ ?_
    · rw [mvExp_eq_subst hF.1, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp hF.1]
    · rw [← mvExp_add hF.1 (by rw [map_neg, hF.1, neg_zero]), add_neg_cancel, mvExp_zero']⟩

theorem mem_logInt [CharZero C] {V : VF C} {σ : Type} {F : MvPowerSeries σ C} :
    F ∈ logInt V σ ↔ constantCoeff F = 0 ∧ IntS V (mvExp F) := Iff.rfl

theorem logInt_subst [CharZero C] {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C}
    (hF : F ∈ logInt V σ) : subst a F ∈ logInt V τ :=
  ⟨by rw [cc_subst ha, hF.1], by rw [← subst_mvExp ha hF.1]; exact intS_subst ha hi hF.2⟩

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def IntEnd (X : RawChart C d I κ) (V : VF C) (A : Matrix κ κ C) : Prop :=
  ∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)

def hEnd (X : RawChart C d I κ) (A B : Matrix κ κ C) : MvPowerSeries κ C :=
  hAt X (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C)) (endP X B (MvPowerSeries.X : κ → MvPowerSeries κ C))

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantGeneratorDescendsMulN
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem invGenDescent_gs_appLE {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (W : Y.Opens) (W' : Y'.Opens)
    (h : W' ≤ τ ⁻¹ᵁ W) (a : Γ(Y, W)) (x : Y') (hx : x ∈ W') :
    gs (𝟙 Y') x W' ((τ.appLE W W' h).hom a) = gs τ x W a := by
  have e := (gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)
  rw [Category.id_comp] at e
  exact e


open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
private theorem invariant_generator_descent {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) (ψ : Y ⟶ X)
    (σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => m ≫ ψ) (fun _ => 1))) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (𝟙 Y' ≫ τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (M.pull ψ).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : PUnit → M.ι, m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j ≤ LB.wchart M (fun _ : PUnit => m ≫ ψ) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : PUnit → M.ι, ∃ v : Γ(Y, LB.wchart M (fun _ : PUnit => ψ) j)ˣ,
      pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M (fun _ : PUnit => ψ) j) (hτ t)).mpr hx
    obtain ⟨J, hJ, e⟩ := exists_good M hM x (fun _ : PUnit => m ≫ ψ) j (fun a b _ => rfl)
      (fun k => Set.mem_iInter.1 (le j hx) k)
    have := inv t x J hJ
    rw [val_of σ _ x J j (fun k => by rw [Category.id_comp, ← Category.assoc, hτ]; exact e k),
      val_of σ _ x J j (fun k => by rw [Category.id_comp]; exact e k), Category.id_comp] at this
    exact (gm_res (τ t) x (le j) hx' _).trans (this.trans (gm_res (𝟙 Y') x (le j) hx _).symm)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : PUnit → M.ι, m x ∈ LB.wchart M (fun _ : PUnit => ψ) j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun _ : PUnit => m ≫ ψ) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M (fun _ : PUnit => ψ) i ⊓ LB.wchart M (fun _ : PUnit => ψ) j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M (fun _ : PUnit => ψ) (fun _ => 1) (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]

theorem invariantGenerator_descends_mulN :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V)),
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V), ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) →
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) := by
  intro H S G _ _ K _ _ f N hN h₁ h₂ h₃ h₄ X M hM ψ σ hσ inv
  refine invariant_generator_descent (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left (T := {y : Over.mk f ⟶ G // y ^ N = 1})
    (fun y => (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y.1)) (snd G (Over.mk f))).left) (fun y => ?_)
    (fun V a ha => H S G K f N hN h₁ h₂ h₃ h₄ V a (fun y hy => ha ⟨y, hy⟩)) M hM ψ σ hσ
    (fun y z J hJ => inv y.1 y.2 _ (𝟙 _) z J hJ)
  rw [← Over.comp_left]
  congr 1
  ext1
  · rw [lift_whiskerRight, lift_fst, whiskerRight_fst, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.mul_one]
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OrbitSumFiftyOne
section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.OrbitPlan

theorem exists_good {S : ℕ} {G : Set ℕ} (h : Windows S G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y ∈ G, (y : ℝ) ≤ r ∧ r - y ≤ S := by
  have h1 := Nat.floor_le hr
  have h2 := Nat.lt_floor_add_one r
  by_cases hS : S ≤ ⌊r⌋₊ + 1
  · obtain ⟨y, hy, hy1, hy2⟩ := h.2 (⌊r⌋₊ + 1 - S)
    have a1 : y ≤ ⌊r⌋₊ := by omega
    have a2 : ⌊r⌋₊ + 1 ≤ y + S := by omega
    have b1 : (y : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast a1
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ y + S := by exact_mod_cast a2
    exact ⟨y, hy, by linarith, by linarith⟩
  · have a2 : ⌊r⌋₊ + 1 ≤ S := by omega
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ S := by exact_mod_cast a2
    exact ⟨0, h.1, by simpa using hr, by simp only [Nat.cast_zero]; linarith⟩

theorem logTerm_nonneg {l n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) * (Real.logb l n + 1) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.logb_nonneg h1 h2
  positivity

end GlobalTheory.OrbitPlan
end

