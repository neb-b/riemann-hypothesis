module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralCoeIff
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.EigenlineBaseChange

theorem isIntegral_coe_iff {M : IntermediateField ℚ ℂ} (x : M) : IsIntegral ℤ (x : ℂ) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective

theorem span_eq_top {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]
    (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M) (τ : D.what₂.Tau) (s : M)
    (hs : TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s}) :
    Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0, ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} = ⊤ := by
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hsm : s ∈ TaylorLogMetric.ellT D M τ := hs ▸ Submodule.mem_span_singleton_self s
  rw [GlobalTheory.Glob.mem_ellT_iff hM] at hsm
  let g : ∀ y ∈ D.host.AA0, 𝓞 M := fun y hy =>
    ⟨s * ⟨_, hM τ (D.host.conj y)⟩, (isIntegral_coe_iff _).1 (hsm y hy)⟩
  set I : Ideal (𝓞 M) := Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
    ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)} with hI
  have hg : ∀ y hy, g y hy ∈ I := fun y hy => Ideal.subset_span ⟨y, hy, rfl⟩
  by_contra hI1
  have hI0 : I ≠ ⊥ := by
    intro h
    have h1 := hg 1 (GlobalTheory.AdelicApprox.one_mem_inverse_halfDifferent D)
    rw [h, Ideal.mem_bot] at h1
    have h2 : (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj 1) = 0 :=
      congrArg (fun a : 𝓞 M => ((a : M) : ℂ)) h1
    rw [map_one, map_one, mul_one] at h2
    exact hs0 (Subtype.ext h2)
  obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := M) hI0 hI1
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI0)] at hx
  have hxs : x * s ∈ TaylorLogMetric.ellT D M τ := by
    rw [GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
      (hx _ (FractionalIdeal.mem_coeIdeal_of_mem _ (hg y hy)))
    have h1 : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
    have h2 : ((c : M) : ℂ) = (x : ℂ) * ((s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)) :=
      congrArg (fun a : M => (a : ℂ)) hc
    rw [h2, ← mul_assoc] at h1
    exact h1
  rw [hs, Submodule.mem_span_singleton] at hxs
  obtain ⟨c, hc⟩ := hxs
  refine hx1 ((FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩)
  exact mul_right_cancel₀ hs0 hc

theorem ellT_eq_span_of_le : ∀ (D : D7) (M M' : IntermediateField ℚ ℂ) [NumberField M] [NumberField M'] (hle : M ≤ M'), (∀ τ x, TaylorLogMetric.embT D τ x ∈ M) → ∀ (τ : D.what₂.Tau) (s : M), TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {s} → TaylorLogMetric.ellT D M' τ = Submodule.span (𝓞 M') {(⟨(s : ℂ), hle s.2⟩ : M')} := by
  intro D M M' _ _ hle hM τ s hs
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M' := fun τ x => hle (hM τ x)
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM hs.symm
  have hs0' : (s : ℂ) ≠ 0 := fun h => hs0 (Subtype.ext h)
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM'] at hx
    have key : ∀ a ∈ Ideal.span {a : 𝓞 M | ∃ y ∈ D.host.AA0,
        ((a : M) : ℂ) = (s : ℂ) * TaylorLogMetric.embT D τ (D.host.conj y)},
        IsIntegral ℤ ((x : ℂ) * (s : ℂ)⁻¹ * ((a : M) : ℂ)) := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, hy, e⟩ := ha
        rw [e, mul_assoc, inv_mul_cancel_left₀ hs0']
        exact hx y hy
      | zero => simpa using isIntegral_zero
      | add a b _ _ ha hb =>
        have e : (((a + b : 𝓞 M) : M) : ℂ) = ((a : M) : ℂ) + ((b : M) : ℂ) := rfl
        rw [e, mul_add]
        exact ha.add hb
      | smul c a _ ha =>
        have hc : IsIntegral ℤ (((c : M) : ℂ)) := (isIntegral_coe_iff _).2 c.isIntegral_coe
        have e : (((c • a : 𝓞 M) : M) : ℂ) = ((c : M) : ℂ) * ((a : M) : ℂ) := rfl
        rw [e, mul_left_comm]
        exact hc.mul ha
    have h1 := key 1 (by rw [span_eq_top hM τ s hs]; trivial)
    have e : (((1 : 𝓞 M) : M) : ℂ) = 1 := rfl
    rw [e, mul_one] at h1
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨(s : ℂ), hle s.2⟩ : M')⁻¹, (isIntegral_coe_iff _).1 h1⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hs0' (congrArg (fun a : M' => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM']
    exact (GlobalTheory.Glob.mem_ellT_iff hM τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)

end GlobalTheory.EigenlineBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanScalIffOfLeftEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTPullTan

open GlobalTheory.UPel.HT

theorem isTanScal_iff_of_left_eq : ∀ {O : Type} [Ring O] {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A'), IsGrpPullback A' A f φ → (∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) → ∀ {R' : Type} [CommRing R'] (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A), v₀.left = v.left ≫ φ → (GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀) := by
  intro O _ S S' A A' _ _ f φ a a' h hact R' _ x b c v v₀ hv₀
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A') (u₀ w₀ : epsPtR (x ≫ f) ⟶ A), u₀.left = u.left ≫ φ → w₀.left = w.left ≫ φ →
      (u.left = spMap (epsScaleR c) ≫ w.left ↔
      u₀.left = spMap (epsScaleR c) ≫ w₀.left) := fun u w u₀ w₀ hu hw => by
    rw [hu, hw]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, hv₀]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · refine hR _ _ _ _ ?_ hv₀
    rw [Over.comp_left, Over.comp_left, hv₀, Category.assoc, Category.assoc, hact]

end GlobalTheory.HTPullTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledCharactersEqAndCongrPrimeToPart
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel.Congr

theorem part_pow {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, ?_⟩
  rw [hz, ← pow_mul, mul_comm, pow_mul]
  have := pow_eq_pow_of_modEq hmod hone
  rwa [pow_one] at this

theorem part_pow_compl {G : Type} [Monoid G] (l : ℕ) (x : G) :
    Formalism.CyclotomicNorms.primeToPart l x ^ (orderOf x / l ^ (orderOf x).factorization l) = 1 := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [← pow_mul, mul_right_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_mul, pow_orderOf_eq_one, one_pow]

theorem eq_of_pow_eq {G : Type} [Monoid G] {M k : ℕ} (hM : M ≠ 0) (hk : k.Coprime M) {y z : G}
    (hy : y ^ M = 1) (hz : z ^ M = 1) (h : y ^ k = z ^ k) : y = z := by
  haveI : NeZero M := ⟨hM⟩
  set u := ((k : ZMod M)⁻¹).val with hu
  have hmod : k * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hk
  have h1 := pow_eq_pow_of_modEq hmod hy
  have h2 := pow_eq_pow_of_modEq hmod hz
  rw [pow_one, pow_mul] at h1 h2
  rw [← h1, h, h2]

theorem part_eq_iff {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x y : G} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) :
    (∃ n : ℕ, x ^ (l ^ n) = y ^ (l ^ n)) ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y := by
  obtain ⟨a, ha⟩ := part_pow hl hx
  obtain ⟨b, hb⟩ := part_pow hl hy
  have h1 : ∀ n, x ^ (l ^ (a + b + n)) = Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ (a + b + n)) := fun n => by
    rw [add_assoc, pow_add, pow_mul, pow_mul, ha]
  have h2 : ∀ n, y ^ (l ^ (a + b + n)) = Formalism.CyclotomicNorms.primeToPart l y ^ (l ^ (a + b + n)) := fun n => by
    rw [add_comm a b, add_assoc, pow_add, pow_mul, pow_mul, hb]
  constructor
  · rintro ⟨n, hn⟩
    have hx0 : orderOf x ≠ 0 := hx.orderOf_pos.ne'
    have hy0 : orderOf y ≠ 0 := hy.orderOf_pos.ne'
    refine eq_of_pow_eq (M := (orderOf x / l ^ (orderOf x).factorization l) *
      (orderOf y / l ^ (orderOf y).factorization l)) (k := l ^ (a + b + n))
      (mul_ne_zero (Nat.ordCompl_pos l hx0).ne' (Nat.ordCompl_pos l hy0).ne')
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (Nat.coprime_ordCompl hl hx0)
        (Nat.coprime_ordCompl hl hy0))) ?_ ?_ ?_
    · rw [pow_mul, part_pow_compl, one_pow]
    · rw [mul_comm, pow_mul, part_pow_compl, one_pow]
    · rw [← h1, ← h2, add_comm, pow_add, pow_mul, pow_mul, hn]
  · intro h
    exact ⟨a + b + 0, by rw [h1, h2, h]⟩

variable {p : ℕ} [Fact p.Prime]

theorem thetaOf_gen (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  have hfin : IsOfFinOrder (L.gen d) := by
    rw [← orderOf_pos_iff, L.gen_order d hd]; exact hp
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left h]
  have h1 := hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  rw [L.gen_order d hd] at h1
  exact (pow_eq_pow_of_modEq h1 (by rw [← map_pow, hx, map_one])).symm

theorem pow_eq_iff (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {θ θ' : Tor p d →* ℂˣ} {x x' : Fbar p}
    (h : LabelsChar L θ x) (h' : LabelsChar L θ' x') (m : ℕ) : θ ^ m = θ' ^ m ↔ x ^ m = x' ^ m := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hx0 : x ≠ 0 := fun e => by
    have := h.1; rw [e, zero_pow hp.ne'] at this; exact zero_ne_one this
  have hx0' : x' ≠ 0 := fun e => by
    have := h'.1; rw [e, zero_pow hp.ne'] at this; exact zero_ne_one this
  constructor
  · intro e
    let u : Tor p d := rootsOfUnity.mkOfPowEq (L.gen d) hprim.pow_eq_one
    have hu : ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ 1 := by rw [pow_one]; rfl
    have e1 := h.2 u
    have e2 := h'.2 u
    rw [hu, thetaOf_gen L hd h.1, pow_one] at e1
    rw [hu, thetaOf_gen L hd h'.1, pow_one] at e2
    have e3 : ((θ u : ℂˣ) : ℂ) ^ m = ((θ' u : ℂˣ) : ℂ) ^ m := by
      have := congrArg (fun f : Tor p d →* ℂˣ => ((f u : ℂˣ) : ℂ)) e
      simpa using this
    refine L.teich_inj _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0') ?_
    rw [map_pow, map_pow, ← e1, ← e2, e3]
  · intro e
    refine MonoidHom.ext fun u => Units.ext ?_
    have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
    have e1 := h.2 u
    have e2 := h'.2 u
    rw [← hn, thetaOf_gen L hd h.1] at e1
    rw [← hn, thetaOf_gen L hd h'.1] at e2
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e1, e2,
      ← pow_mul, ← pow_mul, mul_comm n m, pow_mul, pow_mul, ← map_pow L.teich x m, ← map_pow L.teich x' m, e]

theorem eq_and_congr : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (d : ℕ), 0 < d → ∀ (θ θ' : Tor p d →* ℂˣ) (x x' : Fbar p), LabelsChar L θ x → LabelsChar L θ' x' → (θ = θ' ↔ x = x') ∧ ∀ l : ℕ, l.Prime → (CongrMod l θ θ' ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l x') := by
  intro p _ L d hd θ θ' x x' h h'
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  refine ⟨by simpa using pow_eq_iff L hd h h' 1, fun l hl => ?_⟩
  rw [← part_eq_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hp, h.1⟩) (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hp, h'.1⟩)]
  refine exists_congr fun n => ?_
  rw [div_pow, div_eq_one]
  exact pow_eq_iff L hd h h' _

end GlobalTheory.ParamLabel.Congr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymFirstOrder
open GlobalTheory.CechPic

theorem lbIso_of_symmetric : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left),
    IsAbelianScheme A →
    IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i →
    IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → i ≫ q = 𝟙 _ →
    ∀ (L M : LB A'.left), L.IsLB → M.IsLB →
      LBIso (L.pull (GrpObj.inv : A' ⟶ A').left) L → LBIso (M.pull (GrpObj.inv : A' ⟶ A').left) M →
      LBIso (L.pull i) (M.pull i) → LBIso L M := by
  intro K _ _ A _ A' _ i q hA hi hq e L M hL hM hLs hMs hLM
  have hA' : IsAbelianScheme A' := by
    have := hA.comm
    have hcomm : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hq.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hq.2 T x y (pushPt hq.1.w x) (pushPt hq.1.w y) rfl rfl,
        ← hq.2 T y x (pushPt hq.1.w y) (pushPt hq.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hcomm, MorphismProperty.of_isPullback (P := @Smooth) hq.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hq.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hq.1 hA.geomConnected⟩
  set c := cls L hL - cls M hM with hc
  have h0 : pull i c = 0 := by
    rw [hc, map_sub, ← cls_pull hL i (pull_isLB hL i), ← cls_pull hM i (pull_isLB hM i),
      (cls_eq_iff (pull_isLB hL i) (pull_isLB hM i)).2 hLM, sub_self]
  have hinv : pull (GrpObj.inv : A' ⟶ A').left c = c := by
    rw [hc, map_sub, ← cls_pull hL _ (pull_isLB hL _), ← cls_pull hM _ (pull_isLB hM _),
      (cls_eq_iff _ hL).2 hLs, (cls_eq_iff _ hM).2 hMs]
  have hlam := ConstTheta.lam_eq_zero GlobalTheory.laws_without_cohomology.1 hA' hi.1 c h0 (𝟙 A') (𝟙 A')⁻¹
  have einv : (𝟙 A')⁻¹ = (GrpObj.inv : A' ⟶ A') := by simp [Hom.inv_def]
  have hone : pull (1 : A' ⟶ A').left c = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨Q, hQ, hQc⟩ := cls_surj (pull (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left c)
    rw [← hQc, (cls_eq_zero_iff hQ).2 (LB.exists_isGen_of_isLocalRing hQ), map_zero]
  have htwo : 2 • c = 0 := by
    unfold lam at hlam
    rw [mul_inv_cancel, einv, hinv, hone, Over.id_left, pull_id] at hlam
    rw [two_nsmul, ← neg_eq_zero, neg_add]
    simpa [sub_eq_add_neg, add_assoc] using hlam

  have hsurj : Surjective i := by
    have : Surjective (GlobalTheory.DeRham.epsRed K) := ⟨fun x => by
      haveI := ConstTheta.subsingleton_sp (K := K)
      obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
      exact ⟨t, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.of_isPullback (P := @Surjective) hi.1.flip this
  have hiq : ∀ x, i (q x) = x := fun x => by
    obtain ⟨y, rfl⟩ := hsurj.surj x
    rw [← Scheme.Hom.comp_apply i q, e]; rfl
  have h2 : IsUnit (2 : Γ(A'.left, ⊤)) := by
    have u : IsUnit (2 : DualNumber K) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [show TrivSqZeroExt.fst (2 : DualNumber K) = 2 from rfl]; exact isUnit_iff_ne_zero.2 two_ne_zero)
    have u' := (u.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom).map A'.hom.appTop.hom
    rwa [map_ofNat, map_ofNat] at u'
  have hsq : ∀ (W : A'.left.Opens) (f g : Γ(A'.left, W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0 := by
    refine SquareZero.mul_eq_zero_of_app_eq_zero (DualNumber K) K (TrivSqZeroExt.fstHom K K K).toRingHom
      TrivSqZeroExt.fst_surjective ?_ A'.left A.left A'.hom A.hom i hi.1
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have hc0 := _root_.GlobalTheory.CechPic.eq_zero_of_sqZero_retract i q e hiq h2 hsq c h0 htwo
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 hc0)

end GlobalTheory.SymFirstOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
section
open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMink

theorem sum_embeddings_eq_two_mul {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (g : (K →+* ℂ) → ℝ) (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ : K →+* ℂ, g σ = 2 * ∑ v : InfinitePlace K, g v.embedding := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ => InfinitePlace.mk σ) g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [this, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
  norm_num

theorem slopeMax_sq_le_of_no_short : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V)
    (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ →
    (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) →
    slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) +
      Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  intro K V _ _ _ _ _ _ _ N L La hG hconj hfg h0 hshort
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hX⟩ := hG.some
  rw [(slopeMax_slopeMin_eq hX hfg h0).1]
  have hXu : ∀ v, IsUnit (X v).det := fun v => (hX v).1
  have hnf : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hmink := Formalism.ExtensionFiltration.muMaxMinkowski K V (Fin n) b X hXu L La hfg h0 (by
    intro x hx hx0
    have h1 := hshort x hx hx0
    rw [sum_embeddings_eq_two_mul (fun σ => Real.log (N σ x)) (fun σ => by simp only [hconj])] at h1
    have e : ∀ v : InfinitePlace K, Real.log (N v.embedding x) = Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) :=
      fun v => by rw [(hX v).2 x]
    simp only [e] at h1
    rw [hnf] at h1
    push_cast at h1
    have : (2 * ∑ v : InfinitePlace K, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) / (2 * (Formalism.HN.nPl K : ℝ)) =
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := by
      field_simp
    linarith)
  haveI : Module.Finite K V := Module.Finite.of_basis b
  have hj : 0 < Formalism.HN.rkK L := by
    have h : Submodule.span K (L : Set V) ≠ ⊥ := by
      intro h
      apply h0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
  have hle : (Formalism.HN.rkK L : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast Submodule.finrank_le _
  have hlog : Real.log (Formalism.HN.rkK L : ℝ) ≤ Real.log (Module.finrank K V : ℝ) :=
    Real.log_le_log (by exact_mod_cast hj) hle
  have hd : Formalism.HN.logDisc K = Real.log |(discr K : ℝ)| := rfl
  rw [hd] at hmink
  linarith

end GlobalTheory.SlopeMink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStable
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.sqProd_sq_mem_and_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
    sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  intro p F L t hp h4 h3 hD
  refine ⟨?_, ?_⟩
  · apply _root_.GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed F
    intro σ hσ
    rw [map_pow]
    rcases _root_.GlobalTheory.SqConj.sqProd_conj p F L t hp h4 h3 hD σ hσ with ⟨h, _⟩ | h
    · rw [h]
    · rw [h, neg_sq]
  · intro hmem σ hσ
    rcases _root_.GlobalTheory.SqConj.sqProd_conj p F L t hp h4 h3 hD σ hσ with ⟨_, he⟩ | h
    · exact he
    · exfalso
      have hne := (_root_.GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero p F L t hp h4 h3 hD).2
      have hfix : σ (sqProd p L t) = sqProd p L t := hσ _ hmem
      rw [hfix] at h
      have h2 : (2 : ℂ) * sqProd p L t = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h2 | h2
      · norm_num at h2
      · exact hne h2
end

