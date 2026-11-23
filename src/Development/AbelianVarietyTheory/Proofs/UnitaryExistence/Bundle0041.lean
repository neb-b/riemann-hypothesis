module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsUnitIffMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieBaseChange

open GlobalTheory.SqZero

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

def pushRHom (P : Type) [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P] :
    (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) where
  toFun := pushR G
  map_one' := pushR_one G
  map_mul' y y' := by
    have h := map_mul (pushHom (isGrpPullback_pullback G (fB R R')) (sp (R₀ := R') P)) y y'
    exact (congrArg (iotaB ≫ ·) h).trans (MonObj.comp_mul _ _ _)

theorem isTan_iff_mem (w : sp (R₀ := R') (DualNumber R') ⟶ (Over.pullback (fB R R')).obj G) :
    IsTan w ↔ pushR G w ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)) := by
  have e : IsTan w ↔ spMap ((fstD R').restrictScalars R) ≫ pushR G w = 1 := by
    rw [← pushR_spMap, IsTan]
    exact ⟨fun h => by rw [h, pushR_one], fun h => pushR_inj G (by rw [h, pushR_one])⟩
  rw [e]
  exact ⟨mem_redKer_of_section _ ((Algebra.ofId R' (DualNumber R')).restrictScalars R)
    (fun a => rfl), fun h => comp_eq_one_of_mem_redKer h _ fun a ha => ha⟩

variable {G} {n : ℕ}

def bcVec (R' : Type) [CommRing R'] [Algebra R R'] (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    epsR R' ⟶ (Over.pullback (fB R R')).obj G :=
  pullR (R' := R') G (spMap (dualMapA R R') ≫ v i)

theorem pushR_bcVec (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    pushR G (bcVec R' v i) = spMap (dualMapA R R') ≫ v i := pushR_pullR G _

theorem bcVec_left_fst (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    (bcVec R' v i).left ≫ pullback.fst G.hom (fB R R') =
      Geo.Tor.spMap (dualMapR (algebraMap R R')) ≫ (v i).left := by
  rw [← pushR_left, pushR_bcVec]
  rfl

theorem pushR_prodPts [IsCommMonObj G] (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R') :
    pushR G (prodPts c (bcVec R' v)) =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  refine (map_list_prod (pushRHom G (DualNumber R')) _).trans ?_
  rw [List.map_ofFn, List.prod_ofFn, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  change pushR G (spMap _ ≫ _) = _
  rw [pushR_spMap, pushR_bcVec, ← Category.assoc, spMap_comp]
  congr 2
  refine DualNumber.algHom_ext ?_
  rw [epsTo_eps, AlgHom.comp_apply]
  change TrivSqZeroExt.map _ (dualMapA R R' (inr 1)) = _
  rw [dualMapA_inr, TrivSqZeroExt.map_inr]
  simp

theorem isLieBasis_bcVec_of [IsCommMonObj G] {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (inj : ∀ c c' : Fin n → R',
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) =
      lieExp v (fun i => (inr (c' i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) →
        c = c')
    (surj : ∀ y ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)), ∃ c : Fin n → R', y =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    IsLieBasis (bcVec R' v) := by
  refine ⟨fun i => (isTan_iff _).1 ((isTan_iff_mem G _).2 ?_), fun w hw => ?_⟩
  · rw [pushR_bcVec]
    refine mem_redKer_of_section ((fstD R').restrictScalars R)
      ((Algebra.ofId R' (DualNumber R')).restrictScalars R) (fun a => rfl) ?_
    have : ((fstD R').restrictScalars R).comp (dualMapA R R') = (Algebra.ofId R R').comp (fstD R) := by
      refine DualNumber.algHom_ext ?_
      change (dualMapA R R' (inr 1)).fst = algebraMap R R' 0
      rw [dualMapA_inr]; simp
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, (isTan_iff _).2 (hv i),
      comp_one']
  · obtain ⟨c, hc⟩ := surj _ ((isTan_iff_mem G _).1 ((isTan_iff _).2 hw))
    refine ⟨c, (isLieComb_iff _ _ _).2 (pushR_inj G (by rw [hc, pushR_prodPts])), fun c' hc' => ?_⟩
    refine inj _ _ ?_
    rw [← hc, (isLieComb_iff _ _ _).1 hc', pushR_prodPts]

theorem isLieBasis_bcVec [IsCommMonObj G] [Smooth G.hom] {v : Fin n → (epsR R ⟶ G)}
    (hv : IsLieBasis v) : IsLieBasis (bcVec R' v) := by
  obtain ⟨h₁, h₂⟩ := expBij (DualNumber R') hv (RingHom.ker ((fstD R').restrictScalars R))
    (ker_fst_sq (R := R) (S := R') R')
  refine isLieBasis_bcVec_of hv.1 (fun c c' h => funext fun i => ?_) fun y hy => ?_
  · exact congrArg TrivSqZeroExt.snd
      (congrFun (h₁ _ _ (fun i => inr_mem_kerD (c i)) (fun i => inr_mem_kerD (c' i)) _ _ h) i)
  · obtain ⟨c, hc, hcJ, e⟩ := h₂ y hy
    have hc' : ∀ i, c i = inr (c i).snd := fun i =>
      have h0 : (c i).fst = 0 := hcJ i
      TrivSqZeroExt.ext h0 rfl
    exact ⟨fun i => (c i).snd, e.trans (lieExp_congr v hc' _ _)⟩

end GlobalTheory.LieBaseChange

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)

theorem exists_isLieBasis_baseChange (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R')
    (G : Over (Sp R)) (G' : Over (Sp R')) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) (hs : Smooth G.hom) (n : ℕ)
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) :
    ∃ v' : Fin n → (epsR R' ⟶ G'), IsLieBasis v' ∧
      ∀ i, (v' i).left ≫ φ = Geo.Tor.spMap (Chart.dualMapR f) ≫ (v i).left := by
  let _ := f.toAlgebra
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine ⟨fun i => LieBaseChange.bcVec R' v i ≫ e.inv, isLieBasis_iso e ?_, fun i => ?_⟩
  · simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using
      LieBaseChange.isLieBasis_bcVec (R' := R') hv
  · rw [← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact LieBaseChange.bcVec_left_fst v i

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralClosureFiniteLocalCompleteMixedChar
section
open IsLocalRing

namespace GlobalTheory


open IsLocalRing in
theorem _root_.GlobalTheory.finite_normalisation_of_finite_over_normal (A S : Type) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [CharZero S]
    [Algebra A S] [FaithfulSMul A S] [Module.Finite A S] :
    Module.Finite S (integralClosure S (FractionRing S)) := by
  haveI : FaithfulSMul A (FractionRing S) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A S (FractionRing S)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective A S))
  letI : Algebra (FractionRing A) (FractionRing S) := FractionRing.liftAlgebra A _
  haveI := FractionRing.isScalarTower_liftAlgebra A (FractionRing S)
  haveI : CharZero (FractionRing S) := charZero_of_injective_algebraMap (IsFractionRing.injective S _)
  haveI : CharZero (FractionRing A) := (algebraMap (FractionRing A) (FractionRing S)).charZero
  haveI : FiniteDimensional (FractionRing A) (FractionRing S) := inferInstance
  haveI : IsIntegralClosure (integralClosure S (FractionRing S)) A (FractionRing S) := by
    refine ⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, h.tower_top⟩, rfl⟩, ?_⟩⟩
    rintro ⟨y, rfl⟩
    exact isIntegral_trans (R := A) (A := S) (y : FractionRing S) y.2
  haveI : Module.Finite A (integralClosure S (FractionRing S)) :=
    IsIntegralClosure.finite A (FractionRing A) (FractionRing S) _
  exact Module.Finite.of_restrictScalars_finite A S _

open IsLocalRing in
private theorem isPrecomplete_of_finite_module {R M : Type*} [CommRing R] {I : Ideal R} [hR : IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hpow : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have key : ∀ n (x : M), x ∈ (I ^ n • ⊤ : Submodule R M) →
      ∃ c : Fin k → R, (∀ j, c j ∈ I ^ n) ∧ ∑ j, c j • g j = x := by
    intro n x hx
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, by simp [Finsupp.sum_fintype]⟩
  refine ⟨fun {f} hf => ?_⟩
  have hd : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := fun n => by
    have := (hf (Nat.le_succ n))
    rw [SModEq.sub_mem] at this
    simpa using neg_mem this
  choose c hcI hcsum using fun n => key n _ (hd n)
  have hs : ∀ j, ∃ a : R, ∀ n, (∑ i ∈ Finset.range n, c i j) ≡ a [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro j
    refine hR.prec' _ fun {m n} hmn => ?_
    rw [SModEq.sub_mem, hpow]
    have : ∑ i ∈ Finset.range m, c i j - ∑ i ∈ Finset.range n, c i j =
        -∑ i ∈ Finset.Ico m n, c i j := by
      rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
    rw [this]
    exact neg_mem (Ideal.sum_mem _ fun i hi =>
      Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hcI i j))
  choose a ha using hs
  refine ⟨f 0 + ∑ j, a j • g j, fun n => ?_⟩
  have hfn : f n = f 0 + ∑ j, (∑ i ∈ Finset.range n, c i j) • g j := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, hcsum n]
      rw [← add_assoc, ← ih]
      abel
  rw [SModEq.sub_mem, hfn, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have := (SModEq.sub_mem.1 (ha j n))
  rw [hpow] at this
  exact Submodule.smul_mem_smul this Submodule.mem_top

open IsLocalRing in
open Polynomial in
private theorem isLocalRing_of_finite_domain_over_complete (S C : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] [CommRing C] [IsDomain C] [Algebra S C]
    [Module.Finite S C] : IsLocalRing C := by
  set I : Ideal C := (maximalIdeal S).map (algebraMap S C) with hI
  haveI : IsPrecomplete (maximalIdeal S) C := isPrecomplete_of_finite_module
  haveI : IsAdicComplete (maximalIdeal S) C := {}
  haveI : IsAdicComplete I C := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  have hIM : ∀ M : Ideal C, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S) M)).ge
  haveI : IsArtinianRing (C ⧸ I) := by
    letI := Ideal.Quotient.field (maximalIdeal S)
    haveI : Module.Finite (S ⧸ maximalIdeal S) (C ⧸ I) :=
      Module.Finite.of_restrictScalars_finite S _ _
    exact IsArtinianRing.of_finite (S ⧸ maximalIdeal S) _
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨M₁, hM₁⟩ := Ideal.exists_maximal C
  refine ⟨M₁, hM₁, fun M₂ hM₂ => ?_⟩
  by_contra hne
  obtain ⟨x, hx₂, hx₁⟩ : ∃ x ∈ M₂, x ∉ M₁ := by
    by_contra! h
    exact hne (hM₂.eq_of_le hM₁.ne_top h)
  set u := Ideal.Quotient.mk I x with hu
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := C ⧸ I) (M := C ⧸ I)
    ⟨fun n => OrderDual.toDual (Ideal.span {u ^ n}),
      fun a b hab => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow u hab)⟩
  set m := N + 1 with hmdef
  have hm : u ^ m ∈ Ideal.span {u ^ (m + 1)} := by
    have h₁ := hN m (by omega)
    have h₂ := hN (m + 1) (by omega)
    have : Ideal.span {u ^ m} = Ideal.span {u ^ (m + 1)} := by
      exact congrArg OrderDual.ofDual (h₁.symm.trans h₂)
    rw [← this]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hm
  have hpow : ∀ j, u ^ m = u ^ (m + j) * v ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, pow_add u m j, ← hv]
      ring
  have he : (u ^ m * v ^ m) * (u ^ m * v ^ m) = u ^ m * v ^ m := by
    calc (u ^ m * v ^ m) * (u ^ m * v ^ m) = (u ^ (m + m) * v ^ m) * v ^ m := by ring
      _ = u ^ m * v ^ m := by rw [← hpow m]
  have hue : u ^ m = u ^ m * (u ^ m * v ^ m) := by
    calc u ^ m = u ^ (m + m) * v ^ m := hpow m
      _ = u ^ m * (u ^ m * v ^ m) := by ring
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
  set a₀ := x ^ m * y ^ m with ha₀def
  have hmk : Ideal.Quotient.mk I a₀ = u ^ m * Ideal.Quotient.mk I y ^ m := by
    simp [ha₀def, hu]
  have hmon : (X ^ 2 - X : C[X]).Monic := by monicity!
  have heval : (X ^ 2 - X : C[X]).eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow, hmk]
    rw [sq, he, sub_self]
  have hder : (derivative (X ^ 2 - X : C[X])).eval a₀ = 2 * a₀ - 1 := by
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_one]
    norm_num
  have hunit : IsUnit (Ideal.Quotient.mk I ((derivative (X ^ 2 - X : C[X])).eval a₀)) := by
    rw [hder, map_sub, map_mul, hmk, map_one, map_ofNat]
    exact (Units.mkOfMulEqOne _ (2 * (u ^ m * Ideal.Quotient.mk I y ^ m) - 1)
      (by linear_combination 4 * he)).isUnit
  obtain ⟨a, ha, haa₀⟩ := HenselianRing.is_henselian (I := I) _ hmon a₀ heval hunit
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  have hx₂m : a₀ ∈ M₂ := M₂.mul_mem_right _ (M₂.pow_mem_of_mem hx₂ m (by omega))
  rcases mul_eq_zero.1 ha' with h0 | h1
  · subst h0
    have ha₀I : a₀ ∈ I := by simpa using neg_mem haa₀
    have hxm : x ^ m - x ^ m * a₀ ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, map_pow, ← hu, ← hue,
        sub_self]
    have : x ^ m ∈ M₁ := by
      have h := hIM M₁ hM₁ hxm
      have h' := M₁.mul_mem_left (x ^ m) (hIM M₁ hM₁ ha₀I)
      simpa using M₁.add_mem h h'
    exact hx₁ (hM₁.isPrime.mem_of_pow_mem m this)
  · have h1' : a = 1 := sub_eq_zero.1 h1
    subst h1'
    have : (1 : C) ∈ M₂ := by
      have h := hIM M₂ hM₂ haa₀
      simpa using M₂.add_mem h hx₂m
    exact hM₂.ne_top ((Ideal.eq_top_iff_one _).2 this)

open IsLocalRing in
theorem _root_.GlobalTheory.normalisation_finite_local_complete_of_mixedChar :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      Module.Finite S (integralClosure S (FractionRing S)) ∧
        ∃ _ : IsLocalRing (integralClosure S (FractionRing S)),
          IsNoetherianRing (integralClosure S (FractionRing S)) ∧
          IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S)))
            (integralClosure S (FractionRing S)) := by
  intro S _ _ _ _ p hp hpm hS hSc
  obtain ⟨A, _, _, _, i, hi, hfin, hAn, hAic, hAc⟩ :=
    _root_.GlobalTheory.CohenStructure.exists_finite_injective_of_isAdicComplete S p hp hpm hS hSc
  letI : Algebra A S := i.toAlgebra
  haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  haveI : Module.Finite A S := hfin
  haveI := hAn
  haveI := hAic
  haveI := hS
  haveI := hSc
  haveI hC : Module.Finite S (integralClosure S (FractionRing S)) := _root_.GlobalTheory.finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing (integralClosure S (FractionRing S)) := isLocalRing_of_finite_domain_over_complete S _
  haveI : IsNoetherianRing (integralClosure S (FractionRing S)) := isNoetherian_of_tower S inferInstance
  exact ⟨hC, inferInstance, inferInstance,
    _root_.GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite S _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmoothOfDedekindCharts
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.CurveThrough

theorem smooth_of_dedekind_charts (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0})
    (f : C ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (h : ∀ U : C.Opens, IsAffineOpen U → Nonempty U → IsDedekindDomain Γ(C, U)) :
    Smooth f := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : C.affineOpens // Nonempty U.1} => U.1) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, ⟨⟨x, hx⟩⟩⟩, hx⟩
  · rintro ⟨⟨U, hU⟩, hne⟩
    haveI := h U hU hne
    have hft : (f.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩
        ⟨U, hU⟩ le_top
    let e := Scheme.ΓSpecIso (CommRingCat.of k)
    let φ : k →+* Γ(C, U) := (e.inv ≫ f.appLE ⊤ U le_top).hom
    have hφ : φ.FiniteType :=
      (RingHom.finiteType_respectsIso.cancel_left_isIso e.inv (f.appLE ⊤ U le_top)).2 hft
    have hs : φ.Smooth := by
      letI := φ.toAlgebra
      haveI : Algebra.FiniteType k Γ(C, U) := hφ
      exact GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain k Γ(C, U)
    exact (RingHom.Smooth.propertyIsLocal.respectsIso.cancel_left_isIso e.inv (f.appLE ⊤ U le_top)).1 hs

end GlobalTheory.CurveThrough
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem unitRes_top_injective {S : Scheme.{0}} {T : Over S} :
    Function.Injective (Out.unitRes (T := T) ⊤) := by
  intro a b h
  have hi : IsIso (⊤ : T.left.Opens).ι := inferInstanceAs (IsIso T.left.topIso.hom)
  have hi' : IsIso (⊤ : T.left.Opens).ι.appTop := inferInstanceAs (IsIso ((⊤ : T.left.Opens).ι.app ⊤))
  have hb : Function.Injective (⊤ : T.left.Opens).ι.appTop.hom :=
    (ConcreteCategory.bijective_of_isIso (⊤ : T.left.Opens).ι.appTop).1
  exact Units.ext (hb (congrArg Units.val h))

theorem unitOn_injective_of_commRing {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  have hb : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  exact Units.ext (hb (congrArg Units.val h))

theorem weilIs_unique_fieldPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (n : ℤ) (x y : Over.mk t ⟶ G) (c c' : kˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x y (unitOn c') → c = c' := by
  intro S G _ L hL k _ t n x y c c' h h'
  let p : (Over.mk t).left := (⊥ : PrimeSpectrum k)
  have top : ∀ V : (Over.mk t).left.Opens, p ∈ V → V = ⊤ := fun V hV =>
    eq_top_iff.2 fun q _ => by
      have : q = p := Subsingleton.elim (α := PrimeSpectrum k) q p
      exact this ▸ hV
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', -, H'⟩ := h' p
  obtain rfl := top V hV
  obtain rfl := top V' hV'
  exact unitOn_injective_of_commRing (unitRes_top_injective
    (H1.commIsOf_unique hL θx θy _ _ (H θx θy hx hy) (H' θx θy hx hy)))

end GlobalTheory
end

