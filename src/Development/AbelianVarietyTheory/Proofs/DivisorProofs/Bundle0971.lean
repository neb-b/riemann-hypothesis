module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBoxLatticesProduct
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.LeftBasis

theorem isIntB_of_isIntB_of_repr {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) (v : HeightOneSpectrum ℤ)
    (h : ∀ k' k, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' k') k) ∈ v.adicCompletionIntegers ℚ)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) (hy : IsIntB v b' y) : IsIntB v b y := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_tmul b' v y, map_sum, Finsupp.finsetSum_apply]
  refine sum_mem fun k' _ => ?_
  rw [repr_tmul_apply]
  exact mul_mem (hy k') (h k' k)

theorem isIntB_iff_eventually {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ y, IsIntB v b y ↔ IsIntB v b' y := by
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ' × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ',
      algebraMap ℚ (v.adicCompletion ℚ) (b'.repr (b t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv y => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  exact ⟨isIntB_of_isIntB_of_repr b' b v (fun k k' => hv.2 (k, k')) y,
    isIntB_of_isIntB_of_repr b b' v (fun k' k => hv.1 (k', k)) y⟩

theorem isIntB_sum_leftBasis_iff_eventually : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  intro L _ _ C _ _ ι r e he κ ℓ κ' b
  let Φl : (Fin r → L) →ₗ[ℚ] C :=
    ∑ i, (LinearMap.mulRight ℚ (e i)) ∘ₗ ι.toLinearMap ∘ₗ LinearMap.proj i
  have hΦl : ∀ c, Φl c = ∑ i, ι (c i) * e i := fun c => by
    simp [Φl, LinearMap.sum_apply]
  have hbij : Function.Bijective Φl := by
    refine ⟨fun c c' hcc => ?_, fun x => ?_⟩
    · obtain ⟨d, -, hd⟩ := he (Φl c)
      exact (hd c (hΦl c)).trans (hd c' (hcc.trans (hΦl c'))).symm
    · obtain ⟨d, hd, -⟩ := he x
      exact ⟨d, (hΦl d).trans hd.symm⟩
  let Φ := LinearEquiv.ofBijective Φl hbij
  let b' : Module.Basis (Σ _ : Fin r, κ) ℚ C := (Pi.basis fun _ : Fin r => ℓ).map Φ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  haveI : FiniteDimensional ℚ C := Module.Finite.of_basis b'
  haveI : Fintype κ' := FiniteDimensional.fintypeBasisIndex b
  have hsingle : ∀ (j : Fin r) (l : L), Φ (Pi.single j l) = ι l * e j := by
    intro j l
    show Φl _ = _
    rw [hΦl, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · simp
  have hrepr : ∀ (j : Fin r) (l : L) (i : Fin r) (a : κ),
      b'.repr (ι l * e j) ⟨i, a⟩ = ℓ.repr ((Pi.single j l : Fin r → L) i) a := by
    intro j l i a
    rw [← hsingle]
    simp [b', Module.Basis.map_repr, Pi.basis_repr]
  have hcoord : ∀ (v : HeightOneSpectrum ℤ) (j : Fin r) (z : v.adicCompletion ℚ ⊗[ℚ] L) (i : Fin r) (a : κ),
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
        (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι z * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr ((Pi.single j z : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) i) a := by
    intro v j z i a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s l =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, AlgHom.id_apply,
        repr_tmul_apply, hrepr]
      by_cases h : i = j
      · subst h; simp [repr_tmul_apply]
      · simp [h]
    | add x y hx hy =>
      rw [map_add (f := _), add_mul, LinearEquiv.map_add (e := _), Finsupp.add_apply, hx, hy, Pi.single_add, Pi.add_apply,
        LinearEquiv.map_add, Finsupp.add_apply]
  obtain ⟨S, hS⟩ := isIntB_iff_eventually b b'
  refine ⟨S, fun v hv β => ?_⟩
  have hy : ∀ (i : Fin r) (a : κ), (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
      (∑ j, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β j) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr (β i) a := by
    intro i a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    simp_rw [hcoord]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finsupp.finsetSum_apply, ← map_sum]
    congr 2
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hS v hv]
  constructor
  · intro h i a
    rw [← hy]
    exact h ⟨i, a⟩
  · rintro h ⟨i, a⟩
    rw [hy]
    exact h i a

end GlobalTheory.AdicSpan.LeftBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiDetValues


set_option maxHeartbeats 1000000 in
theorem res_mem {D : D7} (S : Subfield ℂ) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq c χ)
    (hS : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ S)
    (P : Pl D.host.E) (ψ : (kP P)ˣ →* ℂˣ) (hψ : IsRes χ P ψ⁻¹) (u : (kP P)ˣ) : ((ψ u : ℂˣ) : ℂ) ∈ S := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  have h4 := hψ a (Units.mk0 _ ha0) u rfl ha.symm
  have h5 := hc.2 P e he (Units.mk0 _ ha0) (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) rfl
  have h6 := hS (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) (by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, hinf,
      zero_mul, add_zero])
  rw [h5, ← h4, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h6
  exact inv_mem_iff.1 h6


set_option maxHeartbeats 1000000 in
theorem chiC_mem_coeff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL t i g
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T t.alg t.laws.pins.2.2.1
  have hσ : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.good_σ₀
  have hA := (t.chiR i D.what₂.embLL hσ).2.2.2.1
  have h : ((chiC R i g : ℂˣ) : ℂ) ∈ (res T D.what₂.embLL).fieldRange := by
    unfold chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy, -⟩ := hA x hx
    exact ⟨y, hy.symm⟩
  exact h

end GlobalTheory.ChiDetValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open Classical in
theorem GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  intro D χ n h
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η hη a => ?_⟩
  have hsq : ∀ x, η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη
  obtain ⟨-, h1, h2, h3⟩ := hη
  set S := (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range ⊔
    (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)).range with hSdef
  have key : ∀ x, ((χ (idF D x) : Circle) : ℂ) = if x ∈ S then 1 else (-1) ^ n := fun x => h x
  have hS : ∀ x ∈ S, η x = 1 := by
    have : S ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ S
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ S := fun hm => hb (hS b hm)
  have hab : a * b ∈ S := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMemSpanCoordinateBoxIndicators
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.BoxDecomp

open Topology Filter

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem ball_mem_nhds_zero (v : Pl (F := F)) (N : ℕ) :
    {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} ∈ 𝓝 (0 : Fv F v) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := (π : v.adicCompletion F) with hp
  have hpv : Valued.v p = WithZero.exp (-1) := by
    rw [hp, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hrv : Valued.v (p ^ N) = WithZero.exp (-(N : ℤ)) := by
    rw [map_pow, hpv, ← WithZero.exp_nsmul]; congr 1; simp
  have hr : Valued.v (p ^ N) ≠ 0 := by rw [hrv]; exact WithZero.exp_ne_zero
  rw [Valued.mem_nhds_zero]
  have h' : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (p ^ N) ≠ 0 := by simpa using hr
  refine ⟨Units.mk0 _ h', fun y hy => ?_⟩
  have := (Valuation.restrict_lt_iff _).1 hy
  rw [hrv] at this
  exact le_of_lt this

theorem exists_ball_subset (v : Pl (F := F)) {s : Set (Fv F v)} (hs : s ∈ 𝓝 (0 : Fv F v)) :
    ∃ N : ℕ, {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact (map_ne_zero _).2 γ.ne_zero
  refine ⟨(-(WithZero.log g)).toNat + 1, fun y hy => hγ ?_⟩
  show (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hy ?_
  have hlt : WithZero.exp (-((((-(WithZero.log g)).toNat + 1 : ℕ)) : ℤ)) < WithZero.exp (WithZero.log g) :=
    WithZero.exp_lt_exp.2 (by omega)
  rwa [WithZero.exp_log hg0] at hlt

def B (v : Pl (F := F)) (κ : Type) (N : ℕ) : Set (κ → Fv F v) :=
  {x | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))}

theorem B_anti {κ : Type} {N M : ℕ} (h : N ≤ M) : B v κ M ⊆ B v κ N := fun x hx i =>
  (hx i).trans (WithZero.exp_le_exp.2 (by omega))

theorem zero_mem_B (κ : Type) (N : ℕ) : (0 : κ → Fv F v) ∈ B v κ N := fun i => by simp

theorem sub_mem_B {κ : Type} {N : ℕ} {x y : κ → Fv F v} (hx : x ∈ B v κ N) (hy : y ∈ B v κ N) :
    x - y ∈ B v κ N := fun i =>
  (Valuation.map_sub _ _ _).trans (max_le (hx i) (hy i))

theorem add_mem_B {κ : Type} {N : ℕ} {x y : κ → Fv F v} (hx : x ∈ B v κ N) (hy : y ∈ B v κ N) :
    x + y ∈ B v κ N := fun i =>
  (Valuation.map_add _ _ _).trans (max_le (hx i) (hy i))

theorem neg_mem_B {κ : Type} {N : ℕ} {x : κ → Fv F v} (hx : x ∈ B v κ N) : -x ∈ B v κ N := fun i => by
  simpa using hx i

theorem B_mem_nhds (κ : Type) [Fintype κ] (N : ℕ) : B v κ N ∈ 𝓝 (0 : κ → Fv F v) := by
  have : B v κ N = Set.pi Set.univ fun _ => {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} := by
    ext x; simp [B]
  rw [this]
  exact set_pi_mem_nhds Set.finite_univ fun i _ => ball_mem_nhds_zero v N

theorem exists_B_subset (κ : Type) [Fintype κ] {s : Set (κ → Fv F v)} (hs : s ∈ 𝓝 (0 : κ → Fv F v)) :
    ∃ N : ℕ, B v κ N ⊆ s := by
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨I, -, t, ht, hts⟩ := hs
  choose Nf hNf using fun i => exists_ball_subset v (ht i)
  refine ⟨Finset.univ.sup Nf, fun x hx => hts fun i _ => hNf i ?_⟩
  exact (hx i).trans (WithZero.exp_le_exp.2 (by
    have := Finset.le_sup (f := Nf) (Finset.mem_univ i); omega))

theorem isOpen_box (κ : Type) [Fintype κ] (N : ℕ) (c : κ → Fv F v) :
    IsOpen {x : κ → Fv F v | x - c ∈ B v κ N} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have ht : Tendsto (fun y : κ → Fv F v => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  refine Filter.mem_of_superset (ht (B_mem_nhds κ N)) fun y hy => ?_
  have : y - c = (y - x) + (x - c) := by abel
  show y - c ∈ B v κ N
  rw [this]; exact add_mem_B hy hx

theorem exists_invariant {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y u, u ∈ B v κ N → φ (y + u) = φ y := by
  have hloc : ∀ x : κ → Fv F v, ∃ N : ℕ, ∀ u ∈ B v κ N, φ (x + u) = φ x := by
    intro x
    have hlc : IsLocallyConstant fun u : κ → Fv F v => φ (x + u) :=
      hφ.1.comp_continuous (continuous_const_add x)
    have hO : {u : κ → Fv F v | φ (x + u) = φ x} ∈ 𝓝 (0 : κ → Fv F v) :=
      (hlc.isOpen_fiber (φ x)).mem_nhds (by simp)
    obtain ⟨N, hN⟩ := exists_B_subset κ hO
    exact ⟨N, fun u hu => hN hu⟩
  choose Nx hNx using hloc
  have hK : IsCompact (tsupport φ) := hφ.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => {y : κ → Fv F v | y - x ∈ B v κ (Nx x)})
    (fun x => isOpen_box κ (Nx x) x) (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using zero_mem_B κ (Nx y)⟩)
  refine ⟨t.sup Nx, fun N hN y u hu => ?_⟩
  have hsub : ∀ x ∈ t, u ∈ B v κ (Nx x) := fun x hx =>
    B_anti ((Finset.le_sup (f := Nx) hx).trans hN) hu
  by_cases hy : ∃ x ∈ t, y - x ∈ B v κ (Nx x)
  · obtain ⟨x, hx, hyx⟩ := hy
    have h1 : φ (y + u) = φ x := by
      have := hNx x ((y - x) + u) (add_mem_B hyx (hsub x hx))
      rwa [show x + ((y - x) + u) = y + u by abel] at this
    have h2 : φ y = φ x := by
      have := hNx x (y - x) hyx
      rwa [show x + (y - x) = y by abel] at this
    rw [h1, h2]
  · push_neg at hy
    have hyK : y ∉ tsupport φ := fun hyK => by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
      exact hy x hx hyx
    have hyuK : y + u ∉ tsupport φ := fun hyK => by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
      refine hy x hx ?_
      have := sub_mem_B hyx (hsub x hx)
      rwa [show y + u - x - u = y - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hyK, image_eq_zero_of_notMem_tsupport hyuK]

def BG (v : Pl (F := F)) (κ : Type) (N : ℕ) : AddSubgroup (κ → Fv F v) where
  carrier := B v κ N
  add_mem' := add_mem_B
  zero_mem' := zero_mem_B κ N
  neg_mem' := neg_mem_B

theorem mk_eq_iff {κ : Type} {N : ℕ} {x c : κ → Fv F v} :
    (x : (κ → Fv F v) ⧸ BG v κ N) = c ↔ x - c ∈ B v κ N := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have := neg_mem_B h
    rwa [show -(-x + c) = x - c by abel] at this
  · intro h
    have := neg_mem_B h
    rwa [show -(x - c) = -x + c by abel] at this

theorem mem_span_boxes (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (φ : (κ → Fv F v) → ℂ) : φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ
      (Set.range fun c : κ → Fv F v => Set.indicator
        {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) := by
  classical
  intro hφ
  obtain ⟨N₀, hN₀⟩ := exists_invariant hφ
  refine ⟨N₀, fun N hN => ?_⟩
  have hK : IsCompact (tsupport φ) := hφ.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c => {y : κ → Fv F v | y - c ∈ B v κ N})
    (fun c => isOpen_box κ N c) (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using zero_mem_B κ N⟩)
  set Q : Finset ((κ → Fv F v) ⧸ BG v κ N) := t.image (QuotientAddGroup.mk (s := BG v κ N)) with hQ
  have heq : φ = ∑ q ∈ Q, φ q.out • Set.indicator
      {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) := by
    funext x
    have hterm : ∀ q : (κ → Fv F v) ⧸ BG v κ N, (φ q.out • Set.indicator
        {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) x =
        if (x : (κ → Fv F v) ⧸ BG v κ N) = q then φ q.out else 0 := by
      intro q
      have hm : (x ∈ {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))}) ↔
          (x : (κ → Fv F v) ⧸ BG v κ N) = q := by
        rw [← QuotientAddGroup.out_eq' q, mk_eq_iff, QuotientAddGroup.out_eq']
        rfl
      rw [Pi.smul_apply, Set.indicator_apply]
      by_cases h : (x : (κ → Fv F v) ⧸ BG v κ N) = q
      · rw [if_pos (hm.2 h), if_pos h, Pi.one_apply, smul_eq_mul, mul_one]
      · rw [if_neg (fun h' => h (hm.1 h')), if_neg h, smul_zero]
    rw [Finset.sum_apply]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · set q : (κ → Fv F v) ⧸ BG v κ N := (x : (κ → Fv F v) ⧸ BG v κ N)
      have hqx : q.out - x ∈ B v κ N := mk_eq_iff.1 (QuotientAddGroup.out_eq' q)
      have := hN₀ N hN x (q.out - x) hqx
      rw [show x + (q.out - x) = q.out by abel] at this
      exact this.symm
    · have hxK : x ∉ tsupport φ := fun hxK => by
        obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hxK)
        have hcQ : (c : (κ → Fv F v) ⧸ BG v κ N) ∈ Q :=
          Finset.mem_image_of_mem (QuotientAddGroup.mk (s := BG v κ N)) hc
        rw [← mk_eq_iff.2 hxc] at hcQ
        exact hx hcQ
      exact image_eq_zero_of_notMem_tsupport hxK
  rw [heq]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.out, rfl⟩)

end GlobalTheory.BoxDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalExpansion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_local_expansion : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  first | (exact @GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (exact GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (intros; apply GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefFormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_signature_one_preserves_posDef_form : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  first | (exact @GlobalTheory.similitude_preserves_posDef) | (exact GlobalTheory.similitude_preserves_posDef) | (intros; apply GlobalTheory.similitude_preserves_posDef  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixedStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) → (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  first | exact @GlobalTheory.CuspRep.fixed_of_locFixed | exact GlobalTheory.CuspRep.fixed_of_locFixed | (intros; apply GlobalTheory.CuspRep.fixed_of_locFixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarPreservesIntegrality
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_preserves_integrality : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v (starT G.star (Qv v) a).unop := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_star_eventually) | (exact GlobalTheory.OrbFinAf.isIntV_star_eventually) | (intros; apply GlobalTheory.OrbFinAf.isIntV_star_eventually  <;> assumption)
end

