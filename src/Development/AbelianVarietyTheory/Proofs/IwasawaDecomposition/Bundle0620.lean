module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGoodSplitHeckePlaceOfSplitNotExcluded
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 2000000

namespace GlobalTheory.GoodPlaceAtState

theorem natCast_mem_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
  rw [← Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  refine Ideal.subset_span ⟨(n : 𝓞 K), h, ?_⟩
  simp

theorem natCast_mem_of_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal) : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have := natCast_mem_conjPl (Formalism.DivisionValues.conjPl w) n h
  rwa [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this

end GlobalTheory.GoodPlaceAtState

theorem GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (x : St P) (v : PlE (Dof x).host), IsSplitPl (Dof x).host v → v ∉ SbD (Dof x) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace x.m.z.R.toRealDat v := by
  intro K B f T w P x v hs hv
  have hc := x.m.z.pins.char
  have hA := hc.allPl
  have hL := hc.base.lev
  have hlow : ∀ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro k hk
    apply hv
    refine (lowSet_finite (Dof x)).mem_toFinset.2 ⟨(Dof x).host.g k, ?_, ((Dof x).host.g_prime k).ne_zero, hk⟩
    fin_cases k <;> simp [lowAll]
  have hdiv : ∀ PP, PP ∈ x.m.z.R.toRealDat.Sb → ∃ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have hm : PP ∈ x.m.z.R.Pg := by rw [← hA]; exact hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    exact ⟨k, Formalism.L2.Host.PiBar.overP _ hk⟩

  unfold GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace
  refine ⟨⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hs, fun hm => ?_, fun Q hQ he => ?_⟩, fun hm => ?_⟩
  · obtain ⟨k, hk⟩ := hdiv v hm
    exact hlow k hk
  · obtain ⟨k, hk⟩ := hdiv Q hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
    rw [he] at hk
    exact hlow k (GlobalTheory.GoodPlaceAtState.natCast_mem_of_conjPl v _ hk)
  · rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    · exact hlow 0 h
    · exact hlow 1 h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfMulIsHomogeneousOfNeZeroRight
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

theorem isHomogeneous_of_mul_isHomogeneous_right {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ)
    (hQ : Q ≠ 0) (hQh : Q.IsHomogeneous b) (hPQ : (P * Q).IsHomogeneous (a + b)) :
    P.IsHomogeneous a := by
  have key : ∀ k, homogeneousComponent (k + b) (P * Q) = homogeneousComponent k P * Q := by
    intro k
    conv_lhs => rw [← sum_homogeneousComponent P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    have hterm : ∀ i, homogeneousComponent (k + b) (homogeneousComponent i P * Q)
        = if i = k then homogeneousComponent i P * Q else 0 := by
      intro i
      have hm : homogeneousComponent i P * Q ∈ homogeneousSubmodule σ ℝ (i + b) :=
        (homogeneousComponent_isHomogeneous i P).mul hQh
      rw [homogeneousComponent_of_mem hm]
      by_cases h : i = k
      · simp [h]
      · have : k + b ≠ i + b := by omega
        rw [if_neg this, if_neg h]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · subst_vars; rfl
    · simp only [Finset.mem_range, not_lt] at h
      rw [homogeneousComponent_eq_zero k P (by omega), zero_mul]
  have hzero : ∀ k, k ≠ a → homogeneousComponent k P = 0 := by
    intro k hk
    have h1 : homogeneousComponent (k + b) (P * Q) = 0 := by
      have : k + b ≠ a + b := by omega
      have e := homogeneousComponent_of_mem (m := k + b) (hPQ : P * Q ∈ homogeneousSubmodule σ ℝ (a + b))
      rw [e, if_neg this]
    rw [key] at h1
    exact (mul_eq_zero.mp h1).resolve_right hQ
  rw [← sum_homogeneousComponent P]
  apply IsHomogeneous.sum
  intro k _
  by_cases hk : k = a
  · subst hk; exact homogeneousComponent_isHomogeneous k P
  · rw [hzero k hk]; exact isHomogeneous_zero _ _ _

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMarkedBalancedIntFormPullbackIffSplitSurjectio
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.SplitPull

theorem apply_eq_zero_of_isotropic {X : Type} [AddCommGroup X] {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) {d : X} (hd : x d d = 0) (z : X) : x d z = 0 := by
  by_contra h
  have h1 := hp ((-(x d z * (x z z + 1))) • d + z)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hd, hs z d] at h1
  have h2 : 1 ≤ x d z * x d z := mul_self_pos.2 h
  have h3 := hp z
  nlinarith [mul_le_mul_of_nonneg_right h2 (show 0 ≤ x z z + 1 by omega)]

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O}
  {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
  {r : X →ₗ[O] X₁} {s : X₁ →ₗ[O] X}

def pullHom (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_pull (h : ∀ a, r (s a) = a) (β : LinearMap.BilinForm ℤ X₁) : pull s (pull r β) = β :=
  LinearMap.ext₂ fun a b => by simp [h]

theorem pull_injective (h : ∀ a, r (s a) = a) : Function.Injective (pull r) :=
  Function.LeftInverse.injective (pull_pull h)

theorem eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hs : ∀ y z, x y z = x z y) (hp : ∀ y, 0 ≤ x y y) (hv : ∀ y, pull r β y y = 0 → x y y = 0) :
    pull r (pull s x) = x := by
  have key : ∀ a z, x (s (r a)) z = x a z := fun a z => by
    have := apply_eq_zero_of_isotropic hs hp (hv (a - s (r a)) (by simp [h])) z
    rw [map_sub, LinearMap.sub_apply] at this
    omega
  refine LinearMap.ext₂ fun a b => ?_
  rw [pull_apply, pull_apply, key, hs, key, hs]

variable [Module.Finite O X] [Module.Finite O X₁]

theorem inFace_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    InFace bar ψ lab (pull r β) (pull r x) ↔ InFace bar ψ lab β x := by
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have e : pull r β + pull r x = pull r (β + x) := rfl
  unfold InFace
  rw [e]
  simp only [evalZ_pull _ hr, pull_apply]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ x y y)).symm
    (and_congr (hr.forall (p := fun y => β y y = 0 → x y y = 0)).symm Iff.rfl))
  rw [← pull_pull h x]
  exact pull_mem s hx

theorem InFace_eq_pull (h : ∀ a, r (s a) = a) {β : LinearMap.BilinForm ℤ X₁} {x : LinearMap.BilinForm ℤ X}
    (hx : InFace bar ψ lab (pull r β) x) : ∃ x₁, pull r x₁ = x :=
  ⟨_, eq_pull h hx.1.1 hx.2.1 hx.2.2.1⟩

theorem isIndec_pull_iff (h : ∀ a, r (s a) = a) {β x : LinearMap.BilinForm ℤ X₁} :
    IsIndec bar ψ lab (pull r β) (pull r x) ↔ IsIndec bar ψ lab β x := by
  have hne : ∀ y : LinearMap.BilinForm ℤ X₁, pull r y ≠ 0 ↔ y ≠ 0 := fun y =>
    (pull_injective h).ne_iff' (rfl : pull r 0 = 0)
  refine and_congr (inFace_pull_iff h) (and_congr (hne x) ⟨fun H y z hy hz y0 z0 e => ?_, fun H y z hy hz y0 z0 e => ?_⟩)
  · exact H _ _ ((inFace_pull_iff h).2 hy) ((inFace_pull_iff h).2 hz) ((hne y).2 y0) ((hne z).2 z0) (by rw [← e]; rfl)
  · obtain ⟨y, rfl⟩ := InFace_eq_pull h hy
    obtain ⟨z, rfl⟩ := InFace_eq_pull h hz
    exact H y z ((inFace_pull_iff h).1 hy) ((inFace_pull_iff h).1 hz) ((hne y).1 y0) ((hne z).1 z0)
      (pull_injective h e)

theorem isMarked_pull_iff' (h : ∀ a, r (s a) = a) (i : ℕ) (β : LinearMap.BilinForm ℤ X₁) :
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β := by
  classical
  have hr : Function.Surjective r := fun a => ⟨s a, h a⟩
  have hsum : ∀ S : Finset (LinearMap.BilinForm ℤ X₁), ∑ x ∈ S.map ⟨pull r, pull_injective h⟩, x = pull r (∑ x ∈ S, x) :=
    fun S => by
      rw [Finset.sum_map]
      exact (map_sum (pullHom r) (fun x => x) S).symm
  unfold IsMarked
  rw [evalZ_pull _ hr]
  refine and_congr ⟨fun hx => ?_, pull_mem r⟩ (and_congr (hr.forall (p := fun y => 0 ≤ β y y)).symm
    (and_congr ⟨fun H k β' e => H k (pull r β') (by rw [← e]; rfl), fun H k β' e => H k (pull s β') ?_⟩
      (and_congr Iff.rfl ⟨?_, ?_⟩)))
  · rw [← pull_pull h β]
    exact pull_mem s hx
  · rw [← pull_pull h β, ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    have hS' : (S.preimage (pull r) (pull_injective h).injOn).map ⟨pull r, pull_injective h⟩ = S := by
      ext x
      simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
      refine ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ?_⟩
      obtain ⟨y, rfl⟩ := InFace_eq_pull h ((hS x).1 hx).1
      exact ⟨y, hx, rfl⟩
    refine ⟨S.preimage (pull r) (pull_injective h).injOn, fun x => ?_, k, hk, pull_injective h ?_⟩
    · rw [Finset.mem_preimage, hS, isIndec_pull_iff h]
    · rw [← hsum, hS', ← e]; rfl
  · rintro ⟨S, hS, k, hk, e⟩
    refine ⟨S.map ⟨pull r, pull_injective h⟩, fun x => ?_, k, hk, ?_⟩
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (isIndec_pull_iff h).2 ((hS y).1 hy)
      · intro hx
        obtain ⟨y, rfl⟩ := InFace_eq_pull h hx.1
        exact ⟨y, (hS y).2 ((isIndec_pull_iff h).1 hx), rfl⟩
    · rw [hsum, ← e]; rfl

theorem isMarked_pull_iff : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ) (X X₁ : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁]
    (r : X →ₗ[O] X₁) (s : X₁ →ₗ[O] X), (∀ a, r (s a) = a) → ∀ β : LinearMap.BilinForm ℤ X₁,
    IsMarked bar ψ lab i X (pull r β) ↔ IsMarked bar ψ lab i X₁ β :=
  fun _ _ _ _ _ i _ _ _ _ _ _ _ _ _ _ h β => isMarked_pull_iff' h i β

end GlobalTheory.PolFan.Mark.SplitPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.RayPrimeOfNorm

theorem isRayPrime_of_norm_eq : ∀ (D : D7) (i : Fin 2) (jE : D.host.E →+* Qb), (D.host.g i).Prime → (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧ (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) → IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g i) := by
  intro D i jE hp ⟨π, hK, hnorm, hm⟩
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : IsScalarTower ℚ D.host.E Qb := IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ Qb) (jE.comp (algebraMap ℚ D.host.E))) x
  let σ : Qb →ₐ[ℚ] Qb := (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).liftNormal Qb
  have hσ : ∀ x : D.host.E, σ (jE x) = jE (D.host.conj x) := fun x =>
    AlgHom.liftNormal_commutes (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) Qb x
  refine ⟨hp, jE (π : D.host.E), (IntermediateField.mem_map _).2 ⟨_, hK, rfl⟩, ?_, ?_, σ, ?_⟩
  · exact (RingOfIntegers.isIntegral_coe π).map jE.toIntAlgHom
  · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hm0 : (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = 0
    · rw [hm0, div_zero]; exact isIntegral_zero
    · have e : (jE (π : D.host.E) - 1) / (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = jE (y : D.host.E) := by
        rw [div_eq_iff hm0]
        have e1 := congrArg (fun z : 𝓞 D.host.E => jE (algebraMap (𝓞 D.host.E) D.host.E z)) hy
        simp only [map_mul, map_sub, map_one, map_natCast] at e1
        push_cast at e1 ⊢
        exact e1.symm
      rw [e]
      exact (RingOfIntegers.isIntegral_coe y).map jE.toIntAlgHom
  · rw [hσ, ← map_mul, hnorm, map_natCast]

end GlobalTheory.RayPrimeOfNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRecGOfIsLocalFamily
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.LocalPack GlobalTheory.Mem.ConcreteRecord

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

def IsLocalFamily (sc : Scale) (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (g : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w)) : Prop :=
  ∃ (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (B : GL (Fin D.R.k) D.host.E)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]),
    Cmp.StdB D B ∧
    (∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B) ∧
    (∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z)) ∧
    (∀ u w hg, (packC D (fun u => L0 u) I ψ u w hg).posOK (iK u w hg) (lam u w hg)) ∧
    (∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (L0 u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (nFr D (D.what₂.places.resChar w))) (ψ u w hg)) ∧
    g = gatOf D L0 I ψ sc


set_option maxHeartbeats 4000000 in
theorem exists_isLocalFamily (sc : Scale) {D : D7} {L0 : LevelData D} (T : ∀ u : D.what₂.Word, Forms0 D u)
    (hS : Formalism.L2.Herm.StdTied D) (hC : Companion D L0) (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) :
    ∃ g, (∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0) ∧ IsLocalFamily sc D L0 T g :=
  ⟨gatOf D L0 (placeId D L0 hS hC) (awayChar D L0 T hJ hψ) sc, gatOf_d D L0 T hJ _ _ sc,
    placeId D L0 hS hC, awayChar D L0 T hJ hψ, stdBasis D hS, embK D L0, embAlg D L0, stdBasis_std D hS, fun _ _ _ _ _ => rfl,
    embK_embAlg D L0, posOK_placeId hS hC _,
    fun u w hg => Classical.choose_spec (GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ hψ u w hg), rfl⟩


set_option maxHeartbeats 32000000 in
theorem isRecG_of_isLocalFamily {sc : Scale} {D : D7} {L0 : LevelData D} {T : ∀ u : D.what₂.Word, Forms0 D u}
    (hJ : ∀ u, Joint0 L0 u (T u)) (hψ : ∀ u, LevelZeroCharacterRational T u) {g} (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (h : IsLocalFamily sc D L0 T g) :
    ∃ (Gt : GatTies (setGat D g hd)) (c : LatCmp (setGat D g hd)) (G : GroupCompatibilityAll (setGat D g hd) Gt c),
      IsRecG sc (setGat D g hd) Gt c G.herm G.forms ∧ (∀ u, G.herm.lev0 u = L0 u) ∧ (∀ u, G.forms u = forms0Set D g hd (T u)) ∧
      ∀ u w hg (v : Fin ((setGat D g hd).gat u w hg).P.nV) (s : Fin (((setGat D g hd).gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
        x ∈ ((G.herm.g u w hg).pl v).1.asIdeal ↔
          (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (setGat D g hd) (Gt.gat_pos u w hg ⟨v, s⟩)
            (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  obtain ⟨I, ψ, B, iK, lam, hBs, hB, hK, hPos, hψ', rfl⟩ := h
  let H0 : Formalism.L2.Herm.Herm0 (recC D sc 1 (fun u => L0 u) I ψ hd) :=
    ⟨fun u => L0 u, levTieG D sc 1 (fun u => L0 u) (packC D (fun u => L0 u) I ψ) hd⟩
  let T' : ∀ u, Forms0 (recC D sc 1 (fun u => L0 u) I ψ hd) u := fun u => forms0Set D (gatOf D L0 I ψ sc) hd (T u)
  have CH := Test.comparison_statements D sc (fun u => L0 u) I ψ hd H0 (fun _ => rfl) T' B hBs hB iK lam hK hPos hJ hψ hψ'
  have hpos := fun u w hg v s x => pos_C D sc 1 (fun u => L0 u) I ψ hd H0 (fun _ => rfl) B hBs hB iK lam hK hPos u w hg v s x
  exact ⟨gatTiesC D sc 1 (fun u => L0 u) I ψ hd, _,
    groupCompatibilityOfRecursion D sc 1 (fun u => L0 u) I ψ hd H0 (fun _ => rfl) T' B hBs hB (CH.toHyp0 hpos).toHyp
      (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)),
    LayerTwoModel.isRecG_retie ⟨D, fun u => L0 u, I, ψ, hd, H0, fun _ => rfl, T', B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩ _,
    fun _ => rfl, fun _ => rfl,
    fun u w hg v s x => GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos D sc 1 (fun u => L0 u) I ψ hd H0 (fun _ => rfl) B hBs hB iK lam hK hPos u w hg v s x⟩

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.JumpsAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lg_of_forall {K : Ctx} {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, p B f T) : large₂ K p :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => h B f T⟩

theorem evLgG_of_forall {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ K B f T, p K B f T) : EvLgG p :=
  evLgG_of_evLg ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0,
    fun _ _ => ⟨0, fun K _ _ _ _ _ => lg_of_forall (h K)⟩⟩⟩⟩⟩

end GlobalTheory.HeightCounting.JumpsAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelTaylorSeriesPreservedDivisionLatticeChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.WitTr


set_option maxHeartbeats 8000000 in
theorem kerT_entC_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B}
    (w : ColW B f T) (Z : w.Lt) (t : ColT w Z) (Y : DivX (w.D Z)) (Gy : G.LatInst (w.D Z))
    (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) (k : KerT t Y Gy ker)
    (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ),
    EntC k → ∃ k' : KerT (DivTr.colTTr w Z N h t) (DivTr.divTrZ w Z N h Y)
      (DivTr.latTrZ w Z N h Gy) (DivTr.kerTr w Z N h ker), EntC k' := by
  intro B f T w Z t Y Gy ker k N h hE
  exact ⟨DivTr.ktTr w Z N h k, DivTr.entC_tr w Z N h k hE⟩

end GlobalTheory.Mem.Top.Bl.WitTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamCopy
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.SideCopy.LamCopy
open GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  have he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) := fun x => (h.cp.embLL0_eq x).symm
  have nOm := h.cp.gal.Om
  have ninstOm := h.cp.gal.instOm
  have nalgOm := h.cp.gal.algOm
  have nplOm := h.cp.gal.plOm
  have nPlG := h.cp.gal.PlG
  have hR := h.cp.gal.R
  have hhost := h.cp.gal.host
  have hTau := h.cp.Tau
  have heTau := h.cp.eTau
  have hhc := h.cp.hc
  have hinW1 := h.cp.inW1
  have hemb0 := h.cp.emb0
  have hTw := h.cp.set.Tw
  obtain ⟨xcc, _, _, _, _, xalgO0, xtopO0, _, _, _, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, _, xhEig, _, _, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.cp.set
  have hjL := h.jL
  have hs2 := h.s2
  have hlamG := h.lamG
  have hXv := h.Xv
  have hqs := h.qs
  have hl := h.cp.set.l
  have hO0 := h.cp.set.O0
  have hcrO0 := h.cp.set.crO0
  have hab := h.cp.set.abelian₂
  have hsideL := h.cp.set.sideL
  have hO := h.cp.set.O
  have hcrO := h.cp.set.crO
  have halgO := h.cp.set.algO
  have hS0 := h.cp.set.S0
  cases D; cases D'
  dsimp only at hR hhost
  subst hR; subst hhost
  rename Rows.Data _ => r1; cases r1; rename Rows.Data _ => r2; cases r2
  dsimp only at hTau
  subst hTau
  dsimp only at heTau hhc
  subst heTau; subst hhc
  rename NData _ _ _ => nd1; cases nd1
  rename NData _ _ _ => nd2; cases nd2
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => n1; cases n1
  rename NTw _ _ _ _ _ => n2; cases n2
  dsimp only at xcc
  subst xcc
  dsimp only at hTw hl hO0 hcrO0 hab hsideL hO hcrO halgO hS0
  subst hTw; subst hl; subst hO0; subst hcrO0; subst hab; subst hsideL; subst hO; subst hcrO; subst hS0
  dsimp only at xalgO0 xtopO0 xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS xhEig xRCG xgrpRCG xfinRCG xart xth hjL hs2 hlamG hXv hqs halgO
  subst xalgO0; subst xtopO0; subst halgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst xhEig; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hjL; subst hs2; subst hlamG; subst hXv; subst hqs
  cases C; cases cf'  
  dsimp only at f1 f2 f3 f4
  subst f1; subst f2; subst f3; subst f4
  refine ⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((hinW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩
  exact (congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))

end GlobalTheory.HeightCounting.SideCopy.LamCopy
end

