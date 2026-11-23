module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDualExponentialLeOfAinfValued
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialExistsUniqueCyclotomicLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualSelmerClassNotKilled
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.DualClass

section Algebra

noncomputable def chr {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n) (y' : B') :
    AddChar B ℂ := (ZMod.stdAddChar (N := n)).compAddMonoidHom (P.flip y')

theorem chr_injective {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n)
    (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Function.Injective (chr P) := by
  intro u v huv
  refine sub_eq_zero.1 (h _ fun y => ?_)
  rw [map_sub, sub_eq_zero]
  exact ZMod.injective_stdAddChar (DFunLike.congr_fun huv y)

theorem card_addChar (B : Type) [AddCommGroup B] [Finite B] : Nat.card (AddChar B ℂ) = Nat.card B := by
  classical
  have := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card (α := AddChar B ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]

theorem card_le_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Nat.card B' ≤ Nat.card B := by
  rw [← card_addChar B]
  exact Nat.card_le_card_of_injective _ (chr_injective P h)

theorem left_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) (hc : Nat.card B ≤ Nat.card B') (y : B)
    (hy : ∀ y', P y y' = 0) : y = 0 := by
  have hb := (chr_injective P h).bijective_of_nat_card_le (by rw [card_addChar]; exact hc)
  refine AddChar.forall_apply_eq_zero.1 fun ψ => ?_
  obtain ⟨y', rfl⟩ := hb.2 ψ
  change ZMod.stdAddChar (P y y') = 1
  rw [hy, AddChar.map_zero_eq_one]

variable {A : Type} [CommRing A]

theorem card_ker_eq_coker {M : Type} [AddCommGroup M] [Module A M] [Finite M] (f : M →ₗ[A] M) :
    Nat.card (LinearMap.ker f) = Nat.card (M ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h3 : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right h3 ?_
  rw [← h1, mul_comm, ← h2]

abbrev Quo (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Type := Y ⧸ LinearMap.range (LinearMap.lsmul A Y c)

abbrev Tor (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Submodule A Y := LinearMap.ker (LinearMap.lsmul A Y c)

variable {n : ℕ} {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y']

theorem exists_induced (β : Y →+ Y' →+ ZMod n) (hβ : Bal A β) (c : A) :
    ∃ β₂ : Quo c Y →+ Tor c Y' →+ ZMod n, ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1 := by
  let P : Y →+ Tor c Y' →+ ZMod n := (β.flip.comp (Tor c Y').subtype.toAddMonoidHom).flip
  refine ⟨QuotientAddGroup.lift (LinearMap.range (LinearMap.lsmul A Y c)).toAddSubgroup P ?_, fun y y' => rfl⟩
  rintro _ ⟨y, rfl⟩
  refine AddMonoidHom.mem_ker.2 (AddMonoidHom.ext fun y' => ?_)
  change β (c • y) y'.1 = 0
  have h : c • y'.1 = 0 := y'.2
  rw [hβ, h, map_zero]

theorem perf_induced [NeZero n] [Finite Y] [Finite Y'] (β : Y →+ Y' →+ ZMod n) (hβ : Perf A β) (c : A)
    (β₂ : Quo c Y →+ Tor c Y' →+ ZMod n) (h : ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1) : Perf A β₂ := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have : Finite (Quo c Y') := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hr : ∀ y', (∀ y, β₂ y y' = 0) → y' = 0 := fun y' hy =>
    Subtype.ext (hβ.2.2 _ fun y => by rw [← h, hy])
  refine ⟨fun a y y' => ?_, left_of_right β₂ hr ?_, hr⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, h, h, hβ.1]
    rfl
  · obtain ⟨γ, hγ⟩ := exists_induced (A := A) β.flip (fun a y' y => (hβ.1 a y y').symm) c
    rw [← card_ker_eq_coker, card_ker_eq_coker (LinearMap.lsmul A Y' c)]
    exact card_le_of_right γ fun y hy => Subtype.ext (hβ.2.1 _ fun y' => by
      have := hy (Submodule.Quotient.mk y')
      rwa [hγ] at this)

theorem smul_mem_range [Finite Y] {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : Nat.card (LinearMap.ker (matAct (M := Y) Φ)) ≤ Nat.card (LinearMap.ker (matAct (M := Quo c Y) Φ)))
    (w : Fin a → Y) : c • w ∈ LinearMap.range (matAct (M := Y) Φ) := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [card_ker_eq_coker, card_ker_eq_coker] at h
  let f : (Fin a → Y) →ₗ[A] (Fin a → Quo c Y) := (Submodule.mkQ _).compLeft (Fin a)
  have hf : LinearMap.range (matAct (M := Y) Φ) ≤ (LinearMap.range (matAct (M := Quo c Y) Φ)).comap f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨f x, funext fun b => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [f, matAct, map_sum]
  have hs : Function.Surjective (Submodule.mapQ _ _ f hf) := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    choose u hu using fun b => Submodule.Quotient.mk_surjective _ (x b)
    exact ⟨Submodule.Quotient.mk u, by rw [Submodule.mapQ_apply]; exact congrArg _ (funext hu)⟩
  have : Finite ((Fin a → Y) ⧸ LinearMap.range (matAct (M := Y) Φ)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hb := hs.bijective_of_nat_card_le h
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hb.1
  rw [map_zero, Submodule.mapQ_apply]
  have h0 : f (c • w) = 0 := funext fun b => (Submodule.Quotient.mk_eq_zero _).2 ⟨w b, rfl⟩
  rw [h0, Submodule.Quotient.mk_zero]

theorem mul_eq_zero_of_range (β : Y →+ A →+ ZMod n) (hβ : Perf A β) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : ∀ w : Fin a → Y, c • w ∈ LinearMap.range (matAct (M := Y) Φ)) (y₀ : Fin a → A) (h0 : Matrix.vecMul y₀ Φ = 0)
    (j : Fin a) : c * y₀ j = 0 := by
  refine hβ.2.2 _ fun w => ?_
  obtain ⟨x, hx⟩ := h (Pi.single j w)
  have h1 : ∑ b, y₀ b • matAct Φ x b = 0 := by
    change ∑ b, y₀ b • ∑ k, Φ b k • x k = 0
    simp only [Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h2 : ∑ b, y₀ b * Φ b k = 0 := congrFun h0 k
    rw [← Finset.sum_smul, h2, zero_smul]
  rw [hx, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)] at h1
  have h3 : (c * y₀ j) • w = 0 := by
    rw [mul_comm, mul_smul]
    simpa using h1
  have h4 := hβ.1 (c * y₀ j) w 1
  rw [h3, smul_eq_mul, mul_one] at h4
  rw [← h4]
  simp

end Algebra

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host))

theorem card_selOn {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (Z : GE N → Matrix (Fin D.R.r) (Fin a) A)
    (h : Univ bkP i s κ Q Φ Z) (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] :
    Nat.card (LinearMap.ker (matAct (M := Y) Φ)) = Nat.card (selOn bkP i (Tgl i s) κ Y Q) := by
  obtain ⟨h1, h2, h3⟩ := h Y
  choose z hz hz' using fun x : LinearMap.ker (matAct (M := Y) Φ) => h1 x.1 x.2
  refine Nat.card_eq_of_bijective (fun x => ⟨_, hz' x⟩) ⟨fun x x' hx => ?_, fun q => ?_⟩
  · have e := (Submodule.Quotient.eq _).1 (congrArg Subtype.val hx)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 e
    refine sub_eq_zero.1 (Subtype.ext (h2 _ (x - x').2 ⟨m, fun g => ?_⟩))
    rw [← hm g]
    change _ = (z x).1 g - (z x').1 g
    rw [hz, hz]
    funext b
    simp [rect, smul_sub]
  · obtain ⟨q, hq⟩ := q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx, m, hm⟩ := h3 y.1 ⟨y, rfl, hq⟩
    refine ⟨⟨x, hx⟩, Subtype.ext (Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)))⟩
    rw [← hm g]
    change y.1 g - (z ⟨x, hx⟩).1 g = _
    rw [hz]


omit [Algebra (X.O0 i) A] in
theorem card_invariants_torsion_submodule {Γ O : Type} [Group Γ] [CommRing O] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ)
    (U : Subgroup Γ) (Y' : Type) [AddCommGroup Y'] [Module A Y'] (c : A)
    (h : ∀ m, (∀ g ∈ U, repOn ρ κ Y' g m = m) → c • m = 0) :
    Nat.card (H0 ((repOn ρ κ (Tor c Y')).comp U.subtype)) = Nat.card (H0 ((repOn ρ κ Y').comp U.subtype)) := by
  refine Nat.card_eq_of_bijective (fun m => ⟨(Tor c Y').subtype.compLeft (Fin r) m.1, fun g => ?_⟩)
    ⟨fun m m' hm => ?_, fun m => ?_⟩
  · exact (repOn_map ρ κ (Tor c Y').subtype g.1 m.1).symm.trans (congrArg _ (m.2 g))
  · exact Subtype.ext (funext fun b => Subtype.ext (congrFun (congrArg Subtype.val hm) b))
  · have h0 := h m.1 fun g hg => m.2 ⟨g, hg⟩
    refine ⟨⟨fun b => ⟨m.1 b, congrFun h0 b⟩, fun g => funext fun b => Subtype.ext ?_⟩, rfl⟩
    exact (congrFun (repOn_map ρ κ (Tor c Y').subtype g.1 _) b).trans (congrFun (m.2 g) b)

theorem exists_not_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))), Perf A β → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (c t : A) (y₀ : Fin a → A) (j : Fin a), (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ A g m = m) → t • m = 0) → Matrix.vecMul y₀ Φ = 0 → c * t * y₀ j ≠ 0 → ∃ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y ∧ ¬ Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) := by
  intro D N X bkP i s A _ _ _ _ _ _ κ Q ρ hS hK hD hN hO Y _ _ _ _ _ β hβ a Φ Z hU c t y₀ j ht h0 hne
  by_contra hcon
  have hcob : ∀ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) :=
    fun y hy => by_contra fun h => hcon ⟨y, hy, h⟩
  haveI : NeZero (X.l i ^ (nu X i + 1)) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  letI : TopologicalSpace (Quo (c * t) Y) := ⊥
  haveI : DiscreteTopology (Quo (c * t) Y) := ⟨rfl⟩
  haveI : Finite (Quo (c * t) Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  obtain ⟨β₂, hβ₂⟩ := exists_induced β hβ.1 (c * t)
  have hP := perf_induced β hβ (c * t) β₂ hβ₂
  obtain ⟨-, e1⟩ := hO Y A β hβ
  obtain ⟨f2, e2⟩ := hO (Quo (c * t) Y) (Tor (c * t) A) β₂ hP
  have hsub : DualCl bkP i s κ ρ β Q ⊆ h1Map ρ κ⁻¹ (Tor (c * t) A).subtype '' DualCl bkP i s κ ρ β₂ Q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y₂, hy₂, m, hm⟩ := _root_.GlobalTheory.DualSub.dualSel_of_smul_cob D N X bkP i s A κ Q ρ hS hK hD hN Y A (Quo (c * t) Y) (Tor (c * t) A) β β₂
      (Submodule.mkQ _) (Tor (c * t) A).subtype c t hβ.1 hP.1 (Submodule.mkQ_surjective _) (Submodule.injective_subtype _)
      (fun y' h => ⟨⟨y', h⟩, rfl⟩) hβ₂ ht y hy (hcob y hy)
    exact ⟨_, ⟨y₂, hy₂, rfl⟩, Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, hm⟩))⟩
  have hfin : (DualCl bkP i s κ ρ β₂ Q).Finite := f2
  have hle : Nat.card (DualCl bkP i s κ ρ β Q) ≤ Nat.card (DualCl bkP i s κ ρ β₂ Q) :=
    (Set.ncard_le_ncard hsub (hfin.image _)).trans (Set.ncard_image_le hfin)
  have hprod : ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ (Tor (c * t) A)).comp (DecV N v).subtype)) =
      ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ A).comp (DecV N v).subtype)) :=
    Finset.prod_congr rfl fun v hv => card_invariants_torsion_submodule ρ κ⁻¹ (DecV N v) A (c * t) fun m hm => by
      rw [mul_smul, ht v (Or.inr hv) m hm, smul_zero]
  refine hne (mul_eq_zero_of_range β hβ Φ (c * t) (smul_mem_range Φ (c * t) ?_) y₀ h0 j)
  rw [card_selOn bkP i s κ Q Φ Z hU, card_selOn bkP i s κ Q Φ Z hU, e1, e2, hprod]
  exact Nat.mul_le_mul_right _ hle

end GlobalTheory.NewPrime.DualClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEPowMulFrobMemRightDivisorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def boundedCoeffSeries (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] : Subalgebra O K⟦X⟧ where
  carrier := {f | ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c}
  mul_mem' hf hg := Hom.bdd_mul hf hg
  add_mem' hf hg := Hom.bdd_add hf hg
  algebraMap_mem' c := ⟨1, (A O K).algebraMap_mem c⟩

theorem Hom.exists_E_pow_mul_frob_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet (τ - 1), E K l e ^ M * frob K l h ∈ F.rdivSet τ := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have key : ∀ {μ : Type} [Fintype μ] (Y : ZMod a → Matrix μ μ K⟦X⟧),
      (∀ τ i j, Y τ i j ∈ invE l e (A O K)) → ∃ n : ℕ, ∀ τ i j, E K l e ^ n * Y τ i j ∈ A O K := by
    intro μ _ Y hY
    choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
    refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (hn (τ, i, j))
  obtain ⟨n₁, hn₁⟩ := key P.mx P.mx_mem
  obtain ⟨n₂, hn₂⟩ := key Q.mxInv Q.mxInv_mem
  refine ⟨n₁ + n₂, fun τ h hh => ?_⟩
  obtain ⟨hb, Y, ⟨c, hc⟩, hF⟩ := hh
  have hA : ∀ f ∈ A O K, f ∈ boundedCoeffSeries O K := fun f hf => ⟨1, hf⟩
  have hfr : ∀ f ∈ boundedCoeffSeries O K, frob K l f ∈ boundedCoeffSeries O K := by
    rintro f ⟨d, hd⟩
    refine ⟨d, fun n => ?_⟩
    rw [coeff_frob]
    split_ifs
    · exact hd _
    · simpa using (norm_nonneg _).trans (hd 0)
  have hE : E K l e ∈ A O K := E_mem l e _
  refine ⟨mul_mem (hA _ (pow_mem hE _)) (hfr _ hb),
    (E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ), ?_, ?_⟩
  · have hmem : ∀ i j, ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ)) i j ∈
        boundedCoeffSeries O K := by
      intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      exact sum_mem fun k _ => mul_mem (sum_mem fun m _ =>
        mul_mem (hA _ (hn₁ τ i m)) (hfr _ ⟨c, fun n => hc m k n⟩)) (hA _ (hn₂ τ k j))
    choose d hd using hmem
    obtain ⟨D, hD⟩ := Finite.exists_le (fun p : ι × κ => d p.1 p.2)
    exact ⟨D, fun i j n => (hd i j n).trans (hD (i, j))⟩
  · have hmap : (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) =
        frob K l h • (1 : Matrix κ κ K⟦X⟧) := by
      have h1 : (F.mat (τ - 1) * Y).map (frob K l) = (F.mat (τ - 1)).map (frob K l) * Y.map (frob K l) :=
        Matrix.map_mul (f := (frob K l).toRingHom)
      rw [← h1, hF]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    calc F.mat τ * ((E K l e ^ n₁ • P.mx τ) * Y.map (frob K l) * (E K l e ^ n₂ • Q.mxInv τ))
        = (E K l e ^ n₁ * E K l e ^ n₂) • ((F.mat τ * P.mx τ) * Y.map (frob K l) * Q.mxInv τ) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = (E K l e ^ n₁ * E K l e ^ n₂) •
          (Q.mx τ * ((F.mat (τ - 1)).map (frob K l) * Y.map (frob K l)) * Q.mxInv τ) := by
          rw [F.comm, Matrix.mul_assoc (Q.mx τ)]
      _ = (E K l e ^ (n₁ + n₂) * frob K l h) • (1 : Matrix κ κ K⟦X⟧) := by
          rw [hmap, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mx_mul_mxInv, smul_smul, pow_add]

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem E_pow_mem_RpiE (N : ℕ) : E K l e ^ N ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (pow_mem (E_mem l e (A O K)) N))

theorem E_mem_RpiE : E K l e ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (E_mem l e (A O K)))

theorem hat_E_pow (N : ℕ) :
    hat O l e (E K l e ^ N) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N := by
  induction N with
  | zero => simpa using (hat_coe (O := O) (K := K) l e 1).trans (map_one _)
  | succ n ih =>
    rw [pow_succ, hat_mul l e (E_pow_mem_RpiE n) E_mem_RpiE, ih, hat_E, pow_succ]

theorem main [NeZero a] (P : PhiMod O K l e a ι) :
    ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e), ∀ τ j i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i) := by
  choose n hn using fun p : ZMod a × ι × ι => mem_away.1 (P.mxInv_mem p.1 p.2.1 p.2.2)
  have hN : ∀ p : ZMod a × ι × ι, E K l e ^ Finset.univ.sup n * P.mxInv p.1 p.2.1 p.2.2 ∈ A O K := by
    intro p
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ p))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn p)
  refine ⟨Finset.univ.sup n, fun τ j i => ofA O K l e ⟨_, hN (τ, j, i)⟩, fun τ j i => ?_⟩
  rw [← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

end Gen

end GlobalTheory.BK.CoordInv

open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P
  exact GlobalTheory.BK.CoordInv.main P
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExpStarZeroNear
section
noncomputable section

namespace GlobalTheory.Cyc.ExpScalar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem expStar_mul_sub (LT : LocTheory) (G : Subgroup (GQ l)) (e : ℕ) (c : ℚ_[l])
    {z z' : GQ l → ℚ_[l]} {α α' : Om l} (h : ExpStar LT G e z α) (h' : ExpStar LT G e z' α') :
    ExpStar LT G e (fun σ => c * z σ - z' σ) (algebraMap ℚ_[l] (Om l) c * α - α') := by
  obtain ⟨⟨c1, -, m⟩, b, hb, H⟩ := h
  obtain ⟨⟨c', -, m'⟩, b', hb', H'⟩ := h'
  have hs : ∀ (n : ℤ) (x : (LT l).R.BdR), x ∈ ((LT l).PD (botExt l)).Fil n →
      algebraMap ℚ_[l] (LT l).R.BdR c * x ∈ ((LT l).PD (botExt l)).Fil n := by
    intro n x hx
    have := ((LT l).PD (botExt l)).Fil n |>.smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 c) hx
    rwa [algebraMap_smul, Algebra.smul_def] at this
  refine ⟨⟨(continuousOn_const.mul c1).sub c', fun _ _ => trivial, fun g hg h hh => ?_⟩,
    algebraMap ℚ_[l] (LT l).R.BdR c * b - b', Submodule.sub_mem _ (hs _ _ hb) hb',
    fun σ hσ => ?_⟩
  · simp only [m g hg h hh, m' g hg h hh]; ring
  · have := Submodule.sub_mem _ (hs _ _ (H σ hσ)) (H' σ hσ)
    convert this using 1
    simp only [map_sub, map_mul, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]; ring

theorem exponent_le (s e : ℕ) :
    ((e * (s + 1) + padicValNat l e.factorial + 1 + s : ℕ) : ℝ) + (e : ℝ) / ((l : ℝ) - 1) ≤
      (((((e + 2) * s + padicValNat l e + e / (l - 1) + 1 : ℕ) : ℤ) - betaE l s e : ℤ) : ℝ) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (e : ℝ) / ((l : ℝ) - 1) ≤ ((e / (l - 1) : ℕ) : ℝ) + 1 := by
    have h2 := Nat.lt_floor_add_one ((e : ℝ) / ((l - 1 : ℕ) : ℝ))
    rw [Nat.floor_div_eq_div, Nat.cast_sub (by omega), Nat.cast_one] at h2
    exact h2.le
  generalize e / (l - 1) = q at h1
  rcases e with _ | e
  · have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    simp [betaE, Nat.padicValNat_def]
    linarith
  · have h3 : padicValNat l (e + 1).factorial = padicValNat l (e + 1) + padicValNat l e.factorial := by
      rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero _)]
    rw [h3]
    simp only [betaE, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    generalize padicValNat l (e + 1) = u
    generalize padicValNat l e.factorial = v
    push_cast at h1 ⊢
    linarith

theorem exists_expStar_zero_near : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z → (∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR (z σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1)) → ∃ z' : GQ l → ℚ_[l], ExpStar D.loc (Gj K s) e z' 0 ∧ ∀ σ ∈ Gj K s, ‖z' σ - (l : ℚ_[l]) ^ ((e + 2) * s + padicValNat l e + e / (l - 1) + 1) * z σ‖ ≤ 1 := by
  intro D _ _ l _ K s hs e z hz hb
  obtain ⟨α, hα, hE⟩ := (_root_.GlobalTheory.ExpDef.expStar_existsUnique D l K s hs e).1 z hz
  have hN := _root_.GlobalTheory.Cyc.ExpBound.norm_expStar_le D l K s hs e z α hα hE hb
  have hx := exponent_le (l := l) s e
  set a : ℕ := (e + 2) * s + padicValNat l e + e / (l - 1) + 1 with ha
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hnl : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  have hmem : (l : Om l) ^ ((a : ℤ) - betaE l s e) * α ∈ Ks K s :=
    mul_mem (zpow_mem (natCast_mem _ _) _) hα
  have hnorm : ‖(l : Om l) ^ ((a : ℤ) - betaE l s e) * α‖ ≤ 1 := by
    have h1 := hN.trans (Real.rpow_le_rpow_of_exponent_le hl.le hx)
    rw [Real.rpow_intCast] at h1
    rw [norm_mul, norm_zpow, hnl, inv_zpow, inv_mul_le_iff₀ (zpow_pos (by linarith) _), mul_one]
    exact h1
  obtain ⟨z1, hz1, hE1⟩ := _root_.GlobalTheory.ExpImage.expStar_image D l K s hs e _ hmem hnorm
  refine ⟨fun σ => (l : ℚ_[l]) ^ a * z σ - z1 σ, ?_, fun σ hσ => ?_⟩
  · have := expStar_mul_sub D.loc (Gj K s) e ((l : ℚ_[l]) ^ a) hE hE1
    convert this using 1
    rw [← mul_assoc, ← zpow_add₀ hl0, add_sub_cancel, zpow_natCast, map_pow, map_natCast, sub_self]
  · simpa using hz1 σ hσ

end GlobalTheory.Cyc.ExpScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConj
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LiftKur

theorem exists_gal_fix_Kur_map : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  intro l _ x y hy
  haveI : Algebra.IsAlgebraic ↥(MaximalUnramifiedExtension l) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) ↥(MaximalUnramifiedExtension l)
  haveI : IsAlgClosure ↥(MaximalUnramifiedExtension l) (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ↥(MaximalUnramifiedExtension l) (Om l) := IsAlgClosure.normal _ _
  have hx : IsIntegral ↥(MaximalUnramifiedExtension l) x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly ↥(MaximalUnramifiedExtension l) x = minpoly ↥(MaximalUnramifiedExtension l) y :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx))
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥(MaximalUnramifiedExtension l)) (E := Om l) (x := y) (y := x)).1 hmin.symm
  refine ⟨τ.restrictScalars ℚ_[l], ?_, ?_⟩
  · intro z hz
    show τ z = z
    exact τ.commutes ⟨z, hz⟩
  · show τ x = y
    exact hτ

end GlobalTheory.LiftKur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralInversePowerSeriesOfUnitConstantCo
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem powerSeries_inv_coeff_norm_le_one :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) →
      ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1 := by
  intro K _ _ f hf hc
  have hc0 : constantCoeff f ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  refine ⟨f⁻¹, ?_, PowerSeries.mul_inv_cancel f hc0⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · rw [norm_inv, hc, inv_one]
    · rw [norm_mul, norm_neg, norm_inv, hc, inv_one, one_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x hx => ?_
      split_ifs with hlt
      · rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hlt)
      · rw [norm_zero]; exact zero_le_one

end GlobalTheory
end

