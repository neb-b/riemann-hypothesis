module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularQuotientNearPrimeFiniteTypeInt
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem generically_regular_quotient_of_finiteType_int :
    ∀ (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧
      ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
        IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
  intro B _ _ p hp
  by_cases h : ∀ a : ℤ, algebraMap ℤ B a ∈ p → a = 0
  · exact _root_.GlobalTheory.prime_generically_regular_quotient ℤ B p h
  push_neg at h
  obtain ⟨a, ha, ha0⟩ := h
  have hP : (p.comap (algebraMap ℤ B)) ≠ ⊥ := by
    intro hb
    apply ha0
    have : a ∈ p.comap (algebraMap ℤ B) := ha
    rw [hb] at this
    simpa using this
  obtain ⟨x, hx, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.IsPrime.comap _) hP
  set l := x.natAbs with hl
  have hlp : l.Prime := Int.prime_iff_natAbs_prime.mp hxp
  haveI : Fact l.Prime := ⟨hlp⟩
  have hlmem : (l : B) ∈ p := by
    have hx' : algebraMap ℤ B x ∈ p := hx
    rcases Int.natAbs_eq x with h1 | h1
    · rw [h1] at hx'
      simpa [hl] using hx'
    · rw [h1] at hx'
      simpa [hl] using hx'
  set I : Ideal B := Ideal.span {(l : B)} with hI
  let mk := Ideal.Quotient.mk I
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker mk = I := Ideal.mk_ker
  have hIp : I ≤ p := by
    rw [hI, Ideal.span_le]; simpa using hlmem
  have hl0 : ∀ a ∈ Ideal.span {((l : ℕ) : ℤ)}, (Int.castRingHom (B ⧸ I)) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have : ((l : ℕ) : B ⧸ I) = 0 := by
      have h0 : (Ideal.Quotient.mk I) (l : B) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span rfl)
      simpa using h0
    simp [this]
  let ψ : ZMod l →+* B ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((l : ℕ) : ℤ)}) (Int.castRingHom (B ⧸ I)) hl0).comp
      (Int.quotientSpanNatEquivZMod l).symm.toRingHom
  letI : Algebra (ZMod l) (B ⧸ I) := ψ.toAlgebra
  haveI : IsScalarTower ℤ (ZMod l) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType (ZMod l) (B ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod l) (B ⧸ I)
  haveI : PerfectField (FractionRing (ZMod l)) := by
    have : Finite (FractionRing (ZMod l)) :=
      Finite.of_equiv _ (FractionRing.algEquiv (ZMod l) (ZMod l)).toEquiv.symm
    infer_instance

  have corr : ∀ (r : Ideal B), r.IsPrime → I ≤ r → (r.map mk).IsPrime ∧ (r.map mk).comap mk = r := by
    intro r hr hIr
    refine ⟨Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hIr), ?_⟩
    rw [Ideal.comap_map_of_surjective' mk hmk, hker]
    exact sup_eq_left.mpr hIr
  obtain ⟨p', hp', rfl⟩ : ∃ p' : Ideal (B ⧸ I), p'.IsPrime ∧ p'.comap mk = p :=
    ⟨p.map mk, corr p hp hIp⟩
  have hdom : ∀ a : ZMod l, algebraMap (ZMod l) (B ⧸ I) a ∈ p' → a = 0 := by
    intro a ha
    by_contra ha0
    exact hp'.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((IsUnit.mk0 a ha0).map _))
  obtain ⟨g', hg'p, hg'⟩ := _root_.GlobalTheory.prime_generically_regular_quotient (ZMod l) (B ⧸ I) p' hdom
  obtain ⟨g, rfl⟩ := hmk g'
  refine ⟨g, fun hg => hg'p hg, ?_⟩
  intro q hq hpq hgq
  have hIq : I ≤ q := hIp.trans hpq
  obtain ⟨q', hq', rfl⟩ : ∃ q' : Ideal (B ⧸ I), q'.IsPrime ∧ q'.comap mk = q :=
    ⟨q.map mk, corr q hq hIq⟩
  have hpq' : p' ≤ q' := by
    intro y hy
    obtain ⟨y, rfl⟩ := hmk y
    exact hpq hy
  have hreg := hg' q' hpq' (fun h => hgq h)
  obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv B (B ⧸ I) mk hmk p' q'
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigIsoOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigLBIso


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_rig_iso_of_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L₁ L₂ : RigLB G), LBIso L₁.L L₂.L → ∃ wL : LB.Iso L₁.L L₂.L, wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  rintro S G _ _ L₁ L₂ ⟨w, hw⟩
  let gv {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
    gm f y _ (w.s (j, k))

  have gm_isGen {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j j' : L.ι)
      (k k' : L'.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
      gv w f y j k = gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gv w f y j' k' := by
    have hV : f y ∈ (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L'.U k) (w.s (j, k)) =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L.U j') (L.g j j') *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
        res (inf_le_right : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j' ⊓ L'.U k') (w.s (j', k')) :=
      hw (j, k) (j', k')
    have key := congrArg (gm f y ((L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    rw [gm_res f y (U := L.U j ⊓ L'.U k) _ hV (w.s (j, k)),
      gm_res f y (U := L.U j' ⊓ L'.U k') _ hV (w.s (j', k'))] at key
    exact key

  let isoPullId {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) : LB.Iso L' (L.pull F) :=
    ⟨fun p => res (fun y hy => ⟨by have := mem_pull.1 hy.1; rw [hF] at this; exact this, hy.2⟩ :
      (LB.pull L F).U p.1 ⊓ L'.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L'.U p.2) (w.s (p.1 PUnit.unit, p.2))⟩

  have gw_isoPullId {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
      (j : L.ι) (k : L'.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L'.U k) :
      gw (isoPullId w hF) f y j k = gv w f y j k := by
    have hmem : f y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 (by rw [hF]; exact hj), hk⟩
    exact gm_res f y _ hmem (w.s (j, k))

  have isoPullId_pgen {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {F : X ⟶ X} (hF : F = 𝟙 X) :
      PGen (isoPullId w hF) := by
    intro Y f y j j' k k' hj hj' hk hk'
    subst hF
    rw [gw_isoPullId w rfl f y j k hj hk, gw_isoPullId w rfl f y j' k' hj' hk', Category.comp_id]
    exact gm_isGen hw f y j j' k k' hj hj' hk hk'

  have hw₀ : PGen (isoPullId w (F := 𝟙 G.left) rfl) := isoPullId_pgen hw rfl
  obtain ⟨c, hc⟩ := GlobalTheory.Unif.RigidifyIso.exists_ratio (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec G) (ε := fun _ => 1) hw₀ L₂.isLB L₁.isLB (𝟙 _)
    (fun _ => by rw [Category.comp_id, Category.id_comp]) L₁.rig L₁.rigGen L₂.rig L₂.rigGen
  let π : G.left ⟶ (𝟙_ (Over S)).left := G.hom
  have hs : eSec G ≫ π = 𝟙 _ := Over.w η[G]
  let wL : LB.Iso L₁.L L₂.L := ⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : L₂.L.ι) (k : L₁.L.ι), f y ∈ L₂.L.U j →
      f y ∈ L₁.L.U k → gv wL f y j k = gm (f ≫ π) y ⊤ c * gv w f y j k := by
    intro Y f y j k hj hk
    have hz : f y ∈ L₂.L.U j ⊓ L₁.L.U k := ⟨hj, hk⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res f y _ hz _).trans (gm_pull f π y ⊤ trivial c)) rfl)
  refine ⟨wL, ?_, ?_⟩
  · rintro p q
    apply unit_ext
    intro x hx
    have h1 : (𝟙 G.left) x ∈ L₂.L.U p.1 := hx.1.1
    have h2 : (𝟙 G.left) x ∈ L₁.L.U p.2 := hx.1.2
    have h3 : (𝟙 G.left) x ∈ L₂.L.U q.1 := hx.2.1
    have h4 : (𝟙 G.left) x ∈ L₁.L.U q.2 := hx.2.2
    have eL : gm (𝟙 G.left) x _ (res (inf_le_left : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s p)) =
        gv wL (𝟙 G.left) x p.1 p.2 := gm_res (𝟙 G.left) x _ hx _
    have eR : gm (𝟙 G.left) x _ ((L₂.L.div L₁.L).g p q *
        res (inf_le_right : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s q)) =
        gm (𝟙 G.left) x _ (L₂.L.g p.1 q.1) * (gm (𝟙 G.left) x _ (L₁.L.g p.2 q.2))⁻¹ * gv wL (𝟙 G.left) x q.1 q.2 :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L₁.L L₂.L (𝟙 G.left) x p q hx) (gm_res (𝟙 G.left) x _ hx _))
    rw [eL, eR, hv _ _ x _ _ h1 h2, hv _ _ x _ _ h3 h4, gm_isGen hw (𝟙 G.left) x p.1 q.1 p.2 q.2 h1 h3 h2 h4]
    exact mul_left_comm _ _ _
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hj : (eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk : (eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hj' : (𝟙 _ ≫ eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk' : (𝟙 _ ≫ eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hc' := hc _ (𝟙 _) x P Q (by simp only [Category.comp_id]; exact hx.1) hx.2
    have ep : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw (isoPullId w (F := 𝟙 G.left) rfl) (K := PUnit) (fun _ => eSec G) (fun _ => 1)
        (𝟙 _) x P Q = gv w (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) := by
      show ∏ k : PUnit, _ = _
      rw [Fintype.prod_unique, zpow_one]
      exact gw_isoPullId w rfl _ x _ _ hj' hk'
    rw [Category.comp_id, ep] at hc'
    have eL : gm (𝟙 _) x _ (res (inf_le_left : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _)
        (L₂.rig.s P)) = gm (𝟙 _) x _ (L₂.rig.s P) := gm_res (𝟙 _) x _ hx _
    have eR : gm (𝟙 _) x _ (@id (Γ((𝟙_ (Over S)).left, LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q)ˣ) ((LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) *
        res (inf_le_right : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _) (L₁.rig.s Q)) =
        gv wL (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) * gm (𝟙 _) x _ (L₁.rig.s Q) := by
      refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 _) x _ hx _))
      show gm (𝟙 _) x _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (wL.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res (𝟙 _) x _ hx _).trans (gm_pull (𝟙 _) (eSec G) x (L₂.L.U (P PUnit.unit) ⊓ L₁.L.U (Q PUnit.unit)) ⟨hj, hk⟩ _)
    refine eL.trans (hc'.trans (Eq.trans ?_ eR.symm))
    rw [hv _ _ x _ _ hj' hk', Category.assoc, hs, Category.comp_id]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.RigLBIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomAddEpsMul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem exists_ringHom_add_eps_mul {R B : Type} [CommRing R] [CommRing B] {n : ℕ} (e : R →+* B)
    (e' : Fin n → (R →+* DualNumber B)) (he : ∀ a f, (e' a f).fst = e f) (δ : R → R)
    (hδa : ∀ f f', δ (f + f') = δ f + δ f') (hδm : ∀ f f', δ (f * f') = f * δ f' + f' * δ f)
    (c : Fin n → B) (ε : B) (hε : ε * ε = 0) :
    ∃ ψ : R →+* B, ∀ f, ψ f = e f + ε * (e (δ f) + ∑ a, c a * (e' a f).snd) := by
  have h1 : δ 1 = 0 := by
    have := hδm 1 1
    simp only [_root_.one_mul, _root_.mul_one] at this
    linear_combination -this
  have h0 : δ 0 = 0 := by
    have := hδa 0 0
    rw [add_zero] at this
    linear_combination -this
  refine ⟨{ toFun := fun f => e f + ε * (e (δ f) + ∑ a, c a * (e' a f).snd),
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun f => rfl⟩
  · simp [h1]
  · intro f f'
    simp only [hδm, map_add (f := _), map_mul, TrivSqZeroExt.snd_mul, he, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    have hs : ∑ x, c x * (e f * TrivSqZeroExt.snd ((e' x) f') + TrivSqZeroExt.snd ((e' x) f) * e f') =
        e f * ∑ a, c a * TrivSqZeroExt.snd ((e' a) f') + e f' * ∑ a, c a * TrivSqZeroExt.snd ((e' a) f) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hs]
    linear_combination (-(e (δ f) + ∑ a, c a * (e' a f).snd) * (e (δ f') + ∑ a, c a * (e' a f').snd)) * hε
  · simp [h0]
  · intro f f'
    simp only [hδa, map_add (f := _), TrivSqZeroExt.snd_add, mul_add, Finset.sum_add_distrib]
    ring

theorem fst_comp_tangent_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (U : X.affineOpens) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left) (hv : IsTanAtG t (LogKS.chart U) v)
    {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A]
    (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) (u : epsR K ⟶ A)
    (hu : u.left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v),
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left := by
  intro E _ _ _ H X t U v hv K _ x0 hU A _ m hm u hu
  have hv2 : spMap (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ v =
      (1 : Over.mk (LogKS.chart U) ⟶ t.G).left := hv.2
  have hux : spMap (ev x0 U.1 hU) ≫ LogKS.chart U = x0 := GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  let κ : Over.mk x0 ⟶ Over.mk (LogKS.chart U) := Over.homMk (spMap (ev x0 U.1 hU)) hux

  have hG1 : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left) ≫ m = (1 : Over.mk x0 ⟶ t.G).left := by
    rw [Category.assoc, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (dualMap (ev x0 U.1 hU)) =
        (ev x0 U.1 hU).comp ((TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom) := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hv2]
    have := congrArg Over.Hom.left (comp_one (M := t.G) κ)
    exact this.symm ▸ rfl
  have hA1 : (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m = (1 : Over.mk x0 ⟶ t.G).left := by
    have hw : ((1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m) ≫ t.G.hom = (Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0)).hom := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ A)]
      rfl
    let z : Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk ((1 : Over.mk (𝟙 (Sp K)) ⟶ A).left ≫ m) hw
    have hz : (z * z).left = z.left := by
      have := hm.2 (Over.mk (𝟙 (Sp K))) 1 1 z z rfl rfl
      rw [this, _root_.mul_one]
      rfl
    have hz1 : z = 1 := by
      have : z * z = z := Over.OverMorphism.ext hz
      simpa using this
    let κ' : Over.mk x0 ⟶ Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x0) := Over.homMk (𝟙 _) (by simp)
    have := congrArg Over.Hom.left (comp_one (M := t.G) κ')
    calc _ = (κ' ≫ z).left := by simp [κ', z]
      _ = _ := by rw [hz1]; exact this
  have hA2 : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left) ≫ A.hom = 𝟙 (Sp K) := by
    rw [Category.assoc, Over.w u]; show spMap _ ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e3 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e3, CommRingCat.ofHom_id, Spec.map_id]
  refine hm.1.hom_ext (hG1.trans hA1.symm) (hA2.trans ?_)
  exact (Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ A)).symm

theorem fst_comp_transl_eq : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (v : epsR K ⟶ A)
    (hv : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ A).left)
    (w : Sp (DualNumber B) ⟶ A.left), IsTransl φ x v w → spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x := by
  intro K _ A _ B _ φ x v hv w ⟨x', v', hx', hv', hw⟩
  have hio : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap ((algebraMap B (DualNumber B)).comp φ) = spMap φ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let io : Over.mk (spMap φ) ⟶ Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) hio
  have hνw : (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left) ≫ A.hom = (Over.mk (𝟙 (Sp K))).hom := by
    rw [Category.assoc, Over.w v]; show spMap _ ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have e3 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e3, CommRingCat.ofHom_id, Spec.map_id]
  let ν : Over.mk (𝟙 (Sp K)) ⟶ A := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left) hνw
  have hν : ν = 1 := Over.OverMorphism.ext hv
  let κ : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap φ) (Category.comp_id _)
  have h1 : io ≫ v' = 1 := by
    have : io ≫ v' = κ ≫ ν := by
      apply Over.OverMorphism.ext
      simp only [io, κ, ν, Over.comp_left, Over.homMk_left, hv']
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, hν, comp_one]
  have h2 : (io ≫ (x' * v')).left = x := by
    rw [comp_mul, h1, _root_.mul_one]
    simp only [io, Over.comp_left, Over.homMk_left, hx']
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp x
  rw [← hw]
  exact h2

theorem top_le_preimage_of_fst : ∀ {B : Type} [CommRing B] {Z : Scheme.{0}} (z : Sp (DualNumber B) ⟶ Z) (V : Z.Opens),
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ z) ⁻¹ᵁ V → ⊤ ≤ z ⁻¹ᵁ V := by
  intro B _ Z z V h p _
  have hp : (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) ((spMap (algebraMap B (DualNumber B))) p) = p := by
    show PrimeSpectrum.comap _ (PrimeSpectrum.comap _ p) = p
    ext y
    show (algebraMap B (DualNumber B)) (TrivSqZeroExt.fst y) ∈ p.asIdeal ↔ y ∈ p.asIdeal
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    have hy : y = TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr y.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq y).symm
    have hn : TrivSqZeroExt.inr y.snd ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    constructor
    · intro h1
      rw [hy]
      exact p.asIdeal.add_mem h1 hn
    · intro h1
      have : TrivSqZeroExt.inl y.fst = y - TrivSqZeroExt.inr y.snd :=
        eq_sub_of_add_eq (TrivSqZeroExt.inl_fst_add_inr_snd_eq y)
      rw [this]
      exact p.asIdeal.sub_mem h1 hn
  have := h (Set.mem_univ ((spMap (algebraMap B (DualNumber B))) p))
  show z p ∈ V
  rw [← hp]
  exact this

theorem comp_hom_of_isTransl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (v : epsR K ⟶ A) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x v w) :
    w ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp φ) := by
  obtain ⟨x', v', -, -, rfl⟩ := hw
  exact Over.w (x' * v')

theorem exists_isChartPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) (W₀ : t.G.left.Opens) (hW₀ : W₀ ≤ t.G.hom ⁻¹ᵁ U.1) (d : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hd : LogKS.IsField W₀ d) (hlift : ∀ r, d W₀ ((t.G.hom.appLE U.1 W₀ hW₀).hom r) = (t.G.hom.appLE U.1 W₀ hW₀).hom (D r)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (hy1 : ∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (m : A.left ⟶ t.G.left) (m' : A'.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hm' : IsGrpPullback A' t.G y1 m') (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (Ω : t.G.left.affineOpens) (hΩ : Ω.1 ≤ W₀) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)), ∃ l, IsChartPt A' m m' Ω.1 (d Ω.1) u θ Wo g x l := by
  intro E _ _ _ H X t U n v D hv W₀ hW₀ d hd hlift K _ x0 hU y1 hU' hy1 A _ A' _ m m' u hm hm' hu Ω hΩ θ Wo g B _ _ x hx hxΩ
  have hwT : ∀ a, IsTransl (baseMap K B) x (u a) (transl (baseMap K B) x (u a)) :=
    fun a => isTransl_transl (baseMap K B) x hx (u a)
  have hred : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ transl (baseMap K B) x (u a) = x := fun a =>
    fst_comp_transl_eq (baseMap K B) x (u a) (fst_comp_tangent_eq_one t U (v a) (hv a) x0 hU A m hm (u a) (hu a)) _ (hwT a)
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_map m le_rfl hxΩ
  have hwm : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω.1 := fun a =>
    top_le_preimage_of_fst _ Ω.1 (by rw [← Category.assoc, hred a]; exact hxm)
  have he : ∀ a f, (ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a) f).fst = ev (x ≫ m) Ω.1 hxm f := by
    intro a f
    have := GlobalTheory.FlagMod.ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a)
      (by rw [← Category.assoc, hred a]; exact hxm)
    have e1 := GlobalTheory.FlagMod.ev_congr (show spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫
      (transl (baseMap K B) x (u a) ≫ m) = x ≫ m by rw [← Category.assoc, hred a]) Ω.1
      (by rw [← Category.assoc, hred a]; exact hxm) hxm
    rw [e1] at this
    rw [this]
    rfl
  have hdΩ := hd.2.1 Ω.1 hΩ
  obtain ⟨ψ, hψ⟩ := exists_ringHom_add_eps_mul (ev (x ≫ m) Ω.1 hxm) (fun a => ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a)) he
    (d Ω.1) (hd.1 Ω.1 hΩ) (hd.2.1 Ω.1 hΩ) (fun a => ∑ b, baseMap K B (θ a b) * dlogAt (baseMap K B) x (u b) Wo g)
    (algebraMap (DualNumber K) B DualNumber.eps) (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero])
  have hψ' : ∀ f, ψ f = chartVal m Ω.1 (d Ω.1) u θ Wo g x f := by
    intro f
    rw [hψ f, chartVal, valR_eq_ev _ _ hxm, valR_eq_ev _ _ hxm]
    simp only [valR_eq_ev _ _ (hwm _)]
  set q : Sp B ⟶ t.G.left := spMap ψ ≫ Ω.2.fromSpec with hq_def
  have hqΩ : ⊤ ≤ q ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le Ω.2 le_rfl)
  have hevq : ev q Ω.1 hqΩ = ψ := GlobalTheory.FlagMod.ev_spMap_tau Ω.2 ψ hqΩ
  have hΩU : Ω.1 ≤ t.G.hom ⁻¹ᵁ U.1 := hΩ.trans hW₀
  have key : ∀ {S : Type} [CommRing S] (ρ : K →+* S) (z : Sp S ⟶ A.left) (hz : z ≫ A.hom = spMap ρ)
      (hzΩ : ⊤ ≤ (z ≫ m) ⁻¹ᵁ Ω.1) (r : Γ(X, U.1)),
      ev (z ≫ m) Ω.1 hzΩ ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r) = ρ (ev x0 U.1 hU r) := by
    intro S _ ρ z hz hzΩ r
    have h1 : (z ≫ m) ≫ t.G.hom = spMap ρ ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, hz]
    rw [GlobalTheory.FlagMod.ev_appLE (z ≫ m) t.G.hom hΩU hzΩ (GlobalTheory.FlagMod.le_preimage_map t.G.hom hΩU hzΩ) r,
      GlobalTheory.FlagMod.ev_congr h1 U.1 _ (GlobalTheory.FlagMod.le_preimage_comp _ hU), GlobalTheory.FlagMod.ev_spMap ρ x0 U.1 hU]
    rfl
  have hres : ∀ r, resG t.G.left hΩ ((t.G.hom.appLE U.1 W₀ hW₀).hom r) = (t.G.hom.appLE U.1 Ω.1 hΩU).hom r := by
    intro r
    rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hdr : ∀ r, d Ω.1 ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r) = (t.G.hom.appLE U.1 Ω.1 hΩU).hom (D r) := by
    intro r
    rw [← hres, hd.2.2 W₀ Ω.1 hΩ le_rfl, hlift, hres]
  have hU1 : ⊤ ≤ (q ≫ t.G.hom) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_map t.G.hom hΩU hqΩ
  have hU2 : ⊤ ≤ (spMap (algebraMap (DualNumber K) B) ≫ y1) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_comp _ hU'
  have hq : q ≫ t.G.hom = spMap (algebraMap (DualNumber K) B) ≫ y1 := by
    rw [← GlobalTheory.FlagMod.spMap_ev (q ≫ t.G.hom) U.2 hU1, ← GlobalTheory.FlagMod.spMap_ev (spMap (algebraMap (DualNumber K) B) ≫ y1) U.2 hU2]
    suffices e : ev (q ≫ t.G.hom) U.1 hU1 = ev (spMap (algebraMap (DualNumber K) B) ≫ y1) U.1 hU2 by rw [e]
    ext r
    rw [← GlobalTheory.FlagMod.ev_appLE q t.G.hom hΩU hqΩ hU1 r, hevq, hψ, GlobalTheory.FlagMod.ev_spMap _ y1 U.1 hU' hU2,
      RingHom.comp_apply, hy1 r, hdr, key (baseMap K B) x hx hxm, key (baseMap K B) x hx hxm]
    have hw0 : ∀ a, (ev (transl (baseMap K B) x (u a) ≫ m) Ω.1 (hwm a) ((t.G.hom.appLE U.1 Ω.1 hΩU).hom r)).snd = 0 := by
      intro a
      rw [key _ _ (comp_hom_of_isTransl _ x (u a) _ (hwT a)) (hwm a) r]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [hw0, mul_zero, Finset.sum_const_zero, add_zero]
    rw [map_add (f := _), DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, baseMap, RingHom.comp_apply,
      RingHom.comp_apply, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨l, hl1, hl2⟩ := hm'.1.exists_lift q (spMap (algebraMap (DualNumber K) B)) hq
  refine ⟨l, hl2, ?_, ?_⟩
  · rw [hl1]; exact hqΩ
  · intro f
    rw [← hψ' f, valR_eq_ev _ _ (by rw [hl1]; exact hqΩ)]
    rw [GlobalTheory.FlagMod.ev_congr hl1 Ω.1 _ hqΩ, hevq]

end GlobalTheory.CechKS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrderStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spanning_posDef_relation_harrisTaylorOrder : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ (r : ℕ) (e : Fin r → D.Oᵐᵒᵖ) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), Submodule.span ℤ (Set.range e) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧ ∑ i, ∑ j, W i j • (e j * MulOpposite.op ((D.star (e i).unop).unop)) = (d : D.Oᵐᵒᵖ) := by
  first | (exact @GlobalTheory.CasimirOrder.exists_posdef_relation) | (exact GlobalTheory.CasimirOrder.exists_posdef_relation) | (intros; apply GlobalTheory.CasimirOrder.exists_posdef_relation  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : S.Gam), ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left := by
  first | exact @GlobalTheory.Poinc.exists_qkPt_of_utest | exact GlobalTheory.Poinc.exists_qkPt_of_utest | (intros; apply GlobalTheory.Poinc.exists_qkPt_of_utest <;> assumption)
end

