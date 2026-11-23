module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FunObj.SqNum GlobalTheory.SignedHC

section Arith

variable {D : D7}

theorem rankV_lt_gap {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) : rankV D (i + 1) (j + 1) < gap D 1 := by
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : rankV D (i + 1) (j + 1) ≤ bigN D := by
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hk := D.R.m_add_three_le_k
    unfold rankV bigN
    rw [mul_add, mul_add, mul_one]
    omega
  have h4 := (isLeast_gap D 1).1.2.1
  have h5 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem numE_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) :
    0 ≤ (num D 1 τ).e (j + 1) ∧ ((num D 1 τ).e (j + 1) : ℝ) ≤ 4 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hbe, -⟩ := hs
  have e1 : (D.hc τ).e ⟨j, hj⟩ = ((num D 1 τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 ⟨j, hj⟩
  obtain ⟨hb0, he4⟩ := hbe τ ⟨j, hj⟩
  have hg := (D.hc τ).gap_be ⟨j, hj⟩
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rw [e1] at hg he4
  refine ⟨?_, by exact_mod_cast he4⟩
  have : (0 : ℚ) ≤ ((num D 1 τ).e (j + 1) : ℚ) := by linarith
  exact_mod_cast this

theorem cen_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) : 0 ≤ cen D 1 τ i ∧ (cen D 1 τ i : ℝ) ≤ L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  set G0 := GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have ev : (D.hc τ).v ⟨0, by omega⟩ = (G0.v 2 : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, by omega⟩
  obtain ⟨v0, v1⟩ := L.cloud_v τ ⟨0, by omega⟩
  rw [ev] at v0 v1
  have hmid : G0.mid i = (G0.v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) + (gap D 1 : ℚ) / 2 :=
    G0.mid_eq h1
  have hc : cen D 1 τ i = ⌊G0.mid i⌋ := rfl
  have hS := L.Sc_pos
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have hi2 : (i : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have hγ : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : ((G0.mid i : ℚ) : ℝ) = (G0.v 2 : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 := by
    rw [hmid]; push_cast; ring
  have v0' : (0 : ℝ) ≤ (G0.v 2 : ℝ) := by exact_mod_cast v0
  have v1' : (G0.v 2 : ℝ) ≤ L.Sc := by exact_mod_cast v1
  have m0 : (0 : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by
    rw [hmR]; have : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ
    linarith
  have m1 : ((G0.mid i : ℚ) : ℝ) ≤ L.sc.b := by
    rw [hmR]
    have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    linarith
  have m0q : (0 : ℚ) ≤ G0.mid i := by exact_mod_cast m0
  refine ⟨hc ▸ Int.floor_nonneg.2 m0q, ?_⟩
  have hf : ((⌊G0.mid i⌋ : ℚ) : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by exact_mod_cast Int.floor_le (G0.mid i)
  rw [hc]
  push_cast at hf ⊢
  linarith

theorem gap_le_b {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) : (gap D 1 : ℝ) ≤ L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨-, -, -, hm, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hS := L.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have h15 : 15 ≤ gap D 1 := by have : 6 ≤ sLen D := by unfold sLen; omega
                                omega
  have hγ : (15 : ℝ) ≤ gap D 1 := by exact_mod_cast h15
  have hm' : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  constructor <;> nlinarith

theorem maxWt_le {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) :
    1 ≤ (maxWt D 1 : ℝ) ∧ (maxWt D 1 : ℝ) ≤ 10 * L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨hγb, hb⟩ := gap_le_b hs
  have key : ∀ x : Fin D.R.m × Fin D.R.m × D.what₂.Tau,
      max (wtA D 1 x.1 x.2.1 x.2.2).natAbs (wtA' D 1 x.1 x.2.1 x.2.2).natAbs ≤ ⌊10 * L.sc.b⌋₊ := by
    rintro ⟨i, j, τ⟩
    have hr := rankV_lt_gap (D := D) i.2 j.2
    have hij : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have hbs : botSmall D i j ≤ rankV D (i + 1) (j + 1) := by unfold botSmall; omega
    have hbb : botBig D i j ≤ rankV D (i + 1) (j + 1) := by unfold botBig; omega
    have hp : rankV D i j % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    obtain ⟨e0, e1⟩ := numE_bounds hs τ j.2
    obtain ⟨c0, c1⟩ := cen_bounds hs τ (i := D.R.m - i) (by omega) (by omega)
    dsimp only
    refine max_le (Nat.le_floor ?_) (Nat.le_floor ?_)
    · have hA : |wtA D 1 i j τ| ≤ 2 * (num D 1 τ).e (j + 1) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA
        constructor <;> omega
      have hA' : |((wtA D 1 i j τ : ℤ) : ℝ)| ≤ 2 * ((num D 1 τ).e (j + 1) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
    · have hA : |wtA' D 1 i j τ| ≤ 2 * cen D 1 τ (D.R.m - i) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA'
        constructor <;> omega
      have hA' : |((wtA' D 1 i j τ : ℤ) : ℝ)| ≤ 2 * (cen D 1 τ (D.R.m - i) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
  have hsup : maxWt D 1 ≤ max 1 ⌊10 * L.sc.b⌋₊ := max_le_max le_rfl (Finset.sup_le fun x _ => key x)
  have hfl : (⌊10 * L.sc.b⌋₊ : ℝ) ≤ 10 * L.sc.b := Nat.floor_le (by linarith)
  refine ⟨by exact_mod_cast le_max_left 1 _, ?_, hb⟩
  have : (maxWt D 1 : ℝ) ≤ ((max 1 ⌊10 * L.sc.b⌋₊ : ℕ) : ℝ) := by exact_mod_cast hsup
  rw [Nat.cast_max, Nat.cast_one] at this
  exact this.trans (max_le (by linarith) hfl)

end Arith

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AlgConn

namespace GlobalTheory.ZariskiConn

theorem preconnectedSpace_of_isLocalRing (Y : Scheme.{0}) [IsLocalRing Γ(Y, ⊤)] : PreconnectedSpace Y := by
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen Y U hU
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ε with h | h
  · right
    rw [← hεU, Y.basicOpen_of_isUnit h]
    rfl
  · left
    have h0 : ε = 0 := by
      have h1 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, he, sub_self]
      exact (h.mul_right_eq_zero).1 h1
    rw [← hεU, h0, Scheme.basicOpen_zero]
    rfl

theorem range_thick (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (thick O (maximalIdeal O) n) = {closedPoint O} := by
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have key : ∀ Q : PrimeSpectrum (O ⧸ maximalIdeal O ^ (n + 1)),
      thick O (maximalIdeal O) n Q = closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap (Ideal.Quotient.mk _) = maximalIdeal O
    have hp : (Q.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal O ^ (n + 1)))).IsPrime := inferInstance
    refine le_antisymm (le_maximalIdeal hp.ne_top) (hp.le_of_pow_le (n := n + 1) fun a ha => ?_)
    change Ideal.Quotient.mk _ a ∈ Q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.asIdeal.zero_mem
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ maximalIdeal O ^ (n + 1))
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem isPreconnected_closedFibre (O : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hI : IsAdicComplete (maximalIdeal O) O) (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [hP : IsProper f]
    [PreconnectedSpace Y] : _root_.IsPreconnected (f ⁻¹' {closedPoint O}) := by
  let ι : ∀ n, pullback f (thick O (maximalIdeal O) n) ⟶ Y := fun n => pullback.fst _ _
  have hTn : ∀ n, Set.range (ι n) = f ⁻¹' {closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (thick O (maximalIdeal O) n)
    rw [range_thick] at h
    exact h
  refine isPreconnected_closed_iff.2 fun A B hA hB hcov ⟨u, hu, huA⟩ ⟨u', hu', hu'B⟩ => ?_
  by_contra hcon
  have hdis : ∀ y, y ∈ f ⁻¹' {closedPoint O} → y ∈ A → y ∈ B → False :=
    fun y h1 h2 h3 => hcon ⟨y, h1, h2, h3⟩
  have hAB : ∀ n, (ι n ⁻¹' A)ᶜ = ι n ⁻¹' B := by
    intro n
    ext x
    have hx : ι n x ∈ f ⁻¹' {closedPoint O} := by rw [← hTn n]; exact ⟨x, rfl⟩
    exact ⟨fun h => (hcov hx).resolve_left h, fun h h' => hdis _ hx h' h⟩
  have hclo : ∀ n, IsClopen (ι n ⁻¹' A) := fun n =>
    ⟨hA.preimage (ι n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (ι n).continuous⟩
  choose h hhp hhU using fun n => GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen O _
    (ι n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have htr : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ ι (n + 1) = ι n := fun n =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hc : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen O _ _ _ ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ≫ ·) (hhp (n + 1))).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ f) (htr n)).trans (hhp n).symm
    · refine TopologicalSpace.Opens.ext ?_
      refine Eq.trans ?_ (hhU n).symm
      refine Eq.trans (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ⁻¹' ·) (hhU (n + 1))) ?_
      rw [← htr n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick
    GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : ι 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      ι 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  rw [← hTn 0] at hu hu'
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨x', rfl⟩ := hu'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ ι 0 ⁻¹' A := huA
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ ι 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    exact hdis _ (by rw [← hTn 0]; exact ⟨x', rfl⟩) hxA hu'B

theorem exists_complete_flat (X : Scheme.{0}) [IsAffine X] [IsLocallyNoetherian X] (x : X) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsNoetherianRing O) (_ : IsLocalRing O),
      IsAdicComplete (maximalIdeal O) O ∧ ∃ g : Spec (.of O) ⟶ X, Flat g ∧ g (closedPoint O) = x := by
  let B : Type := X.presheaf.stalk x
  let O : Type := AdicCompletion (maximalIdeal B) B
  haveI : IsNoetherianRing O := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B _
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of O := CommRingCat.ofHom (algebraMap B O)
  haveI : IsLocalHom φ.hom := inferInstanceAs (IsLocalHom (algebraMap B O))
  haveI : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _)
  haveI : Flat (X.fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X x
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map φ ≫ X.fromSpecStalk x, inferInstance, ?_⟩
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans Scheme.fromSpecStalk_closedPoint

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X]
    [IsLocallyNoetherian X], Function.Bijective f.appTop →
    ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  intro X Y f _ _ _ hf x
  obtain ⟨O, _, _, _, hO, g, hg, hx⟩ := exists_complete_flat X x
  haveI : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hf
  have H := IsPullback.of_hasPullback f g
  haveI : IsIso (pullback.snd f g).appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  haveI : IsLocalRing Γ(pullback f g, ⊤) :=
    ((Scheme.ΓSpecIso (.of O)).symm ≪≫ asIso (pullback.snd f g).appTop).commRingCatIsoToRingEquiv.isLocalRing
  haveI := preconnectedSpace_of_isLocalRing (pullback f g)
  have hc := isPreconnected_closedFibre O hO _ (pullback.snd f g)
  have hw : ∀ y, f (pullback.fst f g y) = g (pullback.snd f g y) := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hR : pullback.fst f g '' (pullback.snd f g ⁻¹' {closedPoint O}) = f.base ⁻¹' {x} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : pullback.snd f g y = closedPoint O := hy
      change f (pullback.fst f g y) = x
      rw [hw, hy', hx]
    · intro hz
      have h1 : f z = g (closedPoint O) := (show f z = x from hz).trans hx.symm
      obtain ⟨y, hy1, hy2⟩ := Scheme.Pullback.exists_preimage_pullback z _ h1
      exact ⟨y, hy2, hy1⟩
  rw [← hR]
  exact hc.image _ (pullback.fst f g).continuous.continuousOn

end GlobalTheory.ZariskiConn
end
end

