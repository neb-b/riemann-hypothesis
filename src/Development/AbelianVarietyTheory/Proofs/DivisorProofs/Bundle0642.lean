module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0611
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCocycleAdditiveLawReductionCoboundary
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option maxHeartbeats 800000

namespace GlobalTheory.LazardHomog

theorem lift_addLaw (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext α
  rw [coeff_lift]
  simp only [addLaw, map_add (f := _), coeff_X]
  have hne : (Finsupp.single (Sum.inl i) 1 : Fin d ⊕ Fin d →₀ ℕ) ≠ Finsupp.single (Sum.inr i) 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]; simp
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · simp [h1, hne]
  · by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · simp [h2, hne.symm]
    · simp [h1, h2]

theorem homogCoc_red_cob : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) k), 2 ≤ N → IsCoc (addLaw k d) c → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ Red p (cob1 (addLaw (Fr p k) d) h) c := by
  intro p _ k _ _ _ d N c hN hc hhom
  have hconst : ∀ (R : Type) [CommRing R] (i : Fin d), constantCoeff (addLaw R d i) = 0 := by
    intro R _ i; simp [addLaw]
  have hc0 : constantCoeff c = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hhom 0 (by simp; omega)
  obtain ⟨b, hb⟩ := GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add k d c hc hc0
  set cm : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k := fun m => at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (Pi.single m (X (Sum.inr m))) with hcm
  set bN := homogeneousComponent N b with hbN
  have hbNc : ∀ α, coeff α bN = if α.degree = N then coeff α b else 0 := fun α =>
    coeff_homogeneousComponent N α b

  have hdec : c = cob1 (addLaw k d) bN + ∑ m, cm m := by
    ext γ
    by_cases hγ : γ.degree = N
    · have e1 : coeff γ (cob1 (addLaw k d) b) = coeff γ (cob1 (addLaw k d) bN) := by
        have := formalCoboundary_add (hconst k) bN (b - bN)
        rw [add_sub_cancel] at this
        rw [this, map_add (f := _), _root_.GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq k d N (b - bN) (fun α hα => by
          rw [map_sub, hbNc, if_pos hα, sub_self]) γ hγ, add_zero]
      conv_lhs => rw [hb]
      rw [map_add (f := _), map_add (f := _), e1]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [hhom γ hγ, map_add (f := _), map_sum, (_root_.GlobalTheory.homog_cob_addLaw k d N).1 bN (fun α hα => by
        rw [hbNc, if_neg hα]) γ hγ, zero_add]
        refine (Finset.sum_eq_zero fun m _ => ?_).symm
        simp only [cm]
        rw [_root_.GlobalTheory.coeff_at2_single_X_inl_inr]
        split_ifs <;> simp [hhom γ hγ]

  set a : Fin d → ℕ → k := fun m n => coeff (Finsupp.single (Sum.inl m) n + Finsupp.single (Sum.inr m) (N - n)) c with ha
  have hsym : ∀ m n, n ≤ N → a m n = a m (N - n) := by
    intro m n hn
    simp only [ha]
    conv_lhs => rw [← hc.2]
    rw [(_root_.GlobalTheory.homog_cob_addLaw k d N).2.2.1, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Nat.sub_sub_self hn, add_comm]
    rfl
  have hrel : ∀ m i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a m (i + j) * ((i + j).choose i : k) = a m i * ((j + l).choose j : k) := by
    intro m i j l hi hj hl hs
    simp only [ha]
    have e1 : N - (i + j) = l := by omega
    have e2 : N - i = j + l := by omega
    rw [e1, e2]
    exact (_root_.GlobalTheory.Katz.CocRel.relations k d c hc.1 m).2 i j l hi hj hl
  have ht := fun m => _root_.GlobalTheory.LazardOne.exists_lift p k N (a m) hN (hsym m) (hrel m)
  choose t ht using ht
  have hzero : ∀ m, coeff (Finsupp.single (Sum.inl m) N) c = 0 :=
    fun m => (_root_.GlobalTheory.Katz.CocRel.relations k d c hc.1 m).1 N (by omega)
  have hzero' : ∀ m, coeff (Finsupp.single (Sum.inr m) N) c = 0 := by
    intro m
    have := hsym m 0 (Nat.zero_le _)
    simp only [ha, Finsupp.single_zero, zero_add, Nat.sub_zero, Nat.sub_self, add_zero] at this
    rw [this, hzero]
  have hconstFr := hconst (Fr p k)
  have redSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
      (G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ m ∈ s, Red p (F m) (G m)) →
      Red p (∑ m ∈ s, F m) (∑ m ∈ s, G m) := by
    intro s F G hFG
    induction s using Finset.induction_on with
    | empty => intro α; exact ⟨0, by simp⟩
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact ((_root_.GlobalTheory.Katz.red_rules p k _).2.2.2.1 _ _ _ _ (hFG x (Finset.mem_insert_self _ _))
        (ih fun m hm => hFG m (Finset.mem_insert_of_mem hm))).1
  have cob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconstFr (0 : Fr p k) 0
    simpa using this
  have cobSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d) (Fr p k)),
      cob1 (addLaw (Fr p k) d) (∑ m ∈ s, F m) = ∑ m ∈ s, cob1 (addLaw (Fr p k) d) (F m) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simpa using cob0
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, formalCoboundary_add hconstFr, ih]
  have redm : ∀ m, Red p (t m • cob1 (addLaw (Fr p k) d) (X m ^ N)) (cm m) := by
    intro m α
    rw [GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose (Fr p k) d N m (by omega)]
    simp only [cm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [_root_.GlobalTheory.coeff_at2_single_X_inl_inr, map_smul, map_sum]
    simp only [coeff_monomial, smul_eq_mul]
    set i := α (Sum.inl m) with hi
    set j := α (Sum.inr m) with hj
    have key : ∀ i', α = Finsupp.single (Sum.inl m) i' + Finsupp.single (Sum.inr m) (N - i') →
        i = i' ∧ j = N - i' := by
      intro i' h
      constructor
      · rw [hi, h]; simp
      · rw [hj, h]; simp
    by_cases hs : α = Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j
    · rw [if_pos hs]
      by_cases hin : 0 < i ∧ i < N ∧ j = N - i
      · obtain ⟨w, hw1, hw2⟩ := ht m i hin.1 hin.2.1
        refine ⟨w, ?_, ?_⟩
        · rw [Finset.sum_eq_single_of_mem i (Finset.mem_Ioo.2 ⟨hin.1, hin.2.1⟩)]
          · rw [if_pos (hs.trans (by rw [hin.2.2])), hw1]
          · intro i' _ hne; rw [if_neg]; intro h; exact hne (key i' h).1.symm
        · rw [hw2]; simp only [ha]; rw [← hin.2.2, ← hs]
      · refine ⟨0, ?_, ?_⟩
        · rw [Finset.sum_eq_zero, mul_zero, map_zero]
          intro i' hi'; rw [if_neg]; intro h
          obtain ⟨e1, e2⟩ := key i' h
          rw [Finset.mem_Ioo] at hi'
          exact hin ⟨e1 ▸ hi'.1, e1 ▸ hi'.2, e1 ▸ e2⟩
        · rw [map_zero]
          by_cases hd : i + j = N
          · have : i = 0 ∨ i = N := by omega
            rcases this with h0 | h0
            · have : α = Finsupp.single (Sum.inr m) N := by
                rw [hs, h0, Finsupp.single_zero, zero_add]; congr 1; omega
              rw [this, hzero']
            · have : α = Finsupp.single (Sum.inl m) N := by
                rw [hs, h0, (by omega : j = 0), Finsupp.single_zero, add_zero]
              rw [this, hzero]
          · refine (hhom α ?_).symm
            rw [hs, map_add (f := _), Finsupp.degree_single, Finsupp.degree_single]; exact hd
    · rw [if_neg hs]
      refine ⟨0, ?_, by simp⟩
      rw [Finset.sum_eq_zero, mul_zero, map_zero]
      intro i' _; rw [if_neg]; intro h
      apply hs; obtain ⟨e1, e2⟩ := key i' h; rw [e1, e2]; exact h
  refine ⟨Katz.lift p bN + ∑ m, t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k)), ?_, ?_⟩
  · intro α hα
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, coeff_lift, hbNc, if_neg hα, WittVector.teichmuller_zero, map_zero,
      zero_add]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [map_smul, coeff_X_pow, if_neg, smul_zero]
    intro h; apply hα; rw [h, Finsupp.degree_single]
  · have h1 : Red p (cob1 (addLaw (Fr p k) d) (Katz.lift p bN)) (cob1 (addLaw k d) bN) := by
      rw [← lift_addLaw p k d]
      exact ((GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (hconst k)).2.1 _ _
        ((_root_.GlobalTheory.Katz.red_rules p k _).2.2.1 bN)).1
    have h2 : Red p (∑ m, cob1 (addLaw (Fr p k) d) (t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k))))
        (∑ m, cm m) := by
      refine redSum _ _ _ fun m _ => ?_
      rw [formalCoboundary_smul hconstFr]; exact redm m
    have := ((_root_.GlobalTheory.Katz.red_rules p k _).2.2.2.1 _ _ _ _ h1 h2).1
    rw [formalCoboundary_add hconstFr, cobSum]
    rwa [← hdec] at this

end GlobalTheory.LazardHomog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.IntAcyc

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def finDiag : Finset B ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin A (t : Set B))
  map {t u} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def finCocone : Cocone (finDiag A B) where
  pt := CommRingCat.of B
  ι := { app := fun t => CommRingCat.ofHom (Algebra.adjoin A (t : Set B)).val.toRingHom
         naturality := fun _ _ _ => by ext; rfl }

def finCoconeIsColimit : IsColimit (finCocone A B) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset B) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (finCocone A B)) ?_ ?_)
  · intro x
    exact ⟨{x}, ⟨x, Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, ?_⟩
    apply Subtype.ext
    exact h

theorem finite_finDiag [Algebra.IsIntegral A B] (t : Finset B) :
    Module.Finite A (Algebra.adjoin A (t : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

end GlobalTheory.EtC.IntAcyc
end

namespace GlobalTheory.EtC.IntAcyc

theorem acycF_of_isIntegral : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      SH A → AcycF R (sp B) F := by
  classical
  intro R _ F hF A B _ _ _ _ hA
  obtain ⟨hHens, hSep⟩ := hA
  intro n hn
  suffices h : ∀ x : H R (sp B) F n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF (Finset B) (finDiag A B) (finCocone A B)
    (finCoconeIsColimit A B) n).1 x
  haveI := finite_finDiag A B j
  obtain ⟨ι, hι, T, hT, hAl, e, hH, hS⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A (Algebra.adjoin A (j : Set B))
  have hac : AcycF R (sp ((finDiag A B).obj j)) F :=
    _root_.GlobalTheory.EtC.acycF_of_pi_sh R F ι T ((finDiag A B).obj j) ⟨e.toRingEquiv⟩ (fun i => ⟨hH i, (hS i).1⟩)
  haveI := hac n hn
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [← hy, hy0]
  exact map_zero _

end GlobalTheory.EtC.IntAcyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegul
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.isChar_J_of_reg : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ _root_.GlobalTheory.Shin.Reg (Nat.card F) p.1 p.2) → ∀ n, n = _root_.GlobalTheory.Shin.deg L → _root_.GlobalTheory.BI.IsChar ℂ ℂ (_root_.GlobalTheory.Shin.J θ L n) := by
  intro F _ _ θ hθ L
  induction L with
  | nil =>
    intro _ n _
    rw [_root_.GlobalTheory.Shin.J_nil]
    exact _root_.GlobalTheory.BI.isChar_one ℂ ℂ _
  | cons p L ih =>
    intro hL n hn
    rw [_root_.GlobalTheory.Shin.J_cons]
    have hp := hL p List.mem_cons_self
    refine _root_.GlobalTheory.Shin.HCChar.hc_isChar F _ _ n ?_ _ _
      (_root_.GlobalTheory.Shin.isChar_cusp_and_norm_of_reg F θ hθ p.1 p.2 hp.1 hp.2).1
      (ih (fun q hq => hL q (List.mem_cons_of_mem p hq)) _ rfl)
    rw [hn]
    simp [_root_.GlobalTheory.Shin.deg]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsOpenOfStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem isClosed_of_isOpen_of_stable {S : Scheme.{0}} [IsLocallyNoetherian S] {L : Set S} (ho : IsOpen L)
    (hs : ∀ t ∈ L, ∀ s, s ∈ closure ({t} : Set S) → s ∈ L) : IsClosed L := by
  rw [← closure_subset_iff_isClosed]
  intro s hsc
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hUa : IsAffineOpen U := hU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set S) := noetherianSpace_of_isAffineOpen U hUa
  haveI : QuasiSober (U : Set S) := U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  let s' : (U : Set S) := ⟨s, hsU⟩
  let L' : Set (U : Set S) := Subtype.val ⁻¹' L
  have hL'o : IsOpen L' := ho.preimage continuous_subtype_val
  have hs' : s' ∈ closure L' := by
    rw [mem_closure_iff]
    intro O hO hsO
    obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hO
    obtain ⟨x, ⟨hxO, hxU⟩, hxL⟩ := mem_closure_iff.mp hsc (O₀ ∩ U) (hO₀.inter U.isOpen) ⟨hsO, hsU⟩
    exact ⟨⟨x, hxU⟩, hxO, hxL⟩
  let D : Set (U : Set S) := ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set S) | (Z ∩ L').Nonempty}, Z
  have hD : IsClosed D :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  have hLD : L' ⊆ D := fun y hy =>
    Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, y, mem_irreducibleComponent, hy⟩
      mem_irreducibleComponent
  obtain ⟨Z, ⟨hZ, hZL⟩, hsZ⟩ := Set.mem_iUnion₂.mp ((closure_minimal hLD hD) hs')
  have hZi : IsIrreducible Z := hZ.1
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hg : IsGenericPoint hZi.genericPoint Z := by
    have := hZi.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  have hgL : hZi.genericPoint ∈ L' := (hg.mem_open_set_iff hL'o).mpr hZL
  have hsp : hZi.genericPoint ⤳ s' := by
    rw [specializes_iff_mem_closure, hg.def]; exact hsZ
  exact hs _ hgL s (specializes_iff_mem_closure.mp (hsp.map continuous_subtype_val))

theorem eqLocus_isClosedImmersion : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A B _ _ u v hA hB hu hv
  haveI := hA.comm
  haveI := hB.comm
  let P : S → Prop := fun t => ∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t
  have hloc : ∀ t, P t → ∃ V : S.Opens, t ∈ V ∧ (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left :=
    fun t ht => eq_near_fibre_of_quot_contracts S A B u v hA hB hu hv t ht
  have hagree : ∀ V : S.Opens, (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left → ∀ t ∈ V, P t := by
    intro V hV t htV x hx
    have hxV : x ∈ A.hom ⁻¹ᵁ V := by show A.hom x ∈ V; rw [hx]; exact htV
    obtain ⟨y, rfl⟩ : x ∈ Set.range (A.hom ⁻¹ᵁ V).ι := by rw [Scheme.Opens.range_ι]; exact hxV
    let Q : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A := Over.homMk (A.hom ⁻¹ᵁ V).ι rfl
    have hQ : Q ≫ u = Q ≫ v := by ext1; simpa [Q] using hV
    have h1 : Q ≫ (u * v⁻¹) = 1 := by rw [comp_mul, GrpObj.comp_inv, hQ, mul_inv_cancel]
    have h2 : (A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left := by
      have := congrArg CommaMorphism.left h1
      simpa [Q, Hom.one_def] using this
    have e1 : ((A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left) y = (((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left) y := by
      rw [h2]
    simp only [Scheme.Hom.comp_apply] at e1
    rw [e1, hx]
  let L : Set S := {t | P t}
  have hLo : IsOpen L := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t ht
    exact ⟨V, fun t' ht' => hagree V hV t' ht', V.isOpen, htV⟩
  have hLc : IsClosed L := isClosed_of_isOpen_of_stable hLo fun t ht s hs =>
    hom_diff_unit_specialises S A B u v hA hB hu hv t s hs ht
  let W : S.Opens := ⟨L, hLo⟩
  have hWi : IsClosedImmersion W.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hLc)
  refine ⟨W, W.ι, hWi, ?_⟩
  intro T t A' _ φ' hp
  constructor
  · intro he
    have hr : Set.range t ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      exact eq_unit_of_pullback_eq S A B u v hA hB hu hv T t A' φ' hp he τ
    exact ⟨IsOpenImmersion.lift W.ι t hr, IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨z, hz⟩
    have hmem : ∀ y : A'.left, P (t (A'.hom y)) := by
      intro y
      have : t (A'.hom y) ∈ Set.range W.ι := ⟨z (A'.hom y), by rw [← hz, Scheme.Hom.comp_apply]⟩
      rw [Scheme.Opens.range_ι] at this
      exact this
    choose V hVt hV using fun y => hloc _ (hmem y)
    have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
    let U : A'.left → A'.left.Opens := fun y => φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)
    have hyU : ∀ y, y ∈ U y := by
      intro y
      show A.hom (φ' y) ∈ V y
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
      exact hVt y
    have hU : TopologicalSpace.IsOpenCover U :=
      eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
    refine Scheme.Cover.hom_ext (Scheme.openCoverOfIsOpenCover _ U hU) _ _ fun y => ?_
    show (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ u.left = (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ v.left
    rw [← morphismRestrict_ι_assoc, ← morphismRestrict_ι_assoc, hV y]

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfMemSmallCover
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
private theorem isNilpotent_of_mem_of_isNilDP {B : Type} [CommRing B]
    {J : Ideal B} (δ : DividedPowers J) (hδ : _root_.GlobalTheory.Cris.IsNilDP δ) {x : B} (hx : x ∈ J) :
    IsNilpotent x := by
  obtain ⟨N, hN⟩ := hδ
  refine ⟨N, ?_⟩
  have h := hN [(N, x)] (by simpa using hx) (by simp)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [← δ.factorial_mul_dpow_eq_pow hx, h, mul_zero]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
theorem _root_.GlobalTheory.Cris.exists_finite_small_cover (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤)
    (T : _root_.GlobalTheory.Cris.Thick κ s) : ∃ (n : ℕ) (b : Fin n → T.B),
      Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : _root_.GlobalTheory.Cris.Thick κ s) (u : T ⟶ S),
        IsUnit (u.φ (b i)) → _root_.GlobalTheory.Cris.IsSmall κ s U S := by
  classical
  let G : Set T.B₀ := {f | ∃ k, ∀ p : PrimeSpectrum T.B₀,
    f ∉ p.asIdeal → T.x.base p ∈ U k}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    let p : PrimeSpectrum T.B₀ := ⟨m, hm.isPrime⟩
    have hp : T.x.base p ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (fun q : PrimeSpectrum T.B₀ ↦ T.x.base q) ⁻¹' (U k))
        hk ((U k).isOpen.preimage T.x.continuous)
    exact hpf (hle (Ideal.subset_span ⟨k, fun q hq ↦ hsub hq⟩))
  obtain ⟨t, htG, htspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  let e := t.equivFin
  have hlift : ∀ i : Fin t.card, ∃ y, T.π y = (e.symm i : T.B₀) :=
    fun i ↦ T.surj _
  choose b hb using hlift
  refine ⟨t.card, b, ?_, ?_⟩
  · have hmap : Ideal.map T.π (Ideal.span (Set.range b)) = ⊤ := by
      rw [Ideal.map_span, ← htspan]
      congr 1
      ext f
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [hb]
        exact (e.symm i).2
      · intro hf
        exact ⟨b (e ⟨f, hf⟩), ⟨_, rfl⟩, by rw [hb, Equiv.symm_apply_apply]⟩
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective _ T.surj).1
      (hmap ▸ Submodule.mem_top : (1 : T.B₀) ∈ _)
    have hJ : 1 - y ∈ T.J := by
      rw [← T.ker, map_sub, map_one, hy1, sub_self]
    have hunit : IsUnit y := by
      have := (isNilpotent_of_mem_of_isNilDP _ T.nil hJ).isUnit_one_sub
      simpa using this
    exact Ideal.eq_top_of_isUnit_mem _ hy hunit
  · intro i S u hu
    obtain ⟨k, hk⟩ := htG (e.symm i).2
    refine ⟨k, fun q _ ↦ ?_⟩
    show S.x.base q ∈ U k
    rw [← u.pt, Scheme.Hom.comp_apply]
    apply hk
    intro hq
    have h1 : u.φ₀ (e.symm i : T.B₀) ∈ q.asIdeal := hq
    rw [← hb, u.comm] at h1
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map S.π))

end GlobalTheory.Cris
end

