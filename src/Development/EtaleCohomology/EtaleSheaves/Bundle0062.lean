module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0056
public import Development.EtaleCohomology.EtaleSheaves.Bundle0058
public import Development.EtaleCohomology.EtaleSheaves.LeafConsPfB
public import Development.EtaleCohomology.EtaleSheaves.Bundle0055

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleStandingHypothesesImplyRestrictionAxiom
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafInj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

theorem fgtInj0 (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨β, hβ⟩ : ∃ β : Cochain ((chains R).obj E) (res R F) (-1), δ (-1) 0 β = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0) := by
    have := hy
    change CohomologyClass.mk _ = 0 at this
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)] at this
    obtain ⟨β, hβ⟩ := this
    exact ⟨β, by rw [hβ]; rfl⟩
  have hdec : z.1 = mappingCone.descCochain ((chains R).map f) ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega))
      ((Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0)) (show (-1 : ℤ) + 1 = 0 by omega) := by
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    simp [mappingCone.inl_descCochain]
  have hz : δ 0 1 z.1 = 0 := Cocycle.δ_eq_zero z 1
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ (by omega)] at hz
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (by omega)] at hz
  obtain ⟨hz1, -⟩ := hz
  simp only [Cochain.comp_zero, Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at hz1
  have hw : δ (-1) 0 ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1))) = 0 := by
    rw [δ_sub, δ_ofHom_comp, hβ, sub_eq_zero]
    rw [show Int.negOnePow 1 = -1 by decide] at hz1
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] at hz1
    exact hz1
  obtain ⟨γ, hγ⟩ : ∃ γ : Cochain ((chains R).obj U) (res R F) (-2), δ (-2) (-1) γ = (mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1)) := by
    have h0 : CohomologyClass.mk (Cocycle.mk _ 0 (by omega) hw) = 0 := Subsingleton.elim _ _
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-2) (by omega)] at h0
    obtain ⟨γ, hγ⟩ := h0
    exact ⟨γ, by rw [hγ]; rfl⟩
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)]
  refine ⟨mappingCone.descCochain ((chains R).map f) γ β (show (-2 : ℤ) + 1 = -1 by omega), ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ (by omega), hγ, hβ, show Int.negOnePow 0 = 1 by decide, one_smul, sub_add_cancel]
  conv_rhs => rw [hdec]
  rfl

theorem fgtPull (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk _ = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl ((chains R).map f)).comp y.1 (by omega), ?_⟩
  rw [δ_units_smul]
  rw [δ_comp (mappingCone.inl ((chains R).map f)) y.1 (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp [zcomp, mappingCone.δ_inl, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem fgtNat (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n) :
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  have key : mappingCone.inr ((chains R).map f') ≫ mappingCone.map ((chains R).map f') ((chains R).map f) ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) = (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [mappingCone.map]
  simp [zcomp, rmap]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, key]

theorem leafRelNat : LeafRelNat := fgtNat

def LeafSecTw : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (s : Sec (tw q i) U.left),
  Sec.res (prB ι U) s = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

def LeafSec0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (h : Ht q (sch.obj U.left) 0 i),
  pull (ZMod q) (sch.map (prB ι U)) (tw q i) 0 h = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ pull (ZMod q) (sch.map a.left) (tw q i) 0 h = 0

theorem etale_standing_hypotheses_imply_restriction_axiom (hH : Hyps) : A9 := by
  unfold Hyps at hH
  exact hH.2.2.2.2.2.2.2.1

theorem LeafSec0W_of (hT : LeafSecTw) : LeafSec0W := by
  intro hH q _ k _ hq i B W s ι _ U h h0 x hx
  obtain ⟨e, hnat, -⟩ := ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).2
  obtain ⟨t, rfl⟩ := (e U.left).surjective h
  rw [hnat] at h0
  have h1 : Sec.res (prB ι U) t = 0 := (e _).injective (by rw [h0, map_zero])
  obtain ⟨U', a, y, hy, h2⟩ := hT q k hq i s ι U t h1 x hx
  exact ⟨U', a, y, hy, by rw [hnat, h2, map_zero]⟩

theorem LeafInj0W_of (hT : LeafSecTw) : LeafInj0W := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 hp1 hp2 hp3 hS U c x hx
  obtain ⟨U', a, y, hy, hz⟩ := LeafSec0W_of hT hH q k hq i s ι U _ (fgtPull (ZMod q) (tw q i) (sch.map (prB ι U)) 0 c) x hx
  refine ⟨U', a, y, hy, Cov.all ?_⟩
  intro U'' b
  apply fgtInj0 (ZMod q) (tw q i) (sch.map (prB ι U''))
  · exact ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).1 _ (-1) (by norm_num)
  · rw [fgtNat]
    have e : (b ≫ a).left = b.left ≫ a.left := rfl
    rw [e, Functor.map_comp, pull_comp, hz, map_zero]

end LateralTheory.E.LeafInj0WPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FlatMonoLimPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.FlatMonoLimPf

theorem exists_lift {X Y T : Scheme.{0}} (m : X ⟶ Y) [Mono m] [Flat m] [QuasiCompact m] (t : T ⟶ Y)
    (h : Set.range t ⊆ Set.range m) : ∃ b : T ⟶ X, b ≫ m = t := by
  have hs : Surjective (pullback.fst t m) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun x => h ⟨x, rfl⟩
  have : IsIso (pullback.fst t m) := Flat.isIso_of_surjective_of_mono _
  refine ⟨inv (pullback.fst t m) ≫ pullback.snd t m, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

theorem FlatMonoLim_of : LateralTheory.E.NbIsoPf.FlatMonoLim := by
  intro Y J _ _ D ι hι hc X m hm hf hq hr c hl
  have ho : ∀ j, IsOpenImmersion (ι j) := fun j => (hι j).1
  have hsub : ∀ j, Set.range m ⊆ Set.range (ι j) := fun j => hr ▸ Set.iInter_subset _ j
  have hind : ∀ j k, c.π.app j ≫ ι j = c.π.app k ≫ ι k := by
    intro j k
    rw [← c.w (IsCofiltered.minToLeft j k), ← c.w (IsCofiltered.minToRight j k), Category.assoc, Category.assoc,
      hc, hc]
  obtain ⟨j0⟩ : Nonempty J := IsCofiltered.nonempty
  have hp : Set.range (c.π.app j0 ≫ ι j0) ⊆ Set.range m := by
    rw [hr]
    refine Set.subset_iInter fun j => ?_
    rw [hind j0 j]
    rintro _ ⟨x, rfl⟩
    exact ⟨c.π.app j x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨b, hb⟩ := exists_lift m _ hp
  let s : Cone D :=
    { pt := X
      π :=
        { app := fun j => IsOpenImmersion.lift (ι j) m (hsub j)
          naturality := fun j k f => by
            rw [← cancel_mono (ι k)]
            simp [hc] } }
  have hs : ∀ j, hl.lift s ≫ c.π.app j ≫ ι j = m := by
    intro j
    rw [hl.fac_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨b, hl.lift s, ?_, ?_⟩⟩
  · refine hl.hom_ext fun j => ?_
    rw [← cancel_mono (ι j)]
    simp only [Category.assoc]
    erw [hs j, hb, Category.id_comp]
    exact hind j0 j
  · rw [← cancel_mono m, Category.assoc, hb, hs, Category.id_comp]

end LateralTheory.E.FlatMonoLimPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.H1FiniteCoefficients
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.NoetherianChartOverlapFiniteComplement

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem exists_pow_mul_mem (S : Subalgebra A K) (u : K) (hu : u ≠ 0) (hv : u⁻¹ ∈ S) {x : K}
    (hx : x ∈ Algebra.adjoin A ((S : Set K) ∪ {u})) : ∃ n : ℕ, u⁻¹ ^ n * x ∈ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hu]; exact S.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using S.algebraMap_mem r⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x + y) = u⁻¹ ^ m * (u⁻¹ ^ n * x) + u⁻¹ ^ n * (u⁻¹ ^ m * y) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem (S.pow_mem hv _) hn) (S.mul_mem (S.pow_mem hv _) hm)
  | mul x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x * y) = (u⁻¹ ^ n * x) * (u⁻¹ ^ m * y) := by ring
    rw [this]; exact S.mul_mem hn hm

theorem pow_inv_mul_pow (t : K) (ht : t ≠ 0) (n j : ℕ) :
    (n ≤ j ∧ t⁻¹ ^ n * t ^ j = t ^ (j - n)) ∨ (j < n ∧ t⁻¹ ^ n * t ^ j = t⁻¹ ^ (n - j)) := by
  rcases le_or_gt n j with h | h
  · left
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht, one_pow, one_mul]
  · right
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, mul_comm (t⁻¹ ^ j), mul_assoc, ← mul_pow, inv_mul_cancel₀ ht,
      one_pow, mul_one]

theorem noetherian_local_chart_overlap_finite_complement : LateralTheory.E.LZIdemSumNoetherian.NoetherianLocalChartOverlapFiniteComplement := by
  intro A _ _ _ K _ _ B C t hc hB _
  obtain ⟨S, hS⟩ := hB
  set R := Algebra.adjoin A ({t} : Set K)
  have hfg : (Algebra.adjoin R (S : Set K)).toSubmodule.FG :=
    fg_adjoin_of_finite S.finite_toSet (fun x hx => hc.intB x (hS ▸ Algebra.subset_adjoin hx))
  obtain ⟨G, hG⟩ := hfg
  have hRB : ∀ r : R, (r : K) ∈ B := by
    intro r
    have : R ≤ B := Algebra.adjoin_le (by simpa using hc.tB)
    exact this r.2
  have hAB : ∀ y ∈ Algebra.adjoin R (S : Set K), y ∈ B := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hS ▸ Algebra.subset_adjoin hx
    | algebraMap r => exact hRB r
    | add x y _ _ hx hy => exact B.add_mem hx hy
    | mul x y _ _ hx hy => exact B.mul_mem hx hy
  have hGB : ∀ g ∈ G, g ∈ B := by
    intro g hg
    have : g ∈ (Algebra.adjoin R (S : Set K)).toSubmodule := hG ▸ Submodule.subset_span hg
    exact hAB g this
  have hBR : ∀ x ∈ B, x ∈ Submodule.span R (G : Set K) := by
    intro x hx
    rw [hG]
    rw [← hS] at hx
    show x ∈ Algebra.adjoin R (S : Set K)
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap a => exact ((Algebra.adjoin R (S : Set K)).restrictScalars A).algebraMap_mem a
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  have hLex : ∀ g ∈ G, ∃ n : ℕ, t⁻¹ ^ n * g ∈ C := by
    intro g hg
    have : g ∈ Algebra.adjoin A ((C : Set K) ∪ {t}) := by
      rw [← hc.glue]; exact Algebra.subset_adjoin (Or.inl (hGB g hg))
    exact exists_pow_mul_mem C t hc.ne hc.tC this
  classical
  let Lf : K → ℕ := fun g => if h : ∃ n : ℕ, t⁻¹ ^ n * g ∈ C then Classical.choose h else 0
  let L := G.sup Lf
  have hL : ∀ g ∈ G, t⁻¹ ^ L * g ∈ C := by
    intro g hg
    have h := hLex g hg
    have hle : Lf g ≤ L := Finset.le_sup hg
    have hspec : t⁻¹ ^ Lf g * g ∈ C := by
      simp only [Lf, dif_pos h]; exact Classical.choose_spec h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm (t⁻¹ ^ Lf g), mul_assoc]
    exact C.mul_mem (C.pow_mem hc.tC _) hspec
  let N : Submodule A K := Submodule.span A ↑((G ×ˢ Finset.range L).image (fun p => t⁻¹ ^ p.2 * p.1))
  refine ⟨N, ⟨_, rfl⟩, ?_⟩
  set T := Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N with hT
  have hCT : ∀ x ∈ C, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have hBT : ∀ x ∈ B, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have core : ∀ g ∈ G, ∀ m : ℕ, t⁻¹ ^ m * g ∈ T := by
    intro g hg m
    rcases lt_or_ge m L with h | h
    · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(g, m), Finset.mem_product.mpr ⟨hg, Finset.mem_range.mpr h⟩, rfl⟩)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      rw [hk, pow_add, mul_comm (t⁻¹ ^ L), mul_assoc]
      exact hCT _ (C.mul_mem (C.pow_mem hc.tC _) (hL g hg))
  have core2 : ∀ g ∈ G, ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * g ∈ T := by
    intro g hg n j
    rcases pow_inv_mul_pow t hc.ne n j with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact hBT _ (B.mul_mem (B.pow_mem hc.tB _) (hGB g hg))
    · rw [h]; exact core g hg _
  have hspan : ∀ x ∈ Submodule.span R (G : Set K), ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * x ∈ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg => exact core2 g hg
    | zero => intro n j; simp
    | add x y _ _ hx hy => intro n j; rw [mul_add]; exact T.add_mem (hx n j) (hy n j)
    | smul r x _ hx =>
      intro n j
      have hr : (r : K) ∈ (Polynomial.aeval (R := A) t).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval A t]; exact r.2
      obtain ⟨p, hp⟩ := hr
      have hp' : Polynomial.aeval t p = (r : K) := hp
      have this : r • x = (r : K) * x := rfl
      rw [this, ← hp']
      clear hp hp' this
      induction p using Polynomial.induction_on' with
      | add p q hp' hq' =>
        rw [map_add (f := _), add_mul, mul_add]
        exact T.add_mem hp' hq'
      | monomial i a =>
        rw [Polynomial.aeval_monomial]
        have : t⁻¹ ^ n * t ^ j * (algebraMap A K a * t ^ i * x) = a • (t⁻¹ ^ n * t ^ (j + i) * x) := by
          rw [Algebra.smul_def, pow_add]; ring
        rw [this]; exact T.smul_mem a (hx n (j + i))
  intro x hx
  have hx' : x ∈ Algebra.adjoin A ((B : Set K) ∪ {t⁻¹}) := hx
  obtain ⟨n, hn⟩ := exists_pow_mul_mem B t⁻¹ (inv_ne_zero hc.ne) (by rw [inv_inv]; exact hc.tB) hx'
  rw [inv_inv] at hn
  have := hspan _ (hBR _ hn) n 0
  have e : t⁻¹ ^ n * t ^ 0 * (t ^ n * x) = x := by
    rw [pow_zero, mul_one, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc.ne, one_pow, one_mul]
  rwa [e] at this

end LateralTheory.E.NoetherianChartOverlapFiniteComplement
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafClosedSHPosPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial IsLocalRing GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafClosedSHPosPf

theorem hens_of_surj {A B : Type} [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B]
    (φ : A →+* B) (hφ : Function.Surjective φ) : HenselianLocalRing B := by
  have := IsLocalHom.of_surjective φ hφ
  have : IsLocalRing B := IsLocalRing.of_surjective φ hφ
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have hl : f ∈ Polynomial.lifts φ := (Polynomial.lifts_iff_coeff_lifts f).2 (fun n => hφ _)
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  obtain ⟨b₀, rfl⟩ := hφ a₀
  have hev : ∀ (p : A[X]) (x : A), (p.map φ).eval (φ x) = φ (p.eval x) := fun p x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  subst hg
  have h1 : g.eval b₀ ∈ maximalIdeal A := by
    rw [hev] at h₁
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 h₁ (hu.map φ))
  have h2 : IsUnit (g.derivative.eval b₀) := by
    rw [derivative_map, hev] at h₂
    exact IsUnit.of_map φ _ h₂
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian g hgm b₀ h1 h2
  refine ⟨φ a, ?_, ?_⟩
  · rw [IsRoot, hev, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 ham (IsUnit.of_map φ _ hu))

theorem sepClosed_of_surj {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) [IsSepClosed (ResidueField A)] :
    IsSepClosed (ResidueField B) := by
  have hs : Function.Surjective (ResidueField.map φ) := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨residue A a, ResidueField.map_residue φ a⟩
  let e : ResidueField A ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map φ) ⟨(ResidueField.map φ).injective, hs⟩
  refine ⟨fun p hp => ?_⟩
  have h1 : (p.map (e.symm : ResidueField B →+* ResidueField A)).Separable := hp.map
  have h2 := (IsSepClosed.splits_of_separable _ h1).map (e : ResidueField A →+* ResidueField B)
  rw [Polynomial.map_map] at h2
  convert h2
  ext x; simp

theorem sub_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) (R : Type) [CommRing R] (F : Shv R) (n : ℤ)
    (h : Subsingleton (H R (sch.obj Y) F n)) : Subsingleton (H R (sch.obj X) F n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : H R (sch.obj X) F n,
      z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem sub_of_empty (hy : Hyps) (R : Type) [CommRing R] (F : Shv R) (W : Scheme.{0}) [IsEmpty W] (n : ℤ)
    (hn : 0 < n) : Subsingleton (H R (sch.obj W) F n) := by
  have a5 : A5 := hy.2.2.2.2.1
  suffices h : ∀ x : H R (sch.obj W) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro x
  obtain ⟨Z, f, -, -, hf⟩ := a5 R W F n hn x
  have : IsEmpty Z := ⟨fun z => isEmptyElim (f.base z)⟩
  let g : W ⟶ Z := (isInitialOfIsEmpty (X := W)).to Z
  have hgf : g ≫ f = 𝟙 W := (isInitialOfIsEmpty (X := W)).hom_ext _ _
  have : pull R (sch.map (g ≫ f)) F n x = x := by rw [hgf, CategoryTheory.Functor.map_id, pull_id]
  rw [← this, CategoryTheory.Functor.map_comp, pull_comp, hf, map_zero]

theorem LeafClosedSHPos_of : LateralTheory.E.LeafVanBPf.LeafClosedSHPos := by
  intro hy q _ i A _ _ hA hq W' ι' _ n hn
  rcases isEmpty_or_nonempty W' with hW | ⟨⟨w⟩⟩
  · exact sub_of_empty hy _ _ W' n hn
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let B : Type := Γ(W', ⊤)
  let ψ : A →+* B := (ι'.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Surjective ψ := hsurj.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have : Nontrivial B := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    let p := W'.isoSpec.hom.base w
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  obtain ⟨hH, hS⟩ := hA
  have := IsLocalHom.of_surjective ψ hψ
  have hHB : HenselianLocalRing B := hens_of_surj ψ hψ
  have hSB : SH B := ⟨hHB, sepClosed_of_surj ψ hψ⟩
  have h2 := LateralTheory.E.LeafVanBPf.heightFunctionalStatement_of_pairingProperties hy (ZMod q) B hSB (tw q i) n hn
  exact sub_of_iso W'.isoSpec (ZMod q) (tw q i) n h2

end LateralTheory.E.LeafClosedSHPosPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafConsPfC
section
namespace LateralTheory.E.LeafConsPfC

theorem LeafCons_of (hL : LateralTheory.E.LeafConsPf.LeafLoc) : LateralTheory.E.EtaleTopologySheaves.LeafCons :=
  LateralTheory.E.LeafConsPf.LeafCons_of hL LateralTheory.E.LeafConsPfB.LeafGlob_pf

end LateralTheory.E.LeafConsPfC
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDescendFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafDescendFPPf

def FP {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f

theorem fp_of_curve {Ω : Type} [Field Ω] {C : Scheme.{0}} {c : C ⟶ Sp Ω} (h : IsCurve c) : FP c := by
  obtain ⟨_, hp, hs⟩ := h
  have := hp
  have := hs
  refine ⟨inferInstance, inferInstance, inferInstance⟩

def LeafObjFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
      FP q ∧ IsPullback v f q (toR R)

def LeafPairFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → IsPullback v0 c0 q (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

def LeafTripleFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), FP (γ2 ≫ γ1 ≫ c0) →
    ∀ {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP (d1 ≫ q) →
    IsPullback v0 c0 q (toR R) → IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) → γ1 ≫ v0 = v1 ≫ d1 →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1)
      (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1) (w2 : C2 ⟶ E2), PreChain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2

theorem diagramDescent_of_objects_pairs_triples (hO : LeafObjFP) (hP : LeafPairFP) (hT : LeafTripleFP) : LeafDescendFP := by
  intro k _ Ω _ _ C0 c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, q, v0, hq, hsq⟩ := hO k Ω c0 (fp_of_curve hc0)
  obtain ⟨R', hR', E0, E1, q', e1, w0, w1, hq', he1, hs0, hs1, hc⟩ :=
    hP k Ω R hR c0 γ1 (fp_of_curve h1) q v0 hq hsq
  exact hT k Ω R' hR' c0 γ1 γ2 (fp_of_curve h2) q' e1 w0 w1 hq' he1 hs0 hs1 hc

end LateralTheory.E.LeafDescendFPPf

end
end

