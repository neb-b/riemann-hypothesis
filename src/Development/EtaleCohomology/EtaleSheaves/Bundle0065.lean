module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0054
public import Development.EtaleCohomology.EtaleSheaves.Bundle0058
public import Development.EtaleCohomology.EtaleSheaves.Bundle0056
public import Development.EtaleCohomology.EtaleSheaves.Bundle0057
public import Development.EtaleCohomology.EtaleSheaves.Bundle0026
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.EtaleCohomology.EtaleSheaves.Bundle0008
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.LeafTwFieldZPf

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocPowPf
section
noncomputable section
open Polynomial IsLocalRing

namespace LateralTheory.E.LocPowPf

theorem pow_eq_one_of_aeval {q : ℕ} {A : Type} [CommRing A] (ξ : A) (h : aeval ξ (cyclotomic q ℤ) = 0) : ξ ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ξ) hp
  rw [map_mul, h, zero_mul, map_sub, map_pow, aeval_X, map_one] at this
  exact sub_eq_zero.1 this

theorem prim_res {q : ℕ} {A : Type} [CommRing A] [IsLocalRing A] (ξ : GlobalTheory.EtC.Prim q A) :
    IsPrimitiveRoot (residue A ξ.1) q := by
  have hu : IsUnit ((q : ResidueField A)) := by simpa using ξ.2.1.map (residue A)
  have : NeZero (q : ResidueField A) := ⟨hu.ne_zero⟩
  obtain ⟨x, -, hx⟩ := ξ
  change IsPrimitiveRoot (residue A x) q
  rw [← isRoot_cyclotomic_iff, IsRoot, ← map_cyclotomic_int, eval_map]
  change aeval ((residue A).toIntAlgHom x) (cyclotomic q ℤ) = 0
  rw [aeval_algHom_apply, hx, map_zero]

theorem LocPow_of : LateralTheory.E.AugBijPf.LocPow := by
  intro q A _ _ ξ ζ
  have hq : IsUnit (q : A) := ξ.2.1
  have hz := prim_res ζ
  have hx := prim_res ξ
  have : NeZero q := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hcop : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  set η := ζ.1 ^ i with hη
  have h1 : ξ.1 ^ q = 1 := pow_eq_one_of_aeval ξ.1 ξ.2.2
  have h2 : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, pow_eq_one_of_aeval ζ.1 ζ.2.2, one_pow]
  have hres : residue A ξ.1 = residue A η := by rw [hη, map_pow]; exact he.symm
  have hηu : residue A η ≠ 0 := hres ▸ hx.ne_zero (NeZero.ne q)
  have hS : IsUnit (∑ j ∈ Finset.range q, ξ.1 ^ j * η ^ (q - 1 - j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_mul, map_pow, hres]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by simpa using (hq.map (residue A)).ne_zero) (pow_ne_zero _ hηu)
  have key := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [h1, h2, sub_self] at key
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 key)

end LateralTheory.E.LocPowPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSecPfB
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfB

def HomSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  ∃ e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X,
    ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)

def ClassSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0})
  (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X),
  (∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)) →
  ∀ (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem locSecB_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LocSecPf.LocSecB := by
  intro R _ X F n
  obtain ⟨e, he⟩ := h1 R X
  exact h2 R X e he F n

theorem LocSec_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPf.LocSec_of LateralTheory.E.LocSecPfA.locSecA (locSecB_of h1 h2)

end LateralTheory.E.LocSecPfB
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.MulRightMem
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemPowProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mul_left_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : s * y ∈ I • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr (S.mul_mem hs hn)
  · rw [mul_add]; exact add_mem hx hy

theorem mul_right_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : y * s ∈ I • Subalgebra.toSubmodule S := by
  rw [mul_comm]; exact mul_left_mem S I hs hy

theorem mul_mem_mul (S : Subalgebra A K) (I J : Ideal A) {x y : K}
    (hx : x ∈ I • Subalgebra.toSubmodule S) (hy : y ∈ J • Subalgebra.toSubmodule S) :
    x * y ∈ (I * J) • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun a b ha hb => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_left_mem S J hn hy)
  · rw [add_mul]; exact add_mem ha hb

theorem lift_pow (S : Subalgebra A K) (x : K) (hx : x ∈ S) (hp : x * x - x ∈ mS S) (n : ℕ) :
    ∃ y ∈ S, y - x ∈ mS S ∧
      y * y - y ∈ (IsLocalRing.maximalIdeal A ^ (2 ^ n)) • Subalgebra.toSubmodule S := by
  induction n with
  | zero => exact ⟨x, hx, by simp, by simpa [mS] using hp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyx, hyy⟩ := ih
    have hle : IsLocalRing.maximalIdeal A ^ (2 ^ n) ≤ IsLocalRing.maximalIdeal A :=
      Ideal.pow_le_self (by positivity)
    have h2y : y + y - 1 ∈ S := S.sub_mem (S.add_mem hy hy) S.one_mem
    have hpS : y * y - y ∈ S := S.sub_mem (S.mul_mem hy hy) hy
    refine ⟨y - (y + y - 1) * (y * y - y), S.sub_mem hy (S.mul_mem h2y hpS), ?_, ?_⟩
    · rw [show y - (y + y - 1) * (y * y - y) - x = (y - x) - (y + y - 1) * (y * y - y) by ring]
      exact sub_mem hyx (Submodule.smul_mono_left hle (mul_left_mem S _ h2y hyy))
    · have h4 : (y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - 1 - 1 - 1 ∈ S :=
        S.sub_mem (S.sub_mem (S.sub_mem (S.add_mem (S.add_mem (S.add_mem hpS hpS) hpS) hpS)
          S.one_mem) S.one_mem) S.one_mem
      have hsq := mul_mem_mul S _ _ hyy hyy
      rw [← pow_add, ← two_mul, ← pow_succ'] at hsq
      have := mul_right_mem S _ h4 hsq
      convert this using 1
      ring

theorem LZIdemPow_of : LateralTheory.E.LZIdemSumNoetherian.LZIdemPow := by
  intro A _ _ K _ _ B C t hc e f hp k
  obtain ⟨he, hf, hee, hff, hef⟩ := hp
  obtain ⟨b, hb, hbe, hbb⟩ := lift_pow B e he hee (k + 1)
  obtain ⟨c, hcC, hcf, hcc⟩ := lift_pow C f hf hff (k + 1)
  have hBD : B ≤ AdjoinInv B t := fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hCD : C ≤ AdjoinInv B t := by
    intro x hx; rw [hc.glue]; exact Algebra.subset_adjoin (Or.inl hx)
  have hbD : b ∈ AdjoinInv B t := hBD hb
  have hcD : c ∈ AdjoinInv B t := hCD hcC
  have hmono : ∀ (I : Ideal A) (S : Subalgebra A K), S ≤ AdjoinInv B t → ∀ x,
      x ∈ I • Subalgebra.toSubmodule S → x ∈ I • Subalgebra.toSubmodule (AdjoinInv B t) :=
    fun I S h x hx => Submodule.smul_mono (le_refl I) (fun y hy => h hy) hx
  have hpow : IsLocalRing.maximalIdeal A ^ (2 ^ (k + 1)) ≤ IsLocalRing.maximalIdeal A ^ (k + 1) :=
    Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le
  have hp : b * b - b ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ B hBD _ hbb)
  have hq : c * c - c ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ C hCD _ hcc)
  have hd1 : b - c ∈ (IsLocalRing.maximalIdeal A ^ 1) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [pow_one, show b - c = (b - e) + (e - f) - (c - f) by ring]
    exact sub_mem (add_mem (hmono _ B hBD _ hbe) hef) (hmono _ C hCD _ hcf)
  have hcube : (b - c) * (b - c) * (b - c) - (b - c) ∈
      (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [show (b - c) * (b - c) * (b - c) - (b - c) = (b * b - b) - (c * c - c) - (c + c) * (b * b - b)
      + (b + b) * (c * c - c) + (b - c) * (b * b - b) + (b - c) * (c * c - c) by ring]
    have hbc : b - c ∈ AdjoinInv B t := (AdjoinInv B t).sub_mem hbD hcD
    refine add_mem (add_mem (add_mem (sub_mem (sub_mem hp hq) ?_) ?_) ?_) ?_
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hcD hcD) hp
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hbD hbD) hq
    · exact mul_left_mem _ _ hbc hp
    · exact mul_left_mem _ _ hbc hq
  have key : ∀ j, j + 1 ≤ k + 1 →
      b - c ∈ (IsLocalRing.maximalIdeal A ^ (j + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    intro j
    induction j with
    | zero => intro _; simpa using hd1
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h3 := mul_mem_mul _ _ _ (mul_mem_mul _ _ _ h1 h1) h1
      rw [← pow_add, ← pow_add] at h3
      have h3' := Submodule.smul_mono_left (Ideal.pow_le_pow_right (show j + 1 + 1 ≤ j + 1 + (j + 1) + (j + 1) by omega)) h3
      have hc' := Submodule.smul_mono_left (Ideal.pow_le_pow_right hj) hcube
      rw [show b - c = (b - c) * (b - c) * (b - c) - ((b - c) * (b - c) * (b - c) - (b - c)) by ring]
      exact sub_mem h3' hc'
  refine ⟨b, hb, c, hcC, ?_, hcf, ?_⟩
  · rw [← neg_sub]; exact neg_mem hbe
  · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (key k le_rfl)

end LateralTheory.E.LZIdemPowProof
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelativeCohomologyForgetInjectiveDegreeZeroOfSub
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0VPf
open CochainComplex CochainComplex.HomComplex
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

def LeafSecTr : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0), ∃ s : Sec (tw q i) U.left,
  (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
  (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0)

def LeafSecV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale) (s : Sec (tw q i) U.left),
  Cov U (fun U' a => Sec.res (toBY (g2 ≫ g1 ≫ p) U' ≫ a.left) s = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem res_comp {q : ℕ} {i : ℤ} {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Sec (tw q i) Z) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem relative_cohomology_forget_injective_degree_zero_of_subsingleton (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) z (zero_add 0)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  obtain rfl : m = -1 := by omega
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] at hγ
  set φ := (chains R).map f
  let w : Cochain (mappingCone φ) (res R F) (-1) := mappingCone.descCochain φ (0 : Cochain ((chains R).obj U) (res R F) (-2)) γ (by norm_num)
  let z' : Cochain (mappingCone φ) (res R F) 0 := z.1 - δ (-1) 0 w
  have hz'c : δ 0 1 z' = 0 := by
    simp [z', δ_δ]
  have hinr : (Cochain.ofHom (mappingCone.inr φ)).comp z' (zero_add 0) = 0 := by
    have h1 : δ (-1) 0 ((Cochain.ofHom (mappingCone.inr φ)).comp w (zero_add _)) =
        (Cochain.ofHom (mappingCone.inr φ)).comp (δ (-1) 0 w) (zero_add 0) := by
      rw [δ_ofHom_comp]
    simp only [z', Cochain.comp_sub, ← h1, w, mappingCone.inr_descCochain]
    rw [hγ, sub_self]
  let β : Cochain ((chains R).obj U) (res R F) (-1) := (mappingCone.inl φ).comp z' (by norm_num)
  have hβc : δ (-1) 0 β = 0 := by
    simp only [β]
    rw [δ_comp _ _ (by norm_num) 0 1 0 (by norm_num) (by norm_num) (by norm_num), mappingCone.δ_inl, hz'c]
    simp only [Cochain.comp_zero, smul_zero, add_zero, Cochain.ofHom_comp]
    rw [Cochain.comp_assoc_of_first_is_zero_cochain, hinr]
    simp
  have hβ0 : CohomologyClass.mk (Cocycle.mk β 0 (by norm_num) hβc) = (0 : H R U F (-1)) := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff] at hβ0
  obtain ⟨m', hm', ε, hε⟩ := hβ0
  obtain rfl : m' = -2 := by omega
  have hz' : z' = δ (-1) 0 (mappingCone.descCochain φ ε 0 (by norm_num)) := by
    rw [mappingCone.δ_descCochain _ _ _ _ 0 (by norm_num)]
    rw [mappingCone.ext_cochain_from_iff φ (-1) 0 (by norm_num)]
    constructor
    · simp [β] at hε
      simp [hε, β]
    · simp [hinr]
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨-1, by norm_num, w + mappingCone.descCochain φ ε 0 (by norm_num), ?_⟩
  rw [δ_add, ← hz']
  simp [z']

theorem secTr (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) (U : B.Etale)
    (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0) : ∃ s : Sec (tw q i) U.left,
    (∀ (U' : B.Etale) (a : U' ⟶ U), Sec.res a.left s = 0 → rB q i ι a 0 c = 0) ∧
    (∀ (U' : B.Etale) (a : U' ⟶ U), rY q i P ι a 0 (bY q i P ι U 0 c) = 0 → Sec.res (toBY P U' ≫ a.left) s = 0) := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨hneg, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨(e U.left).symm (fgt _ _ _ 0 c), ?_, ?_⟩
  · intro U' a ha
    apply relative_cohomology_forget_injective_degree_zero_of_subsingleton _ _ _ (hneg _ (-1) (by norm_num))
    rw [relNat]
    have := hnat a.left ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply] at this
    rw [this, ha, map_zero]
  · intro U' a ha
    have h0 := congrArg (fgt _ _ _ 0) ha
    rw [map_zero, relNat, relNat, ← pull_comp, ← Functor.map_comp] at h0
    have hsq : resY P a ≫ toBY P U = toBY P U' ≫ a.left := by simp only [resY, toBY]; exact pullback.lift_snd _ _ _
    rw [hsq] at h0
    have := hnat (toBY P U' ≫ a.left) ((e U.left).symm (fgt _ _ _ 0 c))
    rw [AddEquiv.apply_symm_apply, h0] at this
    exact (e _).injective (by rw [← this, map_zero])

def LeafSHPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ) {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left), ∃ (A : Type) (_ : CommRing A) (t : Sp A ⟶ U.left), SH A ∧
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a : U' ⟶ U), S a ∧ ∃ t' : Sp A ⟶ U'.left, t' ≫ a.left = t) ∧
  ∀ s : Sec (tw q i) U.left, Sec.res t s = 0 → ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

theorem LeafSecV_of (hP : LeafSHPt) : LeafSecV := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U s hc x hx
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  obtain ⟨-, e, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨A, _, t, hA, hO, hL, hG⟩ := hP hH q k hq i U (U.hom ≫ s0) x
  apply hG
  set P := g2 ≫ g1 ≫ p
  have hxV : x ∈ (U.hom ⁻¹ᵁ V) := by
    change U.hom x ∈ (V : Set B); rw [hV']; exact hx
  have hr : Set.range (t ≫ U.hom) ⊆ (V : Set B) := by
    rintro _ ⟨z, rfl⟩
    exact hO _ hxV ⟨z, rfl⟩
  have hinj := ((hSH A (t ≫ U.hom) hA hr).2.2.2).1
  obtain ⟨S, hS, hPS⟩ := hc
  obtain ⟨U', a, hSa, t', ht'⟩ := hL S hS
  have h0 := hPS U' a hSa
  have hm : pullback.snd P (t ≫ U.hom) ≫ t =
      pullback.map P (t ≫ U.hom) P U'.hom (𝟙 _) t' (𝟙 B) (by simp) (by
        rw [Category.comp_id, ← ht', Category.assoc]; congr 1; simpa using a.w) ≫ (toBY P U' ≫ a.left) := by
    simp only [toBY]
    rw [pullback.lift_snd_assoc, Category.assoc, ht']
  apply (e _).injective
  apply hinj
  rw [map_zero, map_zero]
  change pull _ (sch.map (pullback.snd P (t ≫ U.hom))) _ 0 (e _ (Sec.res t s)) = 0
  rw [hnat, ← res_comp, hm, res_comp, h0]
  simp

theorem LeafInj0V_of_sec (hT : LeafSecTr) (hS : LeafSecV) : LeafInj0V := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s0 ι _ V hV' p g1 g2 hp1 hp2 hp3 hSH U c hc x hx
  obtain ⟨s, h1, h2⟩ := hT hH q i ι (g2 ≫ g1 ≫ p) U c
  obtain ⟨U', a, y, hy, hs⟩ := hS hH q k hq i s0 ι V hV' p g1 g2 hp1 hp2 hp3 hSH U s
    (hc.mono fun U'' b hb => h2 U'' b hb) x hx
  refine ⟨U', a, y, hy, Cov.all fun U'' b => h1 U'' (b ≫ a) ?_⟩
  change Sec.res (b.left ≫ a.left) s = 0
  rw [res_comp, hs]
  simp
theorem LeafInj0V_of (hP : LeafSHPt) : LeafInj0V :=
  LeafInj0V_of_sec (fun hH q _ i _ _ _ ι P U c => secTr hH q i ι P U c) (LeafSecV_of hP)
end LateralTheory.E.LeafInj0VPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ResZeroOfRange
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafSurj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.E8.TwSec

theorem neg_cochain (R : Type) [CommRing R] (E : Spc) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain ((chains R).obj E) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (LateralTheory.E.LeafNegPf.res_isZero R F q hq).eq_of_tgt _ _
  · exact (LateralTheory.E.LeafNegPf.chains_isZero R E p (by omega)).eq_of_src _ _

theorem fgt_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (y : Hrel R f F 0)
    (h : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) z (zero_add 0)) = 0 at h
  rw [CohomologyClass.mk_eq_zero_iff] at h
  obtain ⟨m, hm, β, hβ⟩ := h
  rw [neg_cochain R E F m (by omega) β, δ_zero] at hβ
  have hz : z = 0 := by
    apply Cocycle.ext
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    refine ⟨(neg_cochain R U F _ (by omega) _).trans (neg_cochain R U F _ (by omega) _).symm, ?_⟩
    rw [Cocycle.coe_zero, Cochain.comp_zero]
    exact hβ.symm
  rw [hz]
  rfl

theorem pull_fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ n z

theorem twPt : LeafTwPt := LeafTwPt_of LeafTwAdj_of LeafTwGen_of LeafTwFieldZ_of

theorem secKill (q : ℕ) [NeZero q] {X Z : Scheme.{0}} (ι : Z ⟶ X) (j : ℤ) (s : Sec (tw q j) X) (hs : Sec.res ι s = 0)
    (z : Z) : ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ ι z ∈ Set.range w ∧ Sec.res w s = 0 := by
  obtain ⟨U, w, hw, ⟨u, hu⟩, t, ht⟩ := LateralTheory.E.LeafOfRingsLocSurjPf.LeafOfRingsLocSurj_of (ZMod q) (twF q j) X s (ι z)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := ι) u z hu
  have e2 : Sec.res (F := tw q j) (pullback.fst w ι) (Sec.res w s) = 0 := by
    rw [← res_comp, pullback.condition, res_comp, hs]
    exact map_zero _
  have hP : ofRings.sec (twF q j) _ (((twF q j).map (Scheme.Γ.map (pullback.fst w ι).op)).hom t) = 0 := by
    rw [← sec_res, ← ht]
    exact e2
  obtain ⟨V, v, -, ⟨v0, hv0⟩, hV⟩ := LeafOfRingsLocInj_of (ZMod q) (twF q j) _ _ hP p
  obtain ⟨W, w', hw', ⟨a, ha⟩, hW⟩ := twPt q j U u t V (v ≫ pullback.fst w ι) v0 (by simp [hv0, hp1])
    ((twF_res_comp j _ _ t).trans hV)
  refine ⟨W, w' ≫ w, inferInstance, ⟨a, by simp [ha, hu]⟩, ?_⟩
  rw [res_comp]
  have e := sec_res (twF q j) w' t
  rw [hW] at e
  exact (congrArg (Sec.res w') ht).trans (e.trans (sec_zero _ _))

def zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : Set X :=
  {x | ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ x ∈ Set.range w ∧ Sec.res w s = 0}

theorem isOpen_zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : IsOpen (zeroLocus s) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨W, w, hw, hx, h0⟩
  exact ⟨Set.range w, fun y hy => ⟨W, w, hw, hy, h0⟩, w.isOpenMap.isOpen_range, hx⟩

theorem res_zero_of_range {R : Type} [CommRing R] {F : Shv R} {X T : Scheme.{0}} (s : Sec F X) (g : T ⟶ X)
    (hg : ∀ t, g t ∈ zeroLocus s) : Sec.res g s = 0 := by
  apply LateralTheory.E.PointDetect0Pf.etSep R F T
  intro t
  obtain ⟨W, w, hw, ⟨u, hu⟩, h0⟩ := hg t
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := w) t u hu.symm
  refine ⟨_, pullback.fst g w, inferInstance, ⟨p, hp1⟩, ?_⟩
  rw [← res_comp, pullback.condition, res_comp, h0]
  exact map_zero _

theorem core (h9 : A9) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) [IsProper P]
    (U : B.Etale) (y : Hrel (ZMod q) (sch.map (prU P ι U)) (tw q i) 0) (x : U.left) (hx : U.hom x ∈ Set.range ι) :
    ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i P ι (b ≫ a) 0 y = 0 := by
  obtain ⟨e, he, -⟩ := (h9 (ZMod q) (tw q i)).2
  obtain ⟨s, hs⟩ := (e (YU P U)).surjective (fgt (ZMod q) (sch.map (prU P ι U)) (tw q i) 0 y)
  have hZ : Sec.res (prU P ι U) s = 0 := by
    apply (e _).injective
    rw [← he, hs, map_zero]
    exact pull_fgt _ _ _ _ _
  have hcl : IsClosed ((toBY P U) '' (zeroLocus s)ᶜ) :=
    (toBY P U).isClosedMap _ (isOpen_zeroLocus s).isClosed_compl
  let O : U.left.Opens := ⟨_, hcl.isOpen_compl⟩
  have hxO : x ∈ O := by
    rintro ⟨t, ht, htx⟩
    obtain ⟨w0, hw0⟩ := hx
    obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd P U.hom ≫ U.hom) (g := ι) t w0
      (by rw [hw0, ← htx]; rfl)
    apply ht
    rw [← hp1]
    exact secKill q (prU P ι U) i s hZ p
  have hU : Etale U.hom := U.prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (inferInstanceAs (Etale (O.ι ≫ U.hom)))
  let a : U' ⟶ U := MorphismProperty.Over.homMk O.ι rfl
  refine ⟨U', a, ⟨⟨x, hxO⟩, rfl⟩, fun U'' b => ?_⟩
  apply fgt_zero
  refine (relNat _ _ _ _ _ _ _ _ _).trans ?_
  rw [← hs, he, res_zero_of_range s _ ?_, map_zero]
  intro t
  by_contra hn
  have h1 : resY P (b ≫ a) ≫ toBY P U = (toBY P U'' ≫ b.left) ≫ O.ι := by
    simp only [resY, toBY, pullback.lift_snd]
    rfl
  have h2 : toBY P U (resY P (b ≫ a) t) ∈ O := by
    rw [← Scheme.Hom.comp_apply, h1]
    exact ((toBY P U'' ≫ b.left) t).2
  exact h2 ⟨_, hn, rfl⟩

theorem LeafSurj0W_of : LateralTheory.E.LeafSurj0Pf.LeafSurj0W := by
  intro hy q _ k _ _ i B W Y0 Y1 Y2 _ ι _ V _ p g1 g2 _ _ h2 _ U y x hx
  exact core hy.2.2.2.2.2.2.2.1 q i ι (g2 ≫ g1 ≫ p) U y x hx

end LateralTheory.E.LeafSurj0WPf
end
end

