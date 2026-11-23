module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0070
public import Development.EtaleCohomology.EtaleSheaves.ClosedPointLifts.ClosedLift
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.TwPairExists
public import Development.EtaleCohomology.EtaleSheaves.Bundle0071

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTw0GenFreeOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPfM

theorem iso_inv_mono' {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) : Mono e.inv := inferInstance

theorem resι_mono {R : Type} [CommRing R] (F : Shv R) : Mono (resι R F) := by
  unfold resι
  rw [InjectiveResolution.ι'_f_zero]
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ h0 _ (iso_inv_mono' _)))

theorem sec_inj {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have h1 : Mono ((sheafToPresheaf _ _).map φ) := inferInstance
  have h2 : Mono (((sheafToPresheaf _ _).map φ).app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 h2

def LeafTw0TwFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • twGen 0 ζ = 0 → c = 0

theorem LeafTw0GenFree_of (h : LeafTw0TwFree) : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := by
  intro q _ V ζ
  rcases h q V ζ with h0 | h1
  · exact Or.inl h0
  · right
    intro c hc
    apply h1 c
    have : Mono (resι (ZMod q) (tw q 0)) := resι_mono _
    apply sec_inj (resι (ZMod q) (tw q 0)) V
    show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = Sec.map (resι (ZMod q) (tw q 0)) 0
    rw [show Sec.map (resι (ZMod q) (tw q 0)) (c • twGen 0 ζ) = c • resGen 0 ζ from
      map_smul ((resι (ZMod q) (tw q 0)).hom.app (op V)).hom c _, hc]
    simp [Sec.map]

end LateralTheory.E.LeafTw0LocSplitPfM
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PointEvaluationWitness
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.PointEvaluationWitness
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.SecondDegreeKilling LateralTheory.E.LeafPtWPf

theorem hrelZero : LeafHrelZero := by
  intro R _ F U E f hf n
  exact LateralTheory.E.E8.ExciseCut.LeafConeZero_of R ((chains R).map f) F (fun m => hf m) n

theorem eqv_of_iso' {R : Type} [CommRing R] {E' E : Spc} (f : E' ⟶ E) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem eqv_of_square {R : Type} [CommRing R] {Z X Z0 X0 : Spc} (f : Z ⟶ X) (a : Z0 ⟶ Z) (g : Z0 ⟶ X0) (b : X0 ⟶ X)
    [IsIso g] (w : a ≫ f = g ≫ b) (F : Shv R) (ha : Eqv R a F) (hb : Eqv R b F) : Eqv R f F := fun n => by
  have h1 : Function.Bijective (pull R (g ≫ b) F n) := by
    have e : ⇑(pull R (g ≫ b) F n) = pull R g F n ∘ pull R b F n := funext (pull_comp R g b F n)
    rw [e]; exact (eqv_of_iso' g F n).comp (hb n)
  rw [← w] at h1
  have e : ⇑(pull R (a ≫ f) F n) = pull R a F n ∘ pull R f F n := funext (pull_comp R a f F n)
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff' (ha n) _).1 h1

theorem unit_of {k A : Type} [Field k] [CommRing A] {B : Scheme.{0}} (toK : B ⟶ Sp k) (s : Sp A ⟶ B) (q : ℕ)
    (hq : IsUnit (q : k)) : IsUnit (q : A) := by
  have := hq.map (Spec.preimage (s ≫ toK)).hom
  simpa using this

section geo
variable {B W Y : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B) {A : Type} [CommRing A] [IsLocalRing A]
  (s : Sp A ⟶ B)

abbrev rA (A : Type) [CommRing A] [IsLocalRing A] : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Sp A :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

def gF : pullback (prS p ι s ≫ pullback.snd p s) (rA A) ⟶ pullback (pullback.snd p s) (rA A) :=
  pullback.lift (pullback.fst _ _ ≫ prS p ι s) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])


variable {ι p s} in
def hF (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    pullback (pullback.snd p s) (rA A) ⟶ pullback (prS p ι s ≫ pullback.snd p s) (rA A) :=
  pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w)
      (by simp only [Category.assoc]; rw [hw, pullback.condition_assoc]))
    (pullback.snd _ _) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition])

theorem eZ : pullback.fst (prS p ι s ≫ pullback.snd p s) (rA A) ≫ pullback.snd (pullback.snd p s ≫ s) ι ≫ ι =
    pullback.snd (prS p ι s ≫ pullback.snd p s) (rA A) ≫ rA A ≫ s := by
  have c : pullback.snd (pullback.snd p s ≫ s) ι ≫ ι = prS p ι s ≫ pullback.snd p s ≫ s := pullback.condition.symm
  rw [c]
  have := pullback.condition_assoc (f := prS p ι s ≫ pullback.snd p s) (g := rA A) s
  simpa only [Category.assoc] using this

theorem gF_iso (w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W) (hw : w ≫ ι = rA A ≫ s) :
    IsIso (gF ι p s) := by
  refine ⟨⟨hF w hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      · rw [← cancel_mono ι]
        simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
        rw [hw, eZ]
    · simp only [hF, gF, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext <;> simp only [hF, gF, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]
end geo

theorem proper_base_change_closed_fiber_strictly_henselian_equivalence_holds : ProperBaseChangeClosedFiberStrictlyHenselianEquivalence := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp A _ _ s hA w hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  have hqA := unit_of toK s q hq
  have := hp
  have : IsProper (pullback.snd p s) := inferInstance
  have : IsProper (prS p ι s ≫ pullback.snd p s) := inferInstance
  have h1 := hE2 q A hA hqA (pullback.snd p s) i
  have h2 := hE2 q A hA hqA (prS p ι s ≫ pullback.snd p s) i
  have := gF_iso ι p s w hw
  exact eqv_of_square (sch.map (prS p ι s)) (sch.map (pullback.fst _ (rA A))) (sch.map (gF ι p s))
    (sch.map (pullback.fst _ (rA A)))
    (by rw [← Functor.map_comp, ← Functor.map_comp, gF, pullback.lift_fst]) _ h2 h1

theorem LeafPtW_of : LateralTheory.E.SecondDegreeKilling.LeafPtW :=
  LateralTheory.E.LeafPtWPf.LeafPtW_of hrelZero closedLift proper_base_change_closed_fiber_strictly_henselian_equivalence_holds

end LateralTheory.E.PointEvaluationWitness
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PowQEqOne
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfA

theorem pow_q_eq_one {q : ℕ} {B : Type} [CommRing B] (x : B)
    (hx : Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0) : x ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (Polynomial.aeval x) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hx, zero_mul] at this
  exact sub_eq_zero.1 this

theorem local_eq {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {x y : B}
    (hx : x ^ q = 1) (hy : y ^ q = 1) (hr : IsLocalRing.residue B x = IsLocalRing.residue B y) : x = y := by
  have hg := geom_sum₂_mul x y q
  rw [hx, hy, sub_self] at hg
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy (NeZero.ne q)
  have hres : IsLocalRing.residue B (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) =
      IsLocalRing.residue B ((q : B) * y ^ (q - 1)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, map_pow, map_natCast]
    rw [Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue B y ^ (q - 1))]
    · simp
    · intro i hi
      rw [map_mul, map_pow, map_pow, hr, ← pow_add]
      congr 1; have := Finset.mem_range.1 hi; omega
  have hu' : IsUnit (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) := by
    have h1 : IsUnit (IsLocalRing.residue B ((q : B) * y ^ (q - 1))) := (hq.mul (hyu.pow _)).map _
    rw [← hres] at h1
    exact (isUnit_map_iff (IsLocalRing.residue B) _).1 h1
  exact sub_eq_zero.1 ((IsUnit.mul_right_eq_zero hu').1 hg)

theorem res_root {q : ℕ} {B : Type} [CommRing B] [IsLocalRing B] (z : B)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) :
    Polynomial.IsRoot (Polynomial.cyclotomic q (IsLocalRing.ResidueField B)) (IsLocalRing.residue B z) := by
  have h := Polynomial.aeval_algHom_apply (IsLocalRing.residue B).toIntAlgHom z (Polynomial.cyclotomic q ℤ)
  rw [hz, map_zero] at h
  rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem local_pow {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {ζ ξ : B}
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = ζ ^ (a : ZMod q).val := by
  have : NeZero ((q : ℕ) : IsLocalRing.ResidueField B) :=
    ⟨by simpa [map_natCast] using (hq.map (IsLocalRing.residue B)).ne_zero⟩
  have root : ∀ z : B, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
      IsPrimitiveRoot (IsLocalRing.residue B z) q := fun z hz =>
    Polynomial.isRoot_cyclotomic_iff.1 (res_root z hz)
  obtain ⟨i, hi, hpow⟩ := (root ζ hζ).eq_pow_of_pow_eq_one ((root ξ hξ).pow_eq_one)
  have hc : i.Coprime q :=
    ((root ζ hζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hpow ▸ root ξ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine local_eq hq (pow_q_eq_one ξ hξ) ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, pow_q_eq_one ζ hζ, one_pow]
  · rw [map_pow]; exact hpow.symm

end LateralTheory.E.LeafTw0LocGenPfA
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RingCommutativity
section
namespace LateralTheory.E.RingCommutativity

theorem goal_of : LateralTheory.E.CupProductRingLaws.LeafRingComm := LateralTheory.Fix.CupProductTensor.ringComm'

end LateralTheory.E.RingCommutativity
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SysFMPfSys
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.SysFMPfAlg

namespace LateralTheory.E.SysFMPfSys

def IdemSec : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), Function.Injective (phi w) ∧ ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

theorem basicOpen_one_sub {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) (x : X) :
    x ∉ X.basicOpen s ↔ x ∈ X.basicOpen (1 - s) := by
  simp only [Scheme.mem_basicOpen_top, map_sub, map_one]
  have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
  constructor
  · intro h
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
  · intro h h'
    have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self]
    exact not_isUnit_zero (hz ▸ h'.mul h)

theorem Sys_of (hI : IdemSec) : Sys := by
  intro P _ _ W _ w hW y
  obtain ⟨hinj, hrg⟩ := hI W w
  have hid : ∀ s, IsIdempotentElem (phi w s) → IsIdempotentElem s := fun s h =>
    hinj (by rw [map_mul]; exact h.eq)
  let F : Set W := {e | IsIdempotentElem e ∧ ∃ s, phi w s = e ∧ y ∈ w.normalization.basicOpen s}
  have hF0 : (0 : W) ∉ F := by
    rintro ⟨-, s, hs, hy⟩
    have : s = 0 := hinj (by rw [hs, map_zero])
    subst this
    simp at hy
  have hFu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F := by
    intro e he
    obtain ⟨s, rfl⟩ := hrg e he
    by_cases hy : y ∈ w.normalization.basicOpen s
    · exact Or.inl ⟨he, s, rfl, hy⟩
    · exact Or.inr ⟨he.one_sub, 1 - s, by rw [map_sub, map_one], (basicOpen_one_sub (hid s he) y).1 hy⟩
  have hFm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F := by
    rintro e ⟨he, s, rfl, hs⟩ f ⟨hf, t, rfl, ht⟩
    exact ⟨he.mul hf, s * t, map_mul _ _ _, by rw [Scheme.basicOpen_mul]; exact ⟨hs, ht⟩⟩
  obtain ⟨q, hq⟩ := prime_of_filter hW F (fun e h => h.1) hF0 hFu hFm
  let J : Type := {s : Γ(w.normalization, ⊤) // IsIdempotentElem (phi w s) ∧ phi w s ∉ q.asIdeal}
  letI : Preorder J := Preorder.lift (fun s : J => w.normalization.basicOpen s.1)
  have hmono : Monotone (fun s : J => w.normalization.basicOpen s.1) := fun _ _ h => h
  have hne : Nonempty J := ⟨⟨1, by rw [map_one]; exact IsIdempotentElem.one, by rw [map_one]; exact (Ideal.ne_top_iff_one _).1 q.2.ne_top⟩⟩
  haveI : IsCodirectedOrder J := by
    refine ⟨?_⟩
    rintro ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩
    refine ⟨⟨s * t, by rw [map_mul]; exact hs1.mul ht1, by rw [map_mul]; exact q.2.mul_notMem hs2 ht2⟩, ?_, ?_⟩
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen s
      rw [Scheme.basicOpen_mul]; exact inf_le_left
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen t
      rw [Scheme.basicOpen_mul]; exact inf_le_right
  haveI : IsCofiltered J := { nonempty := hne }
  let D : J ⥤ Scheme.{0} := hmono.functor ⋙ w.normalization.restrictFunctor ⋙ Over.forget _
  have hDι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ (w.normalization.basicOpen k.1).ι = (w.normalization.basicOpen j.1).ι :=
    fun f => Over.w (w.normalization.restrictFunctor.map (hmono.functor.map f))
  let ι : ∀ j : J, D.obj j ⟶ w.normalization := fun j => (w.normalization.basicOpen j.1).ι
  have hr : ∀ j : J, Set.range (ι j) = (w.normalization.basicOpen j.1 : Set w.normalization) := fun j =>
    Scheme.Opens.range_ι _
  refine ⟨q, J, inferInstance, inferInstance, D, ι, fun j => ⟨show IsOpenImmersion (w.normalization.basicOpen j.1).ι from
    inferInstance, isClosedImmersion_basicOpen_idem (hid _ j.2.1), ?_⟩, fun {j k} f => ⟨hDι f, ?_⟩, ?_⟩
  · rw [hr]
    obtain ⟨-, s, hs, hy⟩ := (hq _ j.2.1).1 j.2.2
    rwa [hinj hs] at hy
  · have hk : IsClosedImmersion (ι k) := isClosedImmersion_basicOpen_idem (hid _ k.2.1)
    have hc : IsClosedImmersion (D.map f ≫ ι k) := by
      rw [hDι f]; exact isClosedImmersion_basicOpen_idem (hid _ j.2.1)
    have := @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (D.map f) (ι k) hk hc
    infer_instance
  · ext x
    simp only [Set.mem_iInter, hr, RR, Set.mem_setOf_eq, SetLike.mem_coe]
    exact ⟨fun h s h1 h2 => h ⟨s, h1, h2⟩, fun h j => h j.1 j.2.1 j.2.2⟩

theorem SysFM_of (hI : IdemSec) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM :=
  LateralTheory.E.SysFMPf.SysFM_of (Sys_of hI) hE hR

end LateralTheory.E.SysFMPfSys
end
end

