module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.LRingPf
public import Mathlib
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Development.EtaleCohomology.EtaleTrace.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.GysinTwistZeroExists
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

section Tw
variable {k : Type} [Field k]

private theorem twMul_add (q : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) {i j w : ℤ} (hw : i + j = w)
    (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) (a b : Ht q (sch.obj X) n j) :
    twMul q p hw v n (a + b) = twMul q p hw v n a + twMul q p hw v n b := by
  simp only [twMul, map_add (f := _), cast_add]

private def twHom (q : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) {i j w : ℤ} (hw : i + j = w)
    (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) : Ht q (sch.obj X) n j →+ Ht q (sch.obj X) n w :=
  AddMonoidHom.mk' (twMul q p hw v n) (twMul_add q p hw v n)

private theorem twMul_pull (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S k)
    {i j w : ℤ} (hw : i + j = w) (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) (a : Ht q (sch.obj X) n j) :
    pull _ (sch.map f) _ n (twMul q p hw v n a) = twMul q (f ≫ p) hw v n (pull _ (sch.map f) _ n a) := by
  simp only [twMul, pull_cast, (h6 q).1, Functor.map_comp, pull_comp]

private theorem twMul_red (h11 : A11) (Q q : ℕ) [NeZero Q] (hd : q ∣ Q) {X : Scheme.{0}} (p : X ⟶ S k)
    {i j w : ℤ} (hw : i + j = w) (v : Ht Q (sch.obj (S k)) 0 i) (n : ℤ) (a : Ht Q (sch.obj X) n j) :
    red Q q (sch.obj X) n w (twMul Q p hw v n a) =
      twMul q p hw (red Q q _ 0 i v) n (red Q q _ n j a) := by
  simp only [twMul, red_cast, ((h11 Q q hd (sch.obj X)).1), ← pull_red]

private theorem twMul_cup (h6 : DivisorRingCompatibility) (q : ℕ) [NeZero q] {Z : Scheme.{0}} (p : Z ⟶ S k) {n m r i : ℤ}
    (h1 : n + m = r) (hi : 0 + i = i) (v : Ht q (sch.obj (S k)) 0 i) (c : Ht q (sch.obj Z) n 0)
    (b : Ht q (sch.obj Z) m 0) :
    twMul q p (add_zero i) v r (Ht.cast h1 (add_zero 0) (cup q c b)) =
      Ht.cast h1 hi (cup q c (twMul q p (add_zero i) v m b)) := by
  have hc : ∀ {a b a' b' : ℤ} (h : a = a') (h' : b = b') (x : Ht q (sch.obj Z) a b),
      HEq (Ht.cast h h' x) x := by
    intro a b a' b' h h' x
    subst h
    subst h'
    rfl
  simp only [twMul, cup_cast_right]
  generalize (pull (ZMod q) (sch.map p) (tw q i) 0) v = v'
  apply eq_of_heq
  refine (hc _ _ _).trans ?_
  refine HEq.trans ?_ (hc _ _ _).symm
  refine (hc _ _ _).trans ?_
  refine HEq.trans ?_ (hc _ _ _).symm
  have hA := (h6 q (sch.obj Z)).2.1 v' c b
  have hC := (h6 q (sch.obj Z)).2.2 v' c
  have hA2 := (h6 q (sch.obj Z)).2.1 c v' b
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at hC
  have e1 : HEq (cup q v' (cup q c b)) (cup q (cup q v' c) b) := by
    rw [hA]
    exact (hc _ _ _).symm
  have e2 : HEq (cup q (cup q v' c) b) (cup q (cup q c v') b) := by
    rw [hC, cup_cast_left]
    exact hc _ _ _
  have e3 : HEq (cup q (cup q c v') b) (cup q c (cup q v' b)) := by
    rw [hA2]
    exact hc _ _ _
  exact e1.trans (e2.trans e3)

private def gZ {l : ℕ} (GT : GysT k) (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i)) (j : ℕ) {d e : ℕ}
    {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m) :
    Ht (l ^ j) (sch.obj Z) n 0 →+ Ht (l ^ j) (sch.obj X) m 0 :=
  (GT.g (l ^ j) h hn (neg_add_cancel (d : ℤ))).comp (twHom (l ^ j) (ι ≫ p) (add_zero (-(d : ℤ))) (w d j) n)

private theorem gZ_apply {l : ℕ} (GT : GysT k) (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i)) (j : ℕ)
    {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (a : Ht (l ^ j) (sch.obj Z) n 0) :
    gZ GT w j h hn a = GT.g (l ^ j) h hn (neg_add_cancel (d : ℤ))
      (twMul (l ^ j) (ι ≫ p) (add_zero (-(d : ℤ))) (w d j) n a) := rfl

private def mkGys0 (hIn : In) {l : ℕ} [Fact l.Prime] (GT : GysT k) (hu : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k))
    (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i))
    (hw : ∀ (i : ℤ) (j : ℕ), red (l ^ (j + 1)) (l ^ j) _ 0 (-i) (w i (j + 1)) = w i j)
    (hb : ∀ (i : ℤ) (j : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (n : ℤ),
      Function.Bijective (twMul (l ^ j) p (add_zero (-i)) (w i j) n)) : Gys0 k l where
  g j _ _ _ _ _ _ h _ _ hn := gZ GT w j h hn
  exact := by
    intro j d e Z X p ι h n m hn U hU y
    have E := GT.exact (l ^ j) (hu j) h hn (neg_add_cancel (d : ℤ)) U hU
    rw [E y]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := (hb d j (ι ≫ p) n).2 a
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨_, rfl⟩
  inj := by
    intro j d e Z X p ι h n m hn U hU hs
    exact (GT.inj (l ^ j) (hu j) h hn (neg_add_cancel (d : ℤ)) U hU hs).comp (hb d j (ι ≫ p) n).1
  nat := by
    intro j d e' e Z' X' Z X p' ι' p ι h' h f t hfp hpb n m hn a
    have hc : t ≫ ι ≫ p = ι' ≫ p' := by
      rw [← Category.assoc, ← hpb.w, Category.assoc, hfp]
    rw [gZ_apply, gZ_apply, GT.nat (l ^ j) (hu j) h' h f t hpb hn _ _, twMul_pull hIn.a6nat _ t (ι ≫ p), hc]
  proj := by
    intro j d e Z X p ι h n m r s t h1 h2 h3 h4 a b
    rw [gZ_apply, gZ_apply]
    unfold cup0
    rw [twMul_cup hIn.a6ring _ _ h1 (zero_add _)]
    exact GT.proj (l ^ j) (hu j) h h1 h2 h3 h4 (zero_add _) (neg_add_cancel _) (neg_add_cancel _) (add_zero 0) a _
  red := by
    intro j d e Z X p ι h n m hn a
    rw [gZ_apply, gZ_apply, GT.red (l ^ (j + 1)) (l ^ j) (hu _) (dvd_succ l j) h hn _ _,
      twMul_red hIn.a11 _ _ (dvd_succ l j), hw]

end Tw

theorem gysinTwistZero_exists : GysinCondition := by
  intro hI hB l _ k _ _ hl hT hG
  obtain ⟨GT⟩ := hG
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  choose u v huv using hT
  have hu : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := by
    intro j
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hl).pow j
  refine ⟨mkGys0 hI GT hu (fun i j => (v i).1 j) (fun i j => (v i).2 j) ?_⟩
  intro i j X p n
  exact (hB hI k (l ^ j) (hu j) i ((u i).1 j) ((v i).1 j) (huv i j) p n 0 (-i)).1 (add_zero (-i))

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.InjLHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem rank_pos {K : Type} [Field K] {Z' : Scheme.{0}} (p' : Z' ⟶ TranscendenceTraces.gp K) [IsFinite p'] [Surjective p'] :
    1 ≤ p'.finrank (IsLocalRing.closedPoint K) := by
  have hF : Flat p' := inferInstance
  obtain ⟨x, hx⟩ := p'.surjective (IsLocalRing.closedPoint K)
  have h := p'.one_le_finrank_map x
  rwa [hx] at h

theorem injL_holds : InjL := by
  intro hT l _ X Y π hfin hsurj hint hloc hl n
  obtain ⟨hW, -, hD, hTr⟩ := hT
  haveI := hfin
  haveI := hsurj
  haveI := hint
  have hw : TranscendenceTraces.IsNwt π (TranscendenceTraces.nwt π) := hW π hloc
  let g : TranscendenceTraces.gp (Y.residueField (genericPoint Y)) ⟶ Y :=
    Y.fromSpecResidueField (genericPoint Y)
  have hpt : TranscendenceTraces.pt g = genericPoint Y :=
    Scheme.fromSpecResidueField_apply _ _
  have hpush := hD (Y.residueField (genericPoint Y)) (pullback.fst π g) (pullback.snd π g) π g
    (IsPullback.of_hasPullback π g) hloc hpt
  have hd := rank_pos (pullback.snd π g)
  have htr := hTr l n 0 π (TranscendenceTraces.nwt π) _ hw.1 hl hpush
  intro a b hab
  have key : ∀ c, ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) • c =
      TranscendenceTraces.trHQ l π (TranscendenceTraces.nwt π) n 0 (pb l π n c) := by
    intro c
    have := LinearMap.congr_fun htr c
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  have hne : ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) ≠ 0 := by
    norm_cast
    omega
  set_option synthInstance.maxHeartbeats 200000 in
    apply smul_right_injective _ hne
  simp only [key, hab]

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.KunLHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private lemma kun_lof {k : Type} [Field k] (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (p : X ⟶ S k)
    (n a : ℤ) (h : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)) :
    kun l p p n (DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v)) =
      ext2 l p h u v := by
  simp [kun, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]

theorem UpperTheory.Gal.KunnethLefschetz.kunL_holds :
    UpperTheory.Gal.KunnethLefschetz.KunL := by
  intro l _ k _ d X p hb
  refine ⟨fun n => ?_, fun lam m n h => ?_⟩
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨x, rfl⟩ := (hb n).2 w
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
        rw [← DirectSum.lof_eq_of ℚ_[l], kun_lof l p n i (by omega) u v]
        exact Submodule.subset_span ⟨i, n - i, by omega, u, v, rfl⟩
      | add s t hs ht =>
        rw [map_add (f := _), map_add (f := _)]
        exact Submodule.add_mem _ hs ht
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · let e := LinearEquiv.ofBijective (kun l p p n) (hb n)
    have he : ∀ a (ha : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)),
        e.symm (ext2 l p ha u v) = DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v) := by
      intro a ha u v
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, kun_lof]
    refine ⟨(DirectSum.toModule ℚ_[l] ℤ (V l X m) (fun i =>
        if hi : i = 2 * (d : ℤ) then
          TensorProduct.lift ((LinearMap.lsmul ℚ_[l] (V l X m)).compl₁₂
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] ℚ_[l]) lam hi.symm)
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] V l X m) LinearMap.id
              (show m = n - i by omega)))
        else 0)) ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
    · intro u v
      obtain rfl : m = n - 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_pos rfl]
      simp [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply]
    · intro a b h' hbm u v
      obtain rfl : b = n - a := by omega
      have ha : a ≠ 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_neg ha, LinearMap.zero_apply]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.LowLHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.H0LimitCoherence
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem sub_of (l : ℕ) [Fact l.Prime] {E : Spc} {n : ℤ} (h : ∀ j, Subsingleton (Ht (l ^ j) E n 0)) :
    Subsingleton (HQ l E n 0) := by
  have hx : ∀ x : Hl l E n 0, x = 0 := by
    intro x
    apply Subtype.ext
    funext j
    exact @Subsingleton.elim _ (h j) _ _
  refine ⟨fun z w => ?_⟩
  obtain ⟨b, x, -, rfl⟩ := tensor_form l z
  obtain ⟨c, y, -, rfl⟩ := tensor_form l w
  rw [hx x, hx y, TensorProduct.tmul_zero, TensorProduct.tmul_zero]

theorem lowL_holds : LowL := by
  intro hI hP l _ k _ _ hl hR hT
  have hu : IsUnit ((l : ℕ) : Γ(S k, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.mpr hl).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨ω, hω, hone⟩ := hR.one_def (S k) hu
  obtain ⟨hsurj, hinj⟩ := rep_of ω
    (fun j z => by
      obtain ⟨a, ha⟩ := (hT j).1.1 z
      exact ⟨a, by rw [ha]; simp [lv, hω]⟩)
    (fun j a ha => (hT j).1.2 a (by simpa [lv, hω] using ha))
  let e : ℤ_[l] ≃ₗ[ℤ_[l]] Hl l (sch.obj (S k)) 0 0 :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[l] _ ω)
      ⟨fun c d hcd => by
        have h0 : (c - d) • ω = 0 := by
          simpa [sub_smul, sub_eq_zero] using hcd
        exact sub_eq_zero.mp (hinj _ h0),
       fun x => by
        obtain ⟨c, hc⟩ := hsurj x
        exact ⟨c, by simp [hc]⟩⟩
  let Φ : V l (S k) 0 ≃ₗ[ℤ_[l]] ℚ_[l] :=
    (TensorProduct.congr (LinearEquiv.refl ℤ_[l] ℚ_[l]) e.symm).trans (TensorProduct.rid ℤ_[l] ℚ_[l])
  have hΦ : ∀ (q : ℚ_[l]) (u : Hl l (sch.obj (S k)) 0 0),
      Φ (q ⊗ₜ u) = ((e.symm u : ℤ_[l]) : ℚ_[l]) * q := by
    intro q u
    simp [Φ, Algebra.smul_def]
  have he : ∀ c : ℤ_[l], e.symm (c • ω) = c := by
    intro c
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have hsm : ∀ r : ℚ_[l], r • oneV l (S k) = r ⊗ₜ ω := by
    intro r
    rw [hone, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hΦr : ∀ r : ℚ_[l], Φ (r • oneV l (S k)) = r := by
    intro r
    rw [hsm, hΦ]
    have := he 1
    rw [one_smul] at this
    rw [this]
    simp
  have key : ∀ (b : ℤ_[l]) (u : Hl l (sch.obj (S k)) 0 0), b ≠ 0 →
      ((b : ℚ_[l])⁻¹ ⊗ₜ[ℤ_[l]] u : V l (S k) 0) = 0 → u = 0 := by
    intro b u hb h
    have h1 := congrArg Φ h
    rw [hΦ, map_zero] at h1
    have hb' : (b : ℚ_[l]) ≠ 0 := fun h' => hb (Subtype.ext h')
    have h2 : ((e.symm u : ℤ_[l]) : ℚ_[l]) = 0 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 (inv_ne_zero hb')
    have h4 : e.symm u = 0 := Subtype.ext h2
    simpa using congrArg e h4
  have hpb : ∀ {X : Scheme} (y : S k ⟶ X) (q : ℚ_[l]) (x : Hl l (sch.obj X) 0 0),
      pb l y 0 (q ⊗ₜ x) = q ⊗ₜ pullHl l (sch.map y) 0 0 x := by
    intro X y q x
    simp only [pb, pullHQ, LinearMap.baseChange_tmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X n hn
    exact sub_of l (fun j => ((In.a9 hI) (ZMod (l ^ j)) (tw (l ^ j) 0)).1 (sch.obj X) n hn)
  · intro n hn
    exact sub_of l (fun j => hP hI k (l ^ j) n 0 hn)
  · intro z
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    obtain ⟨c, rfl⟩ := hsurj x
    refine ⟨(c : ℚ_[l]) * (b : ℚ_[l])⁻¹, ?_, ?_⟩
    · apply Φ.injective
      rw [hΦr, hΦ, he]
    · intro r hr
      have h1 := congrArg Φ hr
      rw [hΦr, hΦ, he] at h1
      exact h1.symm
  · intro X p hp z hz
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    have hx : x = 0 := by
      apply Subtype.ext
      funext j
      apply ((hT j).2 p hp (x.1 j)).1
      intro y
      have h1 := hz y
      rw [hpb] at h1
      have h2 := key b _ hb h1
      exact congrArg (fun w : Hl l (sch.obj (S k)) 0 0 => w.1 j) h2
    rw [hx, TensorProduct.tmul_zero]
  · intro X p hp hc z y y'
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    rw [hpb, hpb]
    congr 1
    apply Subtype.ext
    funext j
    exact ((hT j).2 p hp (x.1 j)).2 hc y y'

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PAffVan
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem sub_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (q : ℕ) (n i : ℤ)
    (h : Subsingleton (Ht q (sp A) n i)) : Subsingleton (Ht q (sp B) n i) := by
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
      ext x
      simp
    rw [this]
    simp
  refine ⟨fun x y => ?_⟩
  have hx : x = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) := by
    rw [← pull_comp, hid, pull_id]
  have hy : y = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y) := by
    rw [← pull_comp, hid, pull_id]
  rw [hx, hy, Subsingleton.elim (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x)
    (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y)]

theorem UpperTheory.Gal.KunnethLefschetz.affVan_holds :
    UpperTheory.Gal.KunnethLefschetz.AffVan := by
  intro hIn hPt k _ _ q _ hq d n i hn
  show Subsingleton (Ht q (sp (MvPolynomial (Fin d) k)) n i)
  induction d with
  | zero =>
    have h0 : Subsingleton (Ht q (sp k) n i) := hPt hIn k q n i hn
    exact sub_of_equiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm q n i h0
  | succ d ih =>
    have hq' : IsUnit ((q : ℕ) : MvPolynomial (Fin d) k) := by
      have := hq.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k)
      rwa [map_natCast] at this
    have hpoly : Subsingleton (Ht q (sp (Polynomial (MvPolynomial (Fin d) k))) n i) := by
      have hb := hIn.c4 q (MvPolynomial (Fin d) k) hq' i n
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hb.2 x
      obtain ⟨b, rfl⟩ := hb.2 y
      rw [Subsingleton.elim a b]
    exact sub_of_equiv (MvPolynomial.finSuccEquiv k d).toRingEquiv.symm q n i hpoly
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PBasisOne
section
noncomputable section

namespace UpperTheory.Gal.KunnethLefschetz

theorem basisOne_holds : BasisOne := by
  intro F M _ _ _ _ lam hlam
  by_cases h0 : lam = 0
  · haveI := hlam h0
    exact ⟨0, Module.Basis.empty M, fun t => t.elim0⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (LinearMap.ext hc)
  set v : M := (lam x)⁻¹ • x with hvdef
  have hv : lam v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
  set N := LinearMap.ker lam
  let e := Module.finBasis F N
  let f : Fin (Module.finrank F N + 1) → M := Fin.cons v (fun i => v + (e i : M))
  have hrange : LinearMap.range lam = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩
  have hcard : Fintype.card (Fin (Module.finrank F N + 1)) = Module.finrank F M := by
    rw [Fintype.card_fin, ← LinearMap.finrank_range_add_finrank_ker lam, hrange, finrank_top,
      Module.finrank_self, add_comm]
  have hvmem : v ∈ Submodule.span F (Set.range f) :=
    Submodule.subset_span ⟨0, by simp [f]⟩
  have hemem : ∀ i, (e i : M) ∈ Submodule.span F (Set.range f) := by
    intro i
    have h1 : v + (e i : M) ∈ Submodule.span F (Set.range f) :=
      Submodule.subset_span ⟨i.succ, by simp [f]⟩
    have := Submodule.sub_mem _ h1 hvmem
    simpa using this
  have hNmem : ∀ y : N, (y : M) ∈ Submodule.span F (Set.range f) := by
    intro y
    rw [← e.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hemem i))
  have hspan : ⊤ ≤ Submodule.span F (Set.range f) := by
    intro z _
    have hz : z - lam z • v ∈ N := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    have h2 := hNmem ⟨_, hz⟩
    have h3 := Submodule.add_mem _ h2 (Submodule.smul_mem _ (lam z) hvmem)
    simpa using h3
  refine ⟨_, basisOfTopLeSpanOfCardEqFinrank f hspan hcard, fun t => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  refine Fin.cases ?_ (fun i => ?_) t
  · simpa [f] using hv
  · have hk : lam (e i : M) = 0 := (e i).2
    simp [f, hv, hk]

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PKunBij
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem kunBij_holds : KunBij := by
  intro hIn l _ k _ _ hl hR d X p hp n
  obtain ⟨hprop, hsm⟩ := hp
  haveI := hprop
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  apply kun_bijective_of_kunIso l p p n (fun a m r h => hR.isCup _ a m r h)
  exact hIn.kun hIn.a2 hIn.a6nat hIn.a6ring hIn.a7 hIn.a8 hIn.a9 hIn.a10 hIn.a11 hIn.b1 hIn.b2
    hIn.b3 hIn.e2 hIn.e3 hIn.e4 l k (Ne.isUnit hl) p p n 0

end UpperTheory.Gal.KunnethLefschetz

end
end

