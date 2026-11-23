module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.LRingPf
public import Development.EtaleCohomology.EtaleTrace.Bundle0008
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PGysTL
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private def castHom {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht q E n i →+ Ht q E n' i' where
  toFun := Ht.cast hn hi
  map_zero' := by subst hn hi; rfl
  map_add' := LRingPf.cast_add hn hi

private def pairSP {k : Type} [Field k] {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X}
    (h : IsPair d e p ι) : LateralTheory.CohomologicalPurity.SP d :=
  { X := X, Z := Z, S := S k, p := p, ι := ι, e := e
    U := ⟨(Set.range ι)ᶜ, h.cl.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    cl := h.cl, smX := h.big, smZ := h.small, hU := rfl }

theorem UpperTheory.Gal.KunnethLefschetz.gysTL_holds :
    UpperTheory.Gal.KunnethLefschetz.GysTL := by
  unfold GysTL
  intro hI hO k _
  have hg : ∀ d, LateralTheory.CohomologicalPurity.Gysin d := hI.gys
  unfold LateralTheory.CohomologicalPurity.Gysin at hg
  choose gys rs H using hg
  refine ⟨⟨fun q d e Z X p ι h n m i j hn hi =>
    (castHom hn hi).comp (gys d q (pairSP h) n i), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    exact ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.2
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU hs
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    have hx := ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.1
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨u, rfl⟩ := (hx a).1 ha
    rw [hs.elim u 0]
    exact map_zero (rs d q (pairSP h) n i)
  · intro q _ hq d e' e Z' X' Z X p' ι' p ι h' h f u hpb n m i j hn hi a
    subst hn hi
    have hoff : Off ι' (f ⁻¹ᵁ (pairSP h).U) := hO.2 ι' ι f u hpb (pairSP h).U rfl
    have hle : (pairSP h').U ≤ f ⁻¹ᵁ (pairSP h).U :=
      (TopologicalSpace.Opens.ext hoff.symm : (pairSP h').U = f ⁻¹ᵁ (pairSP h).U).le
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.1 (pairSP h') ⟨f, u, hpb, hle⟩ n i).1 a)
  · intro q _ hq d e Z X p ι h n m r s t i j i' j' w h1 h2 h3 h4 k1 k2 k3 k4 a b
    subst h1 h2 h3 k1 k2 k3
    exact (H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.1 n m i j a b
  · intro q r _ hq hr d e Z X p ι h n m i j hn hi a
    subst hn hi
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.2 r hr n i).1 a).symm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPtInt
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id' (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem slice_gen {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (R : Ring l) {X : Scheme.{0}} {p : X ⟶ S k}
    (y : Pt p) {a b n : ℤ} (h : a + b = n) (u : V l X a) (v : V l X b) :
    pb l (slice y) n (ext2 l p h u v) = cupV l X h u (pb l p b (pb l y.1 b v)) := by
  simp only [ext2]
  rw [R.nat (slice y) a b n h]
  have e1 : pb l (slice y) a (pb l (pullback.fst p p) a u) = u := by
    rw [← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_fst]
    exact pb_id' l X a u
  have e2 : pb l (slice y) b (pb l (pullback.snd p p) b v) = pb l p b (pb l y.1 b v) := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_snd]
  rw [e1, e2]

theorem ptInt_holds : PtInt := by
  intro l _ k _ _ hl d X p hSP R L K lam Λ hΛ y w
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunitS : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  have key : (pb l y.1 0) ∘ₗ Λ =
      (lam ∘ₗ pb l (slice y) (2 * d)).smulRight (oneV l (S k)) := by
    apply LinearMap.ext_on (K.span (2 * d))
    rintro _ ⟨a, b, hab, u, v, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply]
    rw [slice_gen R y hab u v]
    by_cases hb : b = 0
    · subst hb
      have ha : a = 2 * d := by omega
      subst ha
      obtain ⟨r, hr, -⟩ := L.line (pb l y.1 0 v)
      rw [hΛ.1, map_smul, hr]
      simp only [map_smul, R.one_nat p hunitS, R.mul_one X hunitX, smul_smul, smul_eq_mul]
      rw [mul_comm]
    · have hz : pb l y.1 b v = 0 := by
        rcases lt_or_gt_of_ne hb with hneg | hpos
        · haveI := L.neg (S k) b hneg
          exact Subsingleton.elim _ _
        · haveI := L.pos b hpos
          exact Subsingleton.elim _ _
      rw [hΛ.2 a b hab hb u v, map_zero, hz, map_zero, map_zero, map_zero, zero_smul]
  exact LinearMap.congr_fun key w

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPtVanT
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem sec_of {k : Type} [Field k] [IsAlgClosed k] {Y : Scheme.{0}} (f : Y ⟶ S k) (hf : Etale f)
    (hs : Surjective f) : ∃ s : S k ⟶ Y, s ≫ f = 𝟙 _ := by
  have hmem : Sieve.generate (Presieve.singleton f) ∈ Scheme.etaleTopology (S k) := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨y, rfl⟩ := hs.surj u
    exact ⟨Y, f, y, hf, rfl, ⟨Y, 𝟙 Y, f, Presieve.singleton.mk, Category.id_comp f⟩⟩
  obtain ⟨Z, h, g, hg, hcomp⟩ := PtCover_of k _ hmem
  cases hg
  exact ⟨h, hcomp⟩

theorem ptVanT_holds : PtVanT := by
  intro hIn k _ _ q n i hn
  have hzero : ∀ x : Ht q (sch.obj (S k)) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hIn.a5 (ZMod q) (S k) (tw q i) n hn x
    obtain ⟨s, hsf⟩ := sec_of f hf hs
    calc x = pull (ZMod q) (𝟙 (sch.obj (S k))) (tw q i) n x := (pull_id _ _ _ _ x).symm
      _ = pull (ZMod q) (sch.map s ≫ sch.map f) (tw q i) n x := by
        rw [← CategoryTheory.Functor.map_comp, hsf, CategoryTheory.Functor.map_id]
      _ = pull (ZMod q) (sch.map s) (tw q i) n (pull (ZMod q) (sch.map f) (tw q i) n x) :=
        pull_comp _ _ _ _ _ x
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PSlice
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem slice_holds : Slice := by
  intro hP l _ k _ _ hl d X p hSP hR G y
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  obtain ⟨hdiag, hpt⟩ := hP k d p inferInstance hsm
  obtain ⟨hy, hpb⟩ := hpt y
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunit : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  simp only [GysQ.diag, GysQ.pt, GysQ.cls, dif_pos hdiag, dif_pos hy]
  rw [G.nat hy hdiag (slice y) y.1
    (by rw [slice, ← Category.assoc, pullback.lift_fst, Category.id_comp]) hpb]
  congr 1
  first
  | exact hR.one_nat y.1 hunitX
  | exact hR.one_nat y.1 hunit

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTrComp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) : pb l (𝟙 X) n = LinearMap.id := by
  show pullHQ l (sch.map (𝟙 X)) n 0 = _
  rw [sch.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem lift_square {A B C : Scheme.{0}} (i : A ⟶ C) [IsOpenImmersion i] (y : B ⟶ C) (y' : B ⟶ A)
    (h : y' ≫ i = y) : IsPullback y' (𝟙 B) i y := (IsPullback.of_horiz_isIso_mono ⟨by simp [h]⟩ : IsPullback (𝟙 B) y' y i).flip

private theorem pt_restrict {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} {p : X ⟶ S k}
    (U : X.Opens) (y : Pt p) (y' : Pt (U.ι ≫ p)) (hy : y'.1 ≫ U.ι = y.1)
    (h : IsPair d 0 p y.1) (h' : IsPair d 0 (U.ι ≫ p) y'.1) :
    pb l U.ι _ (G.pt d y) = G.pt d y' := by
  show pb l U.ι _ (G.cls d 0 p y.1) = G.cls d 0 (U.ι ≫ p) y'.1
  unfold GysQ.cls
  rw [dite_eq_left h, dite_eq_left h', G.nat h' h U.ι (𝟙 _) rfl (lift_square U.ι y.1 y'.1 hy), pb_id]
  rfl

theorem trComp_holds : TrComp := by
  intro hC hO hP l _ k _ _ hl R G d hint X p hsp hpj
  obtain ⟨m, U, hU, hcov, hdisj⟩ := hC k d p hsp hpj
  have hex : ∀ j, ∃ lam : V l (U j : Scheme) (2 * d) →ₗ[ℚ_[l]] ℚ_[l],
      ∀ y : Pt ((U j).ι ≫ p), lam (G.pt d y) = 1 :=
    fun j => hint _ (hU j).1 (hU j).2.1 (hU j).2.2
  choose lamj hlamj using hex
  refine ⟨∑ j, (lamj j).comp (pb l (U j).ι (2 * d)), fun y => ?_⟩
  have hsep : IsSeparated p := by
    haveI := hsp.1
    infer_instance
  obtain ⟨hy, -⟩ := (hP k d p hsep hsp.2).2 y
  obtain ⟨s⟩ : Nonempty (S k) := inferInstance
  have hrange : Set.range y.1 = {y.1 s} := by
    ext t
    constructor
    · rintro ⟨t', rfl⟩
      rw [Subsingleton.elim t' s]
      rfl
    · intro ht
      exact ⟨s, ht.symm⟩
  obtain ⟨j, hj⟩ := hcov (y.1 s)
  have hsub : Set.range y.1 ⊆ Set.range (U j).ι := by
    rw [Scheme.Opens.range_ι, hrange]
    simpa using hj
  let y' : Pt ((U j).ι ≫ p) :=
    ⟨IsOpenImmersion.lift (U j).ι y.1 hsub, by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2⟩
  have hfac : y'.1 ≫ (U j).ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hsep' : IsSeparated ((U j).ι ≫ p) := by
    haveI := (hU j).1.1
    infer_instance
  have hy' : IsPair d 0 ((U j).ι ≫ p) y'.1 := ((hP k d ((U j).ι ≫ p) hsep' (hU j).1.2).2 y').1
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [LinearMap.comp_apply, pt_restrict G d (U j) y y' hfac hy hy', hlamj]
  · intro j' _ hj'
    obtain ⟨W, hW⟩ := hO.1 y.1 hy.cl
    have hle : U j' ≤ W := by
      intro t ht
      show t ∈ (W : Set X)
      rw [hW, hrange]
      rintro (rfl : t = y.1 s)
      exact (hdisj j' j hj').le_bot (show y.1 s ∈ U j' ⊓ U j from ⟨ht, hj⟩)
    rw [LinearMap.comp_apply, ← Scheme.homOfLE_ι X hle, pb_comp, LinearMap.comp_apply]
    unfold GysQ.pt GysQ.cls
    rw [dite_eq_left hy, G.off hy _ W hW, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTwBij
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem inv_of_unit {q : ℕ} {X : Scheme.{0}} (hl : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ X := y
  simpa using hl.map y'.appTop.hom

private theorem cancel_lemma {q : ℕ} {E : Spc} {n i : ℤ} (h1 : n = n) (h2 : i = i) (x : Ht q E n i) :
    Ht.cast h1 h2 x = x := rfl

private theorem eq_of_mul_mul_eq_of_det_ne_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (y : Ht q E n' i') (h : Ht.cast h1 h2 x = y) : x = Ht.cast h1.symm h2.symm y := by
  subst h
  rw [LRingPf.cast_cast, cancel_lemma]

private theorem cancel {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} (hi : Inv q E) {i i' : ℤ} (hs : i + i' = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) {n j w : ℤ}
    (h1 : i' + j = w) (h2 : i + w = j) (c : Ht q E n j) :
    (cup q a ((cup q b c).cast (zero_add n) h1)).cast (zero_add n) h2 = c := by
  obtain ⟨hone, hassoc, -⟩ := h6 q E
  have e1 := hassoc a b c
  rw [eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ hab, cup_cast_left, hone hi, LRingPf.cast_cast] at e1
  have e3 := eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ e1.symm
  rw [cup_cast_right, LRingPf.cast_cast, e3, LRingPf.cast_cast, LRingPf.cast_cast, cancel_lemma]

private theorem swap {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} {i i' : ℤ} (hs : i + i' = 0) (hs' : i' + i = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) :
    (cup q b a).cast (add_zero 0) hs' = one q E := by
  rw [(h6 q E).2.2 b a, cast_usmul, LRingPf.cast_cast, hab]
  simp

private theorem bij_of (hI : In) {k : Type} [Field k] {q : ℕ} [NeZero q] (hq : IsUnit (q : k)) {i i' : ℤ}
    (hs : i + i' = 0) (u : Ht q (sch.obj (S k)) 0 i) (v : Ht q (sch.obj (S k)) 0 i')
    (huv : (cup q u v).cast (add_zero 0) hs = one q (sch.obj (S k))) {X : Scheme.{0}} (p : X ⟶ S k) (n j w : ℤ)
    (hw : i + j = w) : Function.Bijective (twMul q p hw u n) := by
  have hX : Inv q (sch.obj X) := inv_of_unit (LPdCut.unit_of p hq)
  have hS : Inv q (sch.obj (S k)) := inv_of_unit (LPdCut.unit_of (𝟙 (S k)) hq)
  have hUV : (cup q (pull _ (sch.map p) _ 0 u) (pull _ (sch.map p) _ 0 v)).cast (add_zero 0) hs = one q (sch.obj X) := by
    rw [← (hI.a6nat q).2.1 (sch.map p) hS, ← huv, pull_cast, (hI.a6nat q).1]
  have hs' : i' + i = 0 := by omega
  have hVU := swap hI.a6ring hs hs' _ _ hUV
  have h : i' + w = j := by omega
  refine Function.bijective_iff_has_inverse.2 ⟨twMul q p h v n, fun c => ?_, fun c => ?_⟩
  · exact cancel hI.a6ring hX hs' _ _ hVU hw h c
  · exact cancel hI.a6ring hX hs _ _ hUV h hw c

theorem twBij_holds : TwBij := by
  unfold TwBij
  intro hI k _ q _ hq i u v huv X p n j w
  have hvu := swap hI.a6ring (add_neg_cancel i) (neg_add_cancel i) u v huv
  exact ⟨fun hw => bij_of hI hq (neg_add_cancel i) v u hvu p n j w hw,
    fun hw => bij_of hI hq (add_neg_cancel i) u v huv p n j w hw⟩

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.SwapSymmetry
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem pb_self (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (n : ℤ) (x : V l X n) : pb l (𝟙 X) n x = x := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem pb_comp_apply (l : ℕ) [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.swap_holds :
    UpperTheory.Gal.KunnethLefschetz.Swap := by
  intro hP l _ k _ _ hl d X p hSP hR G n w h h' x
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  have hpair := (hP k d p inferInstance hsm).1
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hu := hR.mul_one X hunit
  have key : ∀ f : pullback p p ⟶ X, pullback.diagonal p ≫ f = 𝟙 X →
      cupV l (pullback p p) h (pb l f n x) (G.diag d p) = G.g hpair h x := by
    intro f hf
    have hd : G.diag d p = G.g hpair (show (0 : ℤ) + 2 * d = 2 * d by simp) (oneV l X) := by
      simp only [GysQ.diag, GysQ.cls, dif_pos hpair]
    rw [hd, ← G.proj hpair (show n + 0 = n by simp) h (show (0 : ℤ) + 2 * d = 2 * d by simp) h,
      ← pb_comp_apply, hf, pb_self, hu]
  rw [key _ (by simp), hR.comm (pullback p p) (2 * d) n w h' h,
    key _ (by simp), Int.negOnePow_even _ ⟨d * n, by ring⟩, one_smul]
end
end

