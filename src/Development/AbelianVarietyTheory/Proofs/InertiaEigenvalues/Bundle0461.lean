module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversal
section
open GlobalTheory.Prism GlobalTheory.BSP CategoryTheory

namespace GlobalTheory.BSP.PoUniv

variable {l : ℕ} {R : Type} [CommRing R]

def deltaLocus {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B) (c : A →+* B) :
    Subring A where
  carrier := {x | c (D.δ x) = D'.δ (c x)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_mul, D'.δ_mul, ha, hb]
  one_mem' := by simp [D.δ_one, D'.δ_one]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_add, D'.δ_add, ha, hb]
  zero_mem' := by simp [D.δ_zero, D'.δ_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    have e1 := congrArg c (D.δ_add a (-a))
    have e2 := D'.δ_add (c a) (-c a)
    rw [add_neg_cancel, D.δ_zero] at e1
    rw [add_neg_cancel, D'.δ_zero] at e2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_zero, map_sub, map_add (f := _), map_sum, map_mul, map_pow, map_natCast, map_neg, ha] at e1 ⊢
    linear_combination e2 - e1

open CategoryTheory in
private lemma exists_ringHom_of_isPushout {A X Y P W : Type} [CommRing A] [CommRing X]
    [CommRing Y] [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P}
    {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (u : X →+* W) (v : Y →+* W) (huv : u.comp f = v.comp g) :
    ∃ w : P →+* W, w.comp i = u ∧ w.comp j = v := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom u =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom v := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, huv]
  exact ⟨(hP.desc (W := CommRingCat.of W) _ _ hw).hom,
    congrArg CommRingCat.Hom.hom (hP.inl_desc (W := CommRingCat.of W) _ _ hw),
    congrArg CommRingCat.Hom.hom (hP.inr_desc (W := CommRingCat.of W) _ _ hw)⟩

open CategoryTheory in
private lemma ringHom_eq_of_isPushout_of_comp_eq {A X Y P W : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) {u v : P →+* W} (hi : u.comp i = v.comp i)
    (hj : u.comp j = v.comp j) : u = v := by
  have h := hP.hom_ext (W := CommRingCat.of W) (k := CommRingCat.ofHom u)
    (l := CommRingCat.ofHom v) (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi])
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hj])
  exact congrArg CommRingCat.Hom.hom h

open CategoryTheory in
private lemma factorPow_comp_qmap_eq_qmap_comp_factorPow {l : ℕ} {R : Type} [CommRing R]
    {P P' : _root_.GlobalTheory.Prism.Obj l R} (f : _root_.GlobalTheory.Prism.Hom P P') {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P') hle).comp
        (_root_.GlobalTheory.BSP.qmap f n) =
      (_root_.GlobalTheory.BSP.qmap f m).comp
        (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P) hle) := by
  refine Ideal.Quotient.ringHom_ext ?_
  ext x
  simp only [RingHom.comp_apply, _root_.GlobalTheory.BSP.qmap_mk]
  rfl

open CategoryTheory in
private lemma eq_of_forall_mk_pow_eq_of_isHausdorff {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A]
    {x y : A} (hxy : ∀ n, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) :
    x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  exact hxy n

open CategoryTheory in
private lemma mem_subring_of_isPushout_of_maps_mem {A X Y P : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (T : Subring P) (hi : ∀ x, i x ∈ T) (hj : ∀ y, j y ∈ T)
    (p : P) : p ∈ T := by
  have hcomm : i.comp f = j.comp g := congrArg CommRingCat.Hom.hom hP.w
  obtain ⟨r, hr1, hr2⟩ := exists_ringHom_of_isPushout hP (i.codRestrict T hi)
    (j.codRestrict T hj) (by
      ext z
      exact RingHom.congr_fun hcomm z)
  have hid : T.subtype.comp r = RingHom.id P := by
    refine ringHom_eq_of_isPushout_of_comp_eq hP ?_ ?_
    · ext x
      show ((r (i x) : T) : P) = i x
      rw [← RingHom.comp_apply, hr1]
      rfl
    · ext y
      show ((r (j y) : T) : P) = j y
      rw [← RingHom.comp_apply, hr2]
      rfl
  have hp : T.subtype (r p) = p := RingHom.congr_fun hid p
  rw [← hp]
  exact (r p).2


open CategoryTheory in
theorem _root_.GlobalTheory.BSP.PoUniv.isPO_univ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    (B C B' C' : _root_.GlobalTheory.Prism.Obj l R) (h : _root_.GlobalTheory.Prism.Hom B C)
    (k : _root_.GlobalTheory.Prism.Hom B B') (k' : _root_.GlobalTheory.Prism.Hom C C') (h' : _root_.GlobalTheory.Prism.Hom B' C')
    (H : _root_.GlobalTheory.BSP.IsPO h k k' h') (Q : _root_.GlobalTheory.Prism.Obj l R)
    (a : _root_.GlobalTheory.Prism.Hom C Q) (b : _root_.GlobalTheory.Prism.Hom B' Q)
    (hab : a.comp h = b.comp k) :
    ∃! c : _root_.GlobalTheory.Prism.Hom C' Q,
      c.comp k' = a ∧ c.comp h' = b := by
  haveI : IsAdicComplete (_root_.GlobalTheory.BSP.adI Q) Q.A :=
    Q.complete
  have hex : ∀ m, ∃ ψ : C'.A ⧸ _root_.GlobalTheory.BSP.adI C' ^ m →+*
      Q.A ⧸ _root_.GlobalTheory.BSP.adI Q ^ m,
      ψ.comp (_root_.GlobalTheory.BSP.qmap k' m) = _root_.GlobalTheory.BSP.qmap a m ∧
      ψ.comp (_root_.GlobalTheory.BSP.qmap h' m) = _root_.GlobalTheory.BSP.qmap b m := fun m =>
    exists_ringHom_of_isPushout (H.po m) _ _ (by
      rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hab])
  choose ψ hψa hψb using hex
  have hψa' : ∀ m x, ψ m (Ideal.Quotient.mk _ (k'.f x)) =
      Ideal.Quotient.mk _ (a.f x) := by
    intro m x
    have hx := RingHom.congr_fun (hψa m) (Ideal.Quotient.mk _ x)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hx
  have hψb' : ∀ m y, ψ m (Ideal.Quotient.mk _ (h'.f y)) =
      Ideal.Quotient.mk _ (b.f y) := by
    intro m y
    have hy := RingHom.congr_fun (hψb m) (Ideal.Quotient.mk _ y)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hy
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp
        ((ψ n).comp (Ideal.Quotient.mk _)) = (ψ m).comp (Ideal.Quotient.mk _) := by
    intro m n hle
    have key : (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp (ψ n) =
        (ψ m).comp (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI C') hle) := by
      refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
      · rw [RingHom.comp_assoc, hψa, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψa]
      · rw [RingHom.comp_assoc, hψb, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψb]
    rw [← RingHom.comp_assoc, key, RingHom.comp_assoc]
    congr 1
  obtain ⟨c0, hc0⟩ : ∃ c0 : C'.A →+* Q.A, ∀ n x,
      Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI Q ^ n) (c0 x) = ψ n (Ideal.Quotient.mk _ x) :=
    ⟨_, fun n x => IsAdicComplete.mk_liftRingHom _ _ hcompat n x⟩
  have hmap : ∀ n z, z ∈ _root_.GlobalTheory.BSP.adI C' ^ n →
      c0 z ∈ _root_.GlobalTheory.BSP.adI Q ^ n := by
    intro n z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem, hc0, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  have hk : ∀ x, c0 (k'.f x) = a.f x := fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψa']
  have hh : ∀ y, c0 (h'.f y) = b.f y := fun y =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψb']
  have hδ : ∀ x, c0 (C'.D.δ x) =
      Q.D.δ (c0 x) := by
    intro x
    have hS : ∀ n, ∃ s ∈ _root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0,
        x - s ∈ _root_.GlobalTheory.BSP.adI C' ^ n := by
      intro n
      have hT := mem_subring_of_isPushout_of_maps_mem (H.po n)
        ((_root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0).map
          (Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI C' ^ n)))
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (k'.f y)) =
            Q.D.δ (c0 (k'.f y))
          rw [← k'.f_δ, hk, hk, a.f_δ])
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (h'.f y)) =
            Q.D.δ (c0 (h'.f y))
          rw [← h'.f_δ, hh, hh, b.f_δ])
        (Ideal.Quotient.mk _ x)
      obtain ⟨s, hs, hsx⟩ := Subring.mem_map.mp hT
      exact ⟨s, hs, Ideal.Quotient.eq.mp hsx.symm⟩
    refine sub_eq_zero.mp (eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨s, hs, hxs⟩ := hS (n + 1)
    have hs' : c0 (C'.D.δ s) =
        Q.D.δ (c0 s) := hs
    have hlC : (l : C'.A) ∈ _root_.GlobalTheory.BSP.adI C' :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have hlQ : (l : Q.A) ∈ _root_.GlobalTheory.BSP.adI Q :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have h1 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l C'.A C'.D _ hlC n s
      (x - s) hxs
    have h2 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l Q.A Q.D _ hlQ n (c0 s)
      (c0 (x - s)) (hmap _ _ hxs)
    rw [add_sub_cancel] at h1
    rw [← map_add (f := _), add_sub_cancel] at h2
    have h3 := hmap n _ h1
    rw [map_sub, hs'] at h3
    have h4 := Ideal.sub_mem _ h3 h2
    convert h4 using 1
    ring
  have hI : ∀ z ∈ C'.I, c0 z ∈ Q.I := by
    intro z hz
    have hcb : c0.comp h'.f = b.f := RingHom.ext hh
    have hz' : z ∈ Ideal.map h'.f B'.I := by
      rw [_root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' C' h']
      exact hz
    have hmem := Ideal.mem_map_of_mem c0 hz'
    rwa [Ideal.map_map, hcb, _root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' Q b] at hmem
  have hstr : ∀ (r : R) (z : C'.A),
      Ideal.Quotient.mk C'.I z = C'.str r →
      Ideal.Quotient.mk Q.I (c0 z) = Q.str r := by
    intro r z hz
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (B'.str r)
    have h1 := h'.f_str r y hy
    have h2 := b.f_str r y hy
    rw [← h2, ← hh, Ideal.Quotient.eq, ← map_sub]
    refine hI _ ?_
    rw [← Ideal.Quotient.eq, hz, h1]
  let c : _root_.GlobalTheory.Prism.Hom C' Q := ⟨c0, hδ, hI, hstr⟩
  have hcomm : c.comp k' = a ∧ c.comp h' = b :=
    ⟨_root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hk),
      _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hh)⟩
  refine ⟨c, hcomm, fun c' hc' => ?_⟩
  refine _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
  have hq : _root_.GlobalTheory.BSP.qmap c' n = _root_.GlobalTheory.BSP.qmap c n := by
    refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.1, hcomm.1]
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.2, hcomm.2]
  have hx := RingHom.congr_fun hq (Ideal.Quotient.mk _ x)
  simpa only [_root_.GlobalTheory.BSP.qmap_mk] using hx

end GlobalTheory.BSP.PoUniv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjection
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharBlock

open Polynomial Matrix

theorem rank_blockPol_of_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (d : Fin t → K) (hba : b * a = 1) :
    (a * b).rank = t ∧
      blockPol (a * b) (a * Matrix.diagonal d * b) = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  constructor
  · apply le_antisymm
    · exact (Matrix.rank_mul_le_left a b).trans (by simpa using Matrix.rank_le_width a)
    · have h1 : b * (a * b) * a = 1 := by
        rw [← Matrix.mul_assoc b a b, hba, Matrix.one_mul, hba]
      have h2 : (b * (a * b) * a).rank ≤ (a * b).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      rw [h1, Matrix.rank_one] at h2
      simpa using h2
  · unfold blockPol
    have hba' : b.map (C (R := K)) * a.map (C (R := K)) = 1 := by
      rw [← Matrix.map_mul, hba]
      simp
    set D : Matrix (Fin t) (Fin t) K[X] := Matrix.diagonal (fun c => (X : K[X]) - C (d c)) with hD
    have hD' : D = (X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - (Matrix.diagonal d).map (C (R := K)) := by
      ext1 i j
      by_cases h : i = j
      · subst h; simp [hD]
      · simp [hD, h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    have key : (X : K[X]) • (a * b).map (C (R := K)) - (a * Matrix.diagonal d * b).map (C (R := K)) + 1
        - (a * b).map (C (R := K)) = 1 + a.map (C (R := K)) * ((D - 1) * b.map (C (R := K))) := by
      rw [hD', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [key, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hba', Matrix.mul_one, add_sub_cancel, hD,
      Matrix.det_diagonal]

theorem rank_blockPol_proj : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (E M : Matrix (Fin n) (Fin n) K) (d : Fin t → K), (∀ u, e (E.mulVec u) = (0, (e u).2)) → (∀ u, e (M.mulVec u) = (0, fun c => d c * (e u).2 c)) → E.rank = t ∧ blockPol E M = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  intro K _ n r t e E M d hE hM
  let a : Matrix (Fin n) (Fin t) K :=
    LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K (Fin r → K) (Fin t → K))
  let b : Matrix (Fin t) (Fin n) K :=
    LinearMap.toMatrix' (LinearMap.snd K (Fin r → K) (Fin t → K) ∘ₗ e.toLinearMap)
  have ha : ∀ w, a.mulVec w = e.symm (0, w) := by
    intro w
    simp [a, LinearMap.toMatrix'_mulVec]
  have hb : ∀ u, b.mulVec u = (e u).2 := by
    intro u
    simp [b, LinearMap.toMatrix'_mulVec]
  have hba : b * a = 1 := by
    apply Matrix.toLin'.injective
    ext1 w
    ext1
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb,
      LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hE' : E = a * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    rw [← hE, LinearEquiv.symm_apply_apply]
  have hM' : M = a * Matrix.diagonal d * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    apply e.injective
    rw [hM, LinearEquiv.apply_symm_apply]
    congr 1
    funext c
    rw [Matrix.mulVec_diagonal]
  rw [hE', hM']
  exact rank_blockPol_of_factor a b d hba

end GlobalTheory.CharBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqPowFrob
section
noncomputable section

namespace GlobalTheory.FrobeniusPower

open Polynomial

theorem ringHom_eq_pow_frob (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F] [CharP F p]
    (φ : F →+* F) : ∃ m : ℕ, ∀ x : F, φ x = x ^ p ^ m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →ₐ[ZMod p] F :=
    { φ with
      commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (φ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  let σ : F ≃ₐ[ZMod p] F := AlgEquiv.ofBijective ψ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ
  refine ⟨n, fun x => ?_⟩
  have h1 : σ x = φ x := rfl
  rw [← h1, ← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

theorem finite_Fq (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [NeZero a] : Finite (GlobalTheory.BKReal.Fq l a) := by
  have hq : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt
  have hp : (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f (l ^ a)) h
    simp only [coeff_sub, coeff_X_pow, coeff_X, if_true, coeff_zero, if_neg hq.ne] at h2
    simp at h2
  have hsub : ((GlobalTheory.BKReal.resSub l a : Subring (Formalism.BasicNotions.Loc.OCb l)) : Set (Formalism.BasicNotions.Loc.OCb l)) ⊆
      {x | (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]).IsRoot x} := by
    intro x hx
    have hx' : iterateFrobenius (Formalism.BasicNotions.Loc.OCb l) l a x = x := hx
    rw [iterateFrobenius_def] at hx'
    show Polynomial.eval x (X ^ (l ^ a) - X) = 0
    rw [eval_sub, eval_pow, eval_X, hx', sub_self]
  have h : Finite ↥(GlobalTheory.BKReal.resSub l a) := ((Polynomial.finite_setOf_isRoot hp).subset hsub).to_subtype
  exact h

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [inst : NeZero a]
    (φ : GlobalTheory.BKReal.Fq l a →+* GlobalTheory.BKReal.Fq l a), ∃ (m : ℕ), ∀ (x : GlobalTheory.BKReal.Fq l a),
      (φ : GlobalTheory.BKReal.Fq l a → GlobalTheory.BKReal.Fq l a) x = x ^ l ^ m := by
  intro l hl a _ φ
  haveI := finite_Fq l a
  haveI : IsDomain (GlobalTheory.BKReal.Fq l a) := inferInstanceAs (IsDomain ↥(GlobalTheory.BKReal.resSub l a))
  haveI : CharP (GlobalTheory.BKReal.Fq l a) l :=
    inferInstanceAs (CharP ↥(GlobalTheory.BKReal.resSub l a) l)
  letI : Field (GlobalTheory.BKReal.Fq l a) := (Finite.isDomain_to_isField _).toField
  exact ringHom_eq_pow_frob l (GlobalTheory.BKReal.Fq l a) φ

end GlobalTheory.FrobeniusPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormSubLtOne
section
namespace GlobalTheory.UltrametricUnitNorm

section
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_add_lt_one {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_pow_sub_one_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (i : ℕ) : ‖u ^ i - 1‖ < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
    rw [e]
    refine norm_add_lt_one ?_ h
    rwa [norm_mul, hu, one_mul]

theorem norm_geom_sub_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (n : ℕ) :
    ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact norm_add_lt_one ih (norm_pow_sub_one_lt hu h n)

omit [IsUltrametricDist K] in
theorem norm_eq_one_of_pow {x : K} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 h

theorem eq_of_norm_sub_lt {m : ℕ} (hm : 0 < m) (hn : ‖(m : K)‖ = 1) {ζ η : K} (hζ : ζ ^ m = 1)
    (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  have nζ := norm_eq_one_of_pow hm hζ
  have nη := norm_eq_one_of_pow hm hη
  have z0 : ζ ≠ 0 := by
    rintro rfl
    simp at nζ
  by_contra hne
  have hu : ‖η / ζ‖ = 1 := by rw [norm_div, nζ, nη, div_one]
  have hu1 : η / ζ - 1 = (η - ζ) / ζ := by field_simp
  have hlt : ‖η / ζ - 1‖ < 1 := by rwa [hu1, norm_div, nζ, div_one]
  have hne' : η / ζ - 1 ≠ 0 := by
    rw [hu1]
    exact div_ne_zero (sub_ne_zero.2 hne) z0
  have hs : (∑ i ∈ Finset.range m, (η / ζ) ^ i) = 0 := by
    have := geom_sum_mul (η / ζ) m
    rw [div_pow η ζ m, hη, hζ, div_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne'
  have := norm_geom_sub_lt hu hlt m
  rw [hs, zero_sub, norm_neg, hn] at this
  exact lt_irrefl _ this

end

theorem norm_natCast_eq_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hlm : ¬l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm

theorem root_eq_of_norm_sub_lt_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hm : 0 < m) (hlm : ¬l ∣ m)
    {ζ η : Formalism.BasicNotions.Loc.Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ :=
  eq_of_norm_sub_lt hm (norm_natCast_eq_one hlm) hζ hη h

end GlobalTheory.UltrametricUnitNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.StrictAdm

theorem strict_adm : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm11 D := by
  intro D l _ K LL T₀ T₁ T₂ ι π hses hc
  obtain ⟨hi, hs, -, hk, -⟩ := hses
  have hT := D.locT l
  have hsq₀ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi hc
  have hsq₂ := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs hc).1
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ hc).1
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, hk x]
  have he := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ
    ι.f π.f ι.equiv π.equiv hi hs hrk hdr
  exact ⟨hsq₀, hsq₂, fun τ a => (he.2.2 τ a).2.1⟩

end GlobalTheory.Per.StrictAdm
end

