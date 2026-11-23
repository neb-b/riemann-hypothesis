module

public import Development.EtaleCohomology.EtaleTrace.LRingPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PRingL
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

theorem ringL_holds : RingL := by
  unfold RingL
  intro hI l _
  have h11 := hI.a11
  have h6n := hI.a6nat
  have h6r := hI.a6ring
  have hone : ∀ X : Scheme.{0}, IsUnit (l : Γ(X, ⊤)) → ∀ (n : ℤ) (u : V l X n),
      cupV l X (zero_add n) (oneV l X) u = u := by
    intro X hl n u
    rw [cupV_eq l h11, oneV_eq l h11 X hl]
    have key : cupQ l h11 X (zero_add n) ((1 : ℚ_[l]) ⊗ₜ z0 l h11 X hl) = LinearMap.id := by
      apply ext1; intro x
      rw [cupQ_tmul, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (funext fun j => one_cc h6r (inv_of l X hl j) (x.1 j))
    rw [key, LinearMap.id_apply]
  have hcomm : ∀ (X : Scheme.{0}) (n m r : ℤ) (h : n + m = r) (h' : m + n = r) (u : V l X n) (v : V l X m),
      cupV l X h u v = (n * m).negOnePow • cupV l X h' v u := by
    intro X n m r h h' u v
    simp only [cupV_eq l h11]
    have key : cupQ l h11 X h = (((n * m).negOnePow : ℤˣ) : ℤ) • (cupQ l h11 X h').flip := by
      apply LateralTheory.EtaleTrace.LRingPf.ext2; intro x y
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.flip_apply, cupQ_tmul, cupQ_tmul]
      have e := map_zsmul (TensorProduct.mk ℤ_[l] ℚ_[l] (Hl l (sch.obj X) r 0) (1 : ℚ_[l]))
        (((n * m).negOnePow : ℤˣ) : ℤ) (cupL l (sch.obj X) h' h11 y x)
      simp only [TensorProduct.mk_apply] at e
      rw [← e]
      congr 1
      exact Subtype.ext (funext fun j => (comm_cc h h6r h' (x.1 j) (y.1 j)).trans rfl)
    rw [key, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
  refine ⟨fun X n m r h => ?_, fun {Y X} f n m r h u v => ?_, fun X hl => ?_, hone, fun X hl n u => ?_,
    fun {Y X} f hl => ?_, fun X n m r s t w h1 h2 h3 h4 u v z => ?_, hcomm⟩
  · rw [cupV_eq l h11]; exact isCup_cupQ l h11 X h
  · rw [cupV_eq l h11 X, cupV_eq l h11 Y]
    have key : (cupQ l h11 X h).compr₂ (pb l f r) = (cupQ l h11 Y h).compl₁₂ (pb l f n) (pb l f m) := by
      apply LateralTheory.EtaleTrace.LRingPf.ext2; intro x y
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
      rw [cupQ_tmul, pb_tmul, pb_tmul, pb_tmul, cupQ_tmul]
      congr 1
      exact Subtype.ext (funext fun j => pull_cc h h6n (sch.map f) (x.1 j) (y.1 j))
    exact LinearMap.congr_fun₂ key u v
  · exact ⟨z0 l h11 X hl, fun j => rfl, oneV_eq l h11 X hl⟩
  · rw [hcomm X n 0 n (add_zero n) (zero_add n) u (oneV l X), hone X hl n u, mul_zero,
      Int.negOnePow_zero, one_smul]
  · rw [oneV_eq l h11 X hl, oneV_eq l h11 Y (unit_pull l f hl), pb_tmul]
    congr 1
    exact Subtype.ext (funext fun j => (h6n (l ^ j)).2.1 (sch.map f) (inv_of l X hl j))
  · simp only [cupV_eq l h11]
    have key : ∀ z, (cupQ l h11 X h1).compr₂ ((cupQ l h11 X h2).flip z) =
        (cupQ l h11 X h4).compl₂ ((cupQ l h11 X h3).flip z) := by
      intro z; apply LateralTheory.EtaleTrace.LRingPf.ext2; intro x y
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.flip_apply]
      rw [cupQ_tmul]
      have k2 : cupQ l h11 X h2 ((1 : ℚ_[l]) ⊗ₜ cupL l (sch.obj X) h1 h11 x y) =
          (cupQ l h11 X h4 ((1 : ℚ_[l]) ⊗ₜ x)).comp (cupQ l h11 X h3 ((1 : ℚ_[l]) ⊗ₜ y)) := by
        apply ext1; intro w
        rw [LinearMap.comp_apply, cupQ_tmul, cupQ_tmul, cupQ_tmul]
        congr 1
        exact Subtype.ext (funext fun j => assoc_cc h6r h1 h2 h3 h4 (x.1 j) (y.1 j) (w.1 j))
      exact LinearMap.congr_fun k2 z
    exact LinearMap.congr_fun₂ (key z) u v

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTopPart
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

theorem topPart_holds : TopPart := by
  intro l _ k _ _ hl d X p hp hR hLow hKun lam s a hlam Λ hΛ δ
  classical
  have hmem : δ ∈ Submodule.span ℚ_[l]
      {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v} := by
    rw [hKun.span]
    trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', b', h', u, v, rfl⟩ := hx
    rcases lt_trichotomy b' 0 with hb | hb | hb
    · haveI := hLow.neg X b' hb
      obtain rfl : v = 0 := Subsingleton.elim _ _
      refine ⟨0, ?_, ?_⟩
      · simp [ext2]
      · simp [ext2]
    · subst hb
      obtain rfl : a' = 2 * (d : ℤ) := by omega
      let F : V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] V l (pullback p p) (2 * (d : ℤ)) :=
        (cupV l (pullback p p) h').flip (pb l (pullback.snd p p) 0 v) ∘ₗ
          pb l (pullback.fst p p) (2 * (d : ℤ))
      have hsum : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v) =
          ext2 l p h' u v := by
        calc ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v)
            = ∑ t, a.repr u t • F (a t) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              simp only [ext2, F, map_smul, LinearMap.comp_apply, LinearMap.flip_apply]
          _ = F (∑ t, a.repr u t • a t) := by
              set_option synthInstance.maxHeartbeats 100000 in
                rw [map_sum]
              simp only [map_smul]
          _ = ext2 l p h' u v := by
              rw [a.sum_repr]
              rfl
      refine ⟨fun t => a.repr u t • v, ?_, ?_⟩
      · rw [hΛ.1 u v, ← Finset.sum_smul]
        congr 1
        conv_rhs => rw [← a.sum_repr u]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul, hlam, smul_eq_mul, mul_one]
      · rw [hsum, sub_self]
        exact Submodule.zero_mem _
    · refine ⟨0, ?_, ?_⟩
      · simp only [Pi.zero_apply, Finset.sum_const_zero]
        exact (hΛ.2 a' b' h' (ne_of_gt hb) u v).symm
      · have h0 : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) ((0 : Fin s → V l X 0) t) = 0 := by
          simp [ext2]
        rw [h0, sub_zero]
        rcases le_or_gt 0 a' with ha | ha
        · exact Submodule.subset_span ⟨a', b', h', u, v, ha, hb, rfl⟩
        · haveI := hLow.neg X a' ha
          obtain rfl : u = 0 := Subsingleton.elim _ _
          simp [ext2]
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [ext2]
  | add x y _ _ hx hy =>
    obtain ⟨b1, hb1, hm1⟩ := hx
    obtain ⟨b2, hb2, hm2⟩ := hy
    refine ⟨b1 + b2, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hb1, hb2]
    · convert Submodule.add_mem _ hm1 hm2 using 1
      simp only [ext2, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
      abel
  | smul c x _ hx =>
    obtain ⟨b, hb, hm⟩ := hx
    refine ⟨c • b, ?_, ?_⟩
    · simp [← Finset.smul_sum, hb]
    · convert Submodule.smul_mem _ c hm using 1
      simp only [ext2, Pi.smul_apply, map_smul, smul_sub, Finset.smul_sum]

end UpperTheory.Gal.KunnethLefschetz
end
end

