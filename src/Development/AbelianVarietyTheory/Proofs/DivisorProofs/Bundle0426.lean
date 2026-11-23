module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafPresheafOverCoproductEqSum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeCofan

theorem pieces {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) :
    (∀ i, IsOpenImmersion (j i)) ∧ (∀ u : U, ∃ i, ∃ v : V i, j i v = u) ∧
      (∀ i k (v : V i) (w : V k), j i v = j k w → i = k) := by
  let e : ∐ V ≅ U := (colimit.isColimit (Discrete.functor V)).coconePointUniqueUpToIso hc
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (colimit.isColimit (Discrete.functor V)).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hinv : ∀ u : U, e.hom (e.inv u) = u := fun u => by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have hinv' : ∀ z : (∐ V : Scheme.{0}), e.inv (e.hom z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
  refine ⟨fun i => ?_, fun u => ?_, fun i k v w h => ?_⟩
  · rw [← he i]; infer_instance
  · obtain ⟨⟨i, v⟩, hv⟩ := (sigmaMk V).surjective (e.inv u)
    refine ⟨i, v, ?_⟩
    rw [← he i, Scheme.Hom.comp_apply, ← sigmaMk_mk, hv, hinv]
  · rw [← he i, ← he k, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    have h2 := congrArg e.inv h
    rw [hinv', hinv'] at h2
    exact congrArg Sigma.fst ((sigmaι_eq_iff V i k v w).1 h2)

theorem pullback_isColimit {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) {T : Scheme.{0}} (y : T ⟶ U) :
    Nonempty (IsColimit (Cofan.mk T (fun i => pullback.fst y (j i)))) := by
  obtain ⟨ho, hcov, hdis⟩ := pieces j hc
  refine nonempty_isColimit_cofanMk_of _ ?_ ?_
  · rw [eq_top_iff]
    rintro z -
    obtain ⟨i, v, hv⟩ := hcov (y z)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := j i) z v hv.symm
    exact (TopologicalSpace.Opens.mem_iSup (s := fun i => (pullback.fst y (j i)).opensRange)).2 ⟨i, w, hw⟩
  · intro i k hik
    rw [Function.onFun, disjoint_iff, eq_bot_iff]
    rintro z ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    apply hik
    refine hdis i k (pullback.snd y (j i) p) (pullback.snd y (j k) q) ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, ← pullback.condition,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    change y ((pullback.fst y (j i)) p) = y ((pullback.fst y (j k)) q)
    rw [hp, hq]

theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (G : Shv R) (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton (Sec G W) := by
  haveI : ∀ e : PEmpty.{1}, IsOpenImmersion (PEmpty.elim e : (PEmpty.elim e : Scheme.{0}) ⟶ W) :=
    fun e => e.elim
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (X := fun e : PEmpty.{1} => (PEmpty.elim e : Scheme.{0})) (S := W)
    (fun e => PEmpty.elim e) (by rw [eq_top_iff]; rintro z -; exact isEmptyElim z) (fun e => PEmpty.elim e)
  have hb := GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G W PEmpty.{1} _ _ hc
  exact ⟨fun x y => hb.1 (funext fun e => PEmpty.elim e)⟩

end GlobalTheory.EtC.FreeCofan

namespace GlobalTheory.EtC.FreeCofan

theorem res_res {R : Type} [CommRing R] {G : Shv R} {W W' T : Scheme.{0}} (g : W ⟶ W') (f : W' ⟶ T)
    (z : Sec G T) : Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem main : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ (P : PSh) (t : P ⟶ yoneda.obj U) (Q : ι → PSh) (a : ∀ i, Q i ⟶ P) (b : ∀ i, Q i ⟶ yoneda.obj (V i)), (∀ i, IsPullback (a i) (b i) t (yoneda.map (j i))) → Nonempty (IsColimit (Cofan.mk ((free R).obj P) (fun i ↦ (free R).map (a i)))) := by
  intro R _ U ι V j hc P t Q a b hpb
  obtain ⟨ho, -, hdis⟩ := pieces j hc
  have FH := fun (P' : PSh) (G : Shv R) => GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R P' G
  let y : ∀ T : Scheme.{0}, P.obj (op T) → (T ⟶ U) := fun T x => t.app (op T) x
  have hy : ∀ (T T' : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)), y T' (P.map g.op x) = g ≫ y T x :=
    fun T T' g x => NatTrans.naturality_apply t g.op x
  have hw : ∀ i (W : Scheme.{0}) (q0 : (Q i).obj (op W)), y W ((a i).app _ q0) = ((b i).app _ q0 : W ⟶ V i) ≫ j i :=
    fun i W q0 => ConcreteCategory.congr_hom (congr_app (hpb i).w (op W)) q0
  have hcol : ∀ (T : Scheme.{0}) (x : P.obj (op T)), IsColimit (Cofan.mk T (fun i => pullback.fst (y T x) (j i))) :=
    fun T x => (pullback_isColimit j hc (y T x)).some
  have SC := fun (G : Shv R) (T : Scheme.{0}) (x : P.obj (op T)) => GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G T ι _ _ (hcol T x)
  have hex : ∀ i (W : Scheme.{0}) (x : P.obj (op W)) (σ : W ⟶ V i), y W x = σ ≫ j i →
      ∃ q : (Q i).obj (op W), (a i).app _ q = x ∧ (b i).app _ q = σ := fun i W x σ h =>
    Types.exists_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) x σ h
  have huq : ∀ i (W : Scheme.{0}) (q q' : (Q i).obj (op W)), (a i).app _ q = (a i).app _ q' →
      (b i).app _ q = (b i).app _ q' → q = q' := fun i W q q' h1 h2 =>
    Types.ext_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) h1 h2
  have hq : ∀ (T : Scheme.{0}) (x : P.obj (op T)) i, ∃ q : (Q i).obj (op (pullback (y T x) (j i))),
      (a i).app _ q = P.map (pullback.fst (y T x) (j i)).op x ∧ (b i).app _ q = pullback.snd (y T x) (j i) :=
    fun T x i => hex i _ _ _ (by rw [hy]; exact pullback.condition)
  choose q hqa hqb using hq
  have key : ∀ (G : Shv R) (m : (free R).obj P ⟶ G) T x i,
      Sec.res (pullback.fst (y T x) (j i)) (val m T x) = val ((free R).map (a i) ≫ m) _ (q T x i) := by
    intro G m T x i
    rw [(FH P G).2.2.2.1 (Q i) (a i) m, hqa, (FH P G).2.2.1 m]
  let φ : ∀ (G : Shv R) (c : ∀ i, (free R).obj (Q i) ⟶ G) (T : Scheme.{0}), P.obj (op T) → Sec G T :=
    fun G c T x => Function.surjInv (SC G T x).2 (fun i => val (c i) _ (q T x i))
  have hφ : ∀ G c T x i, Sec.res (pullback.fst (y T x) (j i)) (φ G c T x) = val (c i) _ (q T x i) :=
    fun G c T x i => congrFun (Function.surjInv_eq (SC G T x).2 _) i
  have nat : ∀ G c (T' T : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)),
      φ G c T' (P.map g.op x) = Sec.res g (φ G c T x) := by
    intro G c T' T g x
    apply (SC G T' (P.map g.op x)).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, res_res]
    have hw2 : (pullback.fst (y T' (P.map g.op x)) (j i) ≫ g) ≫ y T x = pullback.snd _ (j i) ≫ j i := by
      rw [Category.assoc, ← hy, pullback.condition]
    have h1 : pullback.lift _ _ hw2 ≫ pullback.fst (y T x) (j i) = pullback.fst (y T' (P.map g.op x)) (j i) ≫ g :=
      pullback.lift_fst _ _ _
    have h2 : pullback.lift _ _ hw2 ≫ pullback.snd (y T x) (j i) = pullback.snd (y T' (P.map g.op x)) (j i) :=
      pullback.lift_snd _ _ _
    rw [← h1, ← res_res, hφ, ← (FH (Q i) G).2.2.1 (c i)]
    congr 1
    apply huq
    · rw [hqa, NatTrans.naturality_apply, hqa, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, h1]
    · rw [hqb, NatTrans.naturality_apply, hqb]
      exact h2.symm
  let d : ∀ s : Cofan (fun i => (free R).obj (Q i)), (free R).obj P ⟶ s.pt := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose
  have hd : ∀ s T x, val (d s) T x = φ s.pt s.inj T x := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose_spec
  refine ⟨mkCofanColimit _ d ?_ ?_⟩
  · intro s i
    change (free R).map (a i) ≫ d s = s.inj i
    apply (FH (Q i) s.pt).1
    intro W q0
    rw [(FH P s.pt).2.2.2.1 (Q i) (a i), hd]
    obtain ⟨x, hx⟩ : ∃ x, x = (a i).app (op W) q0 := ⟨_, rfl⟩
    have hwx : y W x = ((b i).app _ q0 : W ⟶ V i) ≫ j i := hx ▸ hw i W q0
    rw [← hx]
    apply (SC s.pt W x).1
    refine funext fun k => ?_
    dsimp only
    rw [hφ, ← (FH (Q i) s.pt).2.2.1]
    by_cases hki : k = i
    · subst hki
      congr 1
      apply huq
      · rw [hqa, NatTrans.naturality_apply, ← hx]
      · rw [hqb, NatTrans.naturality_apply]
        change _ = pullback.fst (y W x) (j k) ≫ ((b k).app _ q0 : W ⟶ V k)
        haveI := ho k
        rw [← cancel_mono (j k), Category.assoc, ← pullback.condition, hwx]
    · haveI : IsEmpty ((pullback (y W x) (j k) : Scheme.{0}) : Type) := by
        refine ⟨fun z => hki (hdis k i (pullback.snd (y W x) (j k) z)
          ((pullback.fst (y W x) (j k) ≫ ((b i).app _ q0 : W ⟶ V i)) z) ?_)⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, Category.assoc, ← hwx]
      exact (sec_subsingleton_of_isEmpty s.pt _).elim _ _
  · intro s m hm
    have hm' : ∀ i, (free R).map (a i) ≫ m = s.inj i := hm
    apply (FH P s.pt).1
    intro T x
    rw [hd]
    apply (SC s.pt T x).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, key, hm']

end GlobalTheory.EtC.FreeCofan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtension
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.PullAd

section
variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] {n : ℕ}

theorem val_eq_one_iff {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ))) {z : K}
    (hz : z ≠ 0) : w z = 1 ↔ w z ≤ 1 ∧ w z⁻¹ ≤ 1 := by
  constructor
  · intro h; simp [map_inv₀, h]
  · rintro ⟨h1, h2⟩
    rw [map_inv₀] at h2
    have h0 : w z ≠ 0 := (Valuation.ne_zero_iff w).2 hz
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = w z * (w z)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ w z * 1 := mul_le_mul_right h2 _
      _ = w z := mul_one _

theorem res_eq_one {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x : F} (hx : x ≠ 0) :
    p.1 (algebraMap F E x) = 1 ↔ (ρ p).1 x = 1 := by
  rw [val_eq_one_iff _ hx, val_eq_one_iff _ ((map_ne_zero _).2 hx), ← map_inv₀, hρ, hρ]

theorem res_mono {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E) {x y : F}
    (h : (ρ p).1 x ≤ (ρ p).1 y) : p.1 (algebraMap F E x) ≤ p.1 (algebraMap F E y) := by
  by_cases hy : y = 0
  · subst hy
    have h0 : (ρ p).1 x = 0 := le_antisymm (by simpa using h) zero_le'
    have hx : x = 0 := (Valuation.zero_iff _).1 h0
    simp [hx]
  · have h1 : (ρ p).1 (x * y⁻¹) ≤ 1 := by
      have h0 : (ρ p).1 y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
      rw [map_mul, map_inv₀]
      calc (ρ p).1 x * ((ρ p).1 y)⁻¹ ≤ (ρ p).1 y * ((ρ p).1 y)⁻¹ := mul_le_mul_left h _
        _ = 1 := mul_inv_cancel₀ h0
    have h2 := (hρ p (x * y⁻¹)).2 h1
    have e : algebraMap F E x = algebraMap F E (x * y⁻¹) * algebraMap F E y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy]
    rw [e, map_mul]
    exact mul_le_of_le_one_left' h2

theorem det_map (M : Matrix (Fin n) (Fin n) F) :
    (M.map (algebraMap F E)).det = algebraMap F E M.det := by
  rw [RingHom.map_det]; rfl

theorem unimod_map {ρ : Place k E → Place k F} (hρ : IsRes ρ) (p : Place k E)
    (M : Matrix (Fin n) (Fin n) F) (hM : M.det ≠ 0) :
    Unimod p (M.map (algebraMap F E)) ↔ Unimod (ρ p) M := by
  unfold Unimod
  rw [det_map, res_eq_one hρ p hM]
  simp only [Matrix.map_apply]
  exact and_congr_left fun _ => forall_congr' fun i => forall_congr' fun j => hρ p _

theorem nrm_of_max (v : Place k F) (x : Fin n → F) (i : Fin n) (h : ∀ j, v.1 (x j) ≤ v.1 (x i)) :
    nrm v x = v.1 (x i) :=
  le_antisymm (Finset.sup_le fun j _ => h j) (Finset.le_sup (f := fun j => v.1 (x j)) (Finset.mem_univ i))

end

theorem adm_pullAd_and_deg_mul_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → admitted (pullAd ρ g) ∧ deg (pullAd ρ g) = Module.finrank F E * deg g ∧ (∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i)) = Module.finrank F E * degLine g w) ∧ ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hFF ρ hρ n g hg
  have hP := _root_.GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul k F E hFF ρ hρ
  have hdet : ∀ p, (pullAd ρ g p).det = algebraMap F E (g (ρ p)).det := fun p => det_map _
  have hadm : admitted (pullAd ρ g) := by
    refine ⟨fun p => by rw [hdet]; exact (map_ne_zero _).2 (hg.1 _), ?_⟩
    refine (hP.1 _ hg.2).subset fun p hp => ?_
    exact fun h => hp ((unimod_map hρ p (g (ρ p)) (hg.1 _)).2 h)
  have hdeg : deg (pullAd ρ g) = Module.finrank F E * deg g := by
    have hfin : {v | ord v (g v).det ≠ 0}.Finite := hg.2.subset fun v hv hu => hv (by simp [ord, hu.2])
    unfold deg
    rw [← hP.2 (fun v => (g v).det) hfin]
    exact finsum_congr fun p => by rw [hdet]
  have hline : ∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i))
      = Module.finrank F E * degLine g w := by
    intro w hw
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      obtain ⟨i, -⟩ := Function.ne_iff.1 hw; exact ⟨i, Finset.mem_univ _⟩
    have hmax : ∀ v : Place k F, ∃ i, ∀ j, v.1 ((g v).mulVec w j) ≤ v.1 ((g v).mulVec w i) := fun v => by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => v.1 ((g v).mulVec w i)) hne
      exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
    choose idx hidx using hmax
    let φ : Place k F → F := fun v => (g v).mulVec w (idx v)
    have hvo : ∀ v, ordVec v ((g v).mulVec w) = ord v (φ v) := fun v => by
      simp only [ordVec, ord, φ, nrm_of_max v _ _ (hidx v)]
    have hpo : ∀ p, ordVec p ((pullAd ρ g p).mulVec (fun i => algebraMap F E (w i)))
        = ord p (algebraMap F E (φ (ρ p))) := fun p => by
      have e : (pullAd ρ g p).mulVec (fun i => algebraMap F E (w i))
          = fun i => algebraMap F E ((g (ρ p)).mulVec w i) := by
        funext i; exact (RingHom.map_mulVec _ _ _ _).symm
      rw [e]
      simp only [ordVec, ord, φ]
      rw [nrm_of_max p _ (idx (ρ p)) fun j => res_mono hρ p (hidx (ρ p) j)]
    have hfin : {v | ord v (φ v) ≠ 0}.Finite := by
      have hS : ({v | ¬ Unimod v (g v)} ∪ ⋃ i, {v : Place k F | w i ≠ 0 ∧ v.1 (w i) ≠ 1}).Finite := by
        refine hg.2.union (Set.finite_iUnion fun i => ?_)
        by_cases hi : w i = 0
        · simp [hi]
        · exact (_root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hFF (w i) hi).1.subset fun v hv => hv.2
      refine hS.subset fun v hv => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_and,
        not_not] at hc
      obtain ⟨hu, hw1⟩ := hc
      apply hv
      rw [← hvo v]
      have h1 : nrm v w = 1 := by
        obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
        replace hi0 : w i0 ≠ 0 := hi0
        apply le_antisymm
        · refine Finset.sup_le fun j _ => ?_
          by_cases hj : w j = 0
          · simp [hj]
          · exact (hw1 j hj).le
        · rw [← hw1 i0 hi0]; exact Finset.le_sup (f := fun j => v.1 (w j)) (Finset.mem_univ i0)
      simp only [ordVec]
      rw [(_root_.GlobalTheory.Nef.ord_calculus k F v).2.2.2.2.2.2.2.2.1 n (g v) w hu, h1]
      simp
    unfold degLine
    rw [finsum_congr hpo, hP.2 φ hfin, finsum_congr hvo]
  have hlines : ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
    intro b hb E' _ _ _ _ _ ρ' hρ' w hw
    letI : Algebra F E' := ((algebraMap E E').comp (algebraMap F E)).toAlgebra
    haveI : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower k F E' := IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k F E,
        ← IsScalarTower.algebraMap_apply k E E']
    haveI : FiniteDimensional F E' := Module.Finite.trans E E'
    have hres : IsRes (fun p => ρ (ρ' p)) := fun p x => (hρ' p (algebraMap F E x)).trans (hρ (ρ' p) x)
    have heq : pullAd ρ' (pullAd ρ g) = pullAd (fun p => ρ (ρ' p)) g := by
      funext p; ext i j; rfl
    have hb' := hb E' (fun p => ρ (ρ' p)) hres w hw
    rw [heq]
    calc (degLine (pullAd (fun p => ρ (ρ' p)) g) w : ℝ) ≤ b * Module.finrank F E' := hb'
      _ = b * Module.finrank F E * Module.finrank E E' := by
        rw [← Module.finrank_mul_finrank F E E']; push_cast; ring
  exact ⟨hadm, hdeg, hline, hlines⟩

end GlobalTheory.Nef.PullAd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def extMap {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R] →ₐ[R] TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R] :=
  { semiDiag (semiHom_mp F φ) with
    commutes' := fun r ↦ by
      change semiDiag (semiHom_mp F φ) (algebraMap R _ r) = algebraMap R _ r
      ext
      · rw [fst_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl', (semiHom_mp F φ).map_algebraMap]
      · rw [snd_semiDiag]; simp [TrivSqZeroExt.algebraMap_eq_inl'] }

theorem fst_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).fst = mp F φ c.fst := fst_semiDiag _ c

theorem snd_extMap {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) :
    (extMap F φ c).snd = p1 F φ c.snd := snd_semiDiag _ c

def omExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
  map φ := CommAlgCat.ofHom (extMap F φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans (mp_id F T _)) ((snd_extMap F _ c).trans (oneFormsMapOfFunctorMorphism_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMap F _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).fst
      rw [fst_extMap, fst_extMap])))
    ((snd_extMap F _ c).trans ((oneFormsMapOfFunctorMorphism_comp F φ ψ _).trans (by
      change _ = ((extMap F ψ) (extMap F φ c)).snd
      rw [snd_extMap, snd_extMap]))))

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem isLocalization_of_data {T T' : C} (l : T ⟶ T') (b : F.obj T) (h1 : IsUnit (mp F l b))
    (h2 : ∀ y : F.obj T', ∃ (n : ℕ) (x : F.obj T), y * mp F l b ^ n = mp F l x)
    (h3 : ∀ x : F.obj T, mp F l x = 0 → ∃ n : ℕ, b ^ n * x = 0) :
    letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
    IsLocalization.Away b (F.obj T') := by
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  refine ⟨?_, fun z ↦ ?_, fun {x y} e ↦ ?_⟩
  · rintro ⟨_, n, rfl⟩
    change IsUnit (mp F l (b ^ n))
    rw [map_pow]; exact h1.pow n
  · obtain ⟨n, x, e⟩ := h2 z
    refine ⟨(x, ⟨b ^ n, n, rfl⟩), ?_⟩
    change z * mp F l (b ^ n) = mp F l x
    rw [map_pow]; exact e
  · obtain ⟨n, hn⟩ := h3 (x - y) (by rw [map_sub]; exact sub_eq_zero.2 e)
    exact ⟨⟨b ^ n, n, rfl⟩, sub_eq_zero.1 (by rw [← mul_sub]; exact hn)⟩

theorem isUnit_mp_omExt_iff {T S : C} (u : T ⟶ S) (c : (omExt F).obj T) :
    IsUnit (mp (omExt F) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMap F u c)))

theorem surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
    (y : TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R]) (a₀ : F.obj T) (η₀ : Ω[F.obj T⁄R]) (k₁ k₂ : ℕ)
    (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀) (hη : mp F l (c.fst ^ k₂) • y.snd = p1 F l η₀) :
    y * extMap F l c ^ (k₁ + k₂ + 1) = extMap F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMap, fst_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMap, fst_extMap, snd_extMap]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      oneFormsMapOfFunctorMorphism_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_key {T : C} (c x : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R]) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_omExt (H : Desc.HasLoc F) : Desc.HasLoc (omExt F) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := isLocalization_of_data F l c.fst h1 h2 h3
  have hp : ∀ ω, p1 F l ω = KaehlerDifferential.map R R (F.obj T) (F.obj T') ω :=
    SemiHom.oneFormMap_eq_kaehlerDifferential_map _ fun _ ↦ rfl
  have hs : ∀ (a : F.obj T) (η : Ω[F.obj T'⁄R]), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omExt_iff F l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omExt_iff F u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (KaehlerDifferential.map R R (F.obj T) (F.obj T')) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_key F l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMap F l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : KaehlerDifferential.map R R (F.obj T) (F.obj T') x.snd = 0 :=
      (hp _).symm.trans ((snd_extMap F l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := KaehlerDifferential.map R R (F.obj T) (F.obj T')) (x₁ := x.snd) (x₂ := 0)
      (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_key F c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExt

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem span_inl_eq_top {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omExt F).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) Ω[F.obj S⁄R])) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

theorem glue_one_forms : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], [Quiver.IsThin C'] → ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : AffOp X'), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : AffOp X') (s : ∀ t, (T ⟶ G.obj t) → Ω[(OAff s').obj (G.obj t)⁄R']), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 (OAff s') (G.map a) (s t u)) → ∃ ω : Ω[(OAff s').obj T⁄R'], ∀ t u, p1 (OAff s') u ω = s t u) := by
  intro R' _ X' s' C' _ _ G hcov hdir T s hs
  have unit : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) G (hasLoc_omExt (OAff s') (hasLoc_OAff s'))
    (fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unit u _ hu)⟩)
    (fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unit u _ hu)⟩)
    T (fun t u ↦ TrivSqZeroExt.inr (s t u)) (fun t t' u a ↦ by
      apply TrivSqZeroExt.ext
      · exact (TrivSqZeroExt.fst_inr _ _).trans (((fst_extMap (OAff s') (G.map a) _).trans
          (by rw [TrivSqZeroExt.fst_inr, map_zero])).symm)
      · exact ((TrivSqZeroExt.snd_inr _ _).trans (hs t t' u a)).trans
          ((snd_extMap (OAff s') (G.map a) _).trans (by rw [TrivSqZeroExt.snd_inr])).symm)
  exact ⟨x.snd, fun t u ↦ (snd_extMap (OAff s') u x).symm.trans
    ((congrArg TrivSqZeroExt.snd (hx t u)).trans (TrivSqZeroExt.snd_inr _ _))⟩

end GlobalTheory.CechDR.FormExt
end
end

