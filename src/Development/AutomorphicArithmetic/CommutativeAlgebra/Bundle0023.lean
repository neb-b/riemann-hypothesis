module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem pull_bij (q : ℕ) {A B : Spc} (f : A ⟶ B) [IsIso f] (n i : ℤ) :
    Function.Bijective (fun x : Ht q B n i => (pull _ f _ _ x : Ht q A n i)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun y => pull _ (inv f) _ _ y, fun x => ?_, fun y => ?_⟩
  · show pull _ (inv f) _ _ (pull _ f _ _ x) = x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · show pull _ f _ _ (pull _ (inv f) _ _ y) = y
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem pull_cup (q : ℕ) {A B : Spc} (f : A ⟶ B) {n m i j : ℤ} (a : Ht q B n i) (b : Ht q B m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem pull_cast' (q : ℕ) {A B : Spc} (f : A ⟶ B) {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q B n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q A n i) := by
  subst hn; subst hi; rfl

theorem UpperTheory.lerayHirsch_of_iso_square :
    ∀ (q : ℕ) [NeZero q] {X X' E E' : Spc} (π : X ⟶ E) (π' : X' ⟶ E') (u : X' ⟶ X) (b : E' ⟶ E) [IsIso u] [IsIso b], u ≫ π = π' ≫ b →
        ∀ {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)), LH q π d e c → LH q π' d e (fun j => pull _ u _ _ (c j)) := by
  intro q _ X X' E E' π π' u b _ _ w m d e c h n i
  have hP : Function.Bijective (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
      (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) :=
    ⟨fun a a' haa => funext fun j => (pull_bij q b _ _).1 (congrFun haa j),
      fun y => ⟨fun j => ((pull_bij q b _ _).2 (y j)).choose,
        funext fun j => ((pull_bij q b _ _).2 (y j)).choose_spec⟩⟩
  have hc : ∀ a : ∀ j, Ht q E (n - d j) (i - e j),
      (∑ j, ((cup q (pull _ π' _ _ (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) (pull _ u _ _ (c j))).cast
        (by ring) (by ring) : Ht q X' n i)) =
      pull _ u _ _ (∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast', pull_cup, ← pull_comp, ← pull_comp, w]
  have hcomp := (pull_bij q u n i).comp (h n i)
  have heq : (fun y : ∀ j, Ht q E' (n - d j) (i - e j) =>
      ∑ j, ((cup q (pull _ π' _ _ (y j)) (pull _ u _ _ (c j))).cast (by ring) (by ring) : Ht q X' n i)) ∘
      (fun (a : ∀ j, Ht q E (n - d j) (i - e j)) j =>
        (pull _ b _ _ (a j) : Ht q E' (n - d j) (i - e j))) =
      (fun x : Ht q X n i => (pull _ u _ _ x : Ht q X' n i)) ∘ (fun a : ∀ j, Ht q E (n - d j) (i - e j) =>
        ∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)) :=
    funext hc
  rw [← heq] at hcomp
  exact (Function.Bijective.of_comp_iff _ hP).1 hcomp
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingCupPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.MvLin

variable {R : Type} [CommRing R]

private noncomputable abbrev pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n) :
    Cochain ((chains R).obj E') I n :=
  (Cochain.ofHom ((chains R).map π)).comp a (zero_add n)

private noncomputable abbrev pbz {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cocycle ((chains R).obj E) I n) :
    Cocycle ((chains R).obj E') I n :=
  zcomp (Cocycle.ofHom ((chains R).map π)) a (zero_add n)

private theorem pb_comp {E'' E' E : Spc} (π : E'' ⟶ E') (ρ : E' ⟶ E) {I : Cx R} {n : ℤ}
    (a : Cochain ((chains R).obj E) I n) : pb (π ≫ ρ) a = pb π (pb ρ a) := by
  simp only [pb, Functor.map_comp]
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (zero_add n)

private theorem sub_map {E' E : Spc} (π : E' ⟶ E) {N : ℕ} {U : Scheme.{0}} (x : Sx E' N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map π).sub j l h = (x.sub j l h).map π :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (π.naturality (SimplexCategory.subinterval j l h).op) (op U)) x).symm

private theorem ev_pb {E' E : Spc} (π : E' ⟶ E) {I : Cx R} {n : ℤ} (a : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E' p U) :
    ev (pb π a) p s h U x = ev a p s h U (x.map π) := by
  have hp := CupSpec.ev_pull π a p s h U x
  exact hp

private theorem aw_pb {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) : μ.IsAW hk (pb π a) (pb π b) (pb π c) := by
  intro N w hw U x
  rw [ev_pb, h N w hw U (x.map π)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pb, ev_pb, sub_map, sub_map]

private theorem aw_unique {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m} {c c' : Cochain ((chains R).obj E) K k}
    (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b c') : c = c' :=
  ((GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a b).unique h h'

private theorem aw_zero {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (a : Cochain ((chains R).obj E) I n) : μ.IsAW hk a (0 : Cochain ((chains R).obj E) J m) 0 := by
  obtain ⟨z, hz, -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).1 a (0 : Cochain ((chains R).obj E) J m)
  have h2 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ hk).2.2 a 0 0 z z hz hz
  rw [add_zero] at h2
  have h3 : z + z = z := aw_unique μ hk h2 hz
  have h4 : z = 0 := by simpa using h3
  exact h4 ▸ hz

private theorem aw_delta {I J K : Cx R} (μ : Pair I J K) {E' E : Spc} (π : E' ⟶ E) {n m : ℤ}
    {a : Cochain ((chains R).obj E') I n} {z : Cocycle ((chains R).obj E) I (n + 1)} {η : Cocycle ((chains R).obj E) J m}
    {a' : Cochain ((chains R).obj E') K (n + m)} {z' : Cochain ((chains R).obj E) K (n + m + 1)}
    (hk : n + 1 + m = n + m + 1) (ha : δ n (n + 1) a = pb π z.1) (h1 : μ.IsAW rfl a (pbz π η).1 a')
    (h2 : μ.IsAW hk z.1 η.1 z') : δ (n + m) (n + m + 1) a' = pb π z' := by
  have h3 : μ.IsAW hk (δ n (n + 1) a) (pbz π η).1 (pb π z') := ha ▸ aw_pb μ π hk h2
  have h4 : μ.IsAW (by omega : n + (m + 1) = n + m + 1) a (δ m (m + 1) (pbz π η).1) 0 := by
    rw [Cocycle.δ_eq_zero]
    exact aw_zero μ _ a
  have h5 := _root_.GlobalTheory.EtC.aw_leibniz_rule R μ rfl a (pbz π η).1 a' (pb π z') 0 h1 h3 h4
  simpa using h5

private theorem mv_core {I J K : Cx R} (μ : Pair I J K) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) {n m : ℤ}
    (γ : Cocycle ((chains R).obj (pullback f g)) I n) (ζ : Cocycle ((chains R).obj E) I (n + 1))
    (α : Cochain ((chains R).obj U) I n) (β : Cochain ((chains R).obj V) I n)
    (η : Cocycle ((chains R).obj E) J m)
    (hγ : pb (pullback.fst f g) α - pb (pullback.snd f g) β = γ.1)
    (hα : δ n (n + 1) α = pb f ζ.1) (hβ : δ n (n + 1) β = pb g ζ.1) (hk : n + 1 + m = n + m + 1) :
    ∃ (γ' : Cocycle ((chains R).obj (pullback f g)) K (n + m)) (ζ' : Cocycle ((chains R).obj E) K (n + m + 1))
      (α' : Cochain ((chains R).obj U) K (n + m)) (β' : Cochain ((chains R).obj V) K (n + m)),
      μ.IsAW rfl γ.1 (pbz (pullback.fst f g ≫ f) η).1 γ'.1 ∧ μ.IsAW hk ζ.1 η.1 ζ'.1 ∧
      pb (pullback.fst f g) α' - pb (pullback.snd f g) β' = γ'.1 ∧
      δ (n + m) (n + m + 1) α' = pb f ζ'.1 ∧ δ (n + m) (n + m + 1) β' = pb g ζ'.1 := by
  obtain ⟨γ', hγ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ rfl).1 γ (pbz (pullback.fst f g ≫ f) η)
  obtain ⟨ζ', hζ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 ζ η
  obtain ⟨α', hα', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 α (pbz f η).1
  obtain ⟨β', hβ', -⟩ := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).1 β (pbz g η).1
  refine ⟨γ', ζ', α', β', hγ', hζ', ?_, aw_delta μ f hk hα hα' hζ', aw_delta μ g hk hβ hβ' hζ'⟩
  have e1 : pb (pullback.fst f g) (pbz f η).1 = (pbz (pullback.fst f g ≫ f) η).1 := (pb_comp _ _ _).symm
  have e2 : pb (pullback.snd f g) (pbz g η).1 = (pbz (pullback.fst f g ≫ f) η).1 :=
    (pb_comp _ _ _).symm.trans (by rw [pullback.condition]; rfl)
  have a1 := aw_pb μ (pullback.fst f g) rfl hα'
  have a2 := aw_pb μ (pullback.snd f g) rfl hβ'
  rw [e1] at a1
  rw [e2] at a2
  have a3 := (GlobalTheory.T.isAW_existsUnique_biadditive_etale R μ rfl).2.1 _ _ _ _ _ hγ' a2
  have e3 : γ.1 + pb (pullback.snd f g) β = pb (pullback.fst f g) α := by rw [← hγ, sub_add_cancel]
  rw [e3] at a3
  have e4 := aw_unique μ rfl a1 a3
  rw [e4, add_sub_cancel_right]

private theorem cast_cup (q : ℕ) {E : Spc} {n m k i j : ℤ} (hk : n + m = k) (a : Ht q E n i) (b : Ht q E m j) :
    (cup q a b).cast hk rfl = (twPair q i j).cup E hk a b := by
  subst hk
  rfl

end UpperTheory.MvLin

open UpperTheory.MvLin in
theorem UpperTheory.mayerVietorisConnecting_cup_pullback :
    ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g → ∀ (n m i j : ℤ) (c : Ht q (pullback f g) n i)
        (x : Ht q E (n + 1) i) (y : Ht q E m j), IsMVd f g (tw q i) n c x →
        IsMVd f g (tw q (i + j)) (n + m) (cup q c (pull _ (pullback.fst f g ≫ f) _ _ y)) ((cup q x y).cast (by ring) rfl) := by
  intro q _ U V E f g _ n m i j c x y h
  obtain ⟨γ, ζ, α, β, rfl, rfl, hγ, hα, hβ⟩ := h
  obtain ⟨η, rfl⟩ := y.mk_surjective
  have hk : n + 1 + m = n + m + 1 := by ring
  obtain ⟨γ', ζ', α', β', h1, h2, h3, h4, h5⟩ := mv_core (twPair q i j) f g γ ζ α β η hγ hα hβ hk
  refine ⟨γ', ζ', α', β', ?_, ?_, h3, h4, h5⟩
  · exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) rfl).2 γ _ γ' h1).symm
  · rw [cast_cup q hk]
    exact ((GlobalTheory.T.cup_eq_class_of_isAW _ (twPair q i j) hk).2 ζ η ζ' h2).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MemPullbackImageIffFactorsThroughOpen
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private noncomputable abbrev evF (p : ℕ) (W : Scheme.{0}) : Spc ⥤ Type :=
  ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk p))) ⋙
    ((evaluation Scheme.{0}ᵒᵖ Type).obj (op W))

theorem UpperTheory.mem_pullbackImage_iff_factors_through_open :
    ∀ {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (p : ℕ) (W : Scheme.{0}) (z : Sx E p W), ((Sub.img (E := E) (pullback.fst π (sch.map U.ι))).mem p W z ↔ ∃ w : W ⟶ U.toScheme, w ≫ U.ι = under π z) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ W), under π (z.res g) = g ≫ under π z) ∧ ∀ (r : ℕ) (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk p), under π (z.along θ) = under π z := by
  intro X U E π p W z
  have hpb : IsPullback ((evF p W).map (pullback.fst π (sch.map U.ι)))
      ((evF p W).map (pullback.snd π (sch.map U.ι))) ((evF p W).map π)
      ((evF p W).map (sch.map U.ι)) := (IsPullback.of_hasPullback π (sch.map U.ι)).map (evF p W)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(evF p W).map (pullback.snd π (sch.map U.ι)) y, ?_⟩
    exact (ConcreteCategory.congr_hom hpb.w y).symm
  · rintro ⟨w, hw⟩
    obtain ⟨y, hy, -⟩ := Types.exists_of_isPullback hpb z (show Sx (sch.obj U.toScheme) p W from w) hw.symm
    exact ⟨y, hy⟩
  · intro V g
    exact ConcreteCategory.congr_hom ((π.app (op (SimplexCategory.mk p))).naturality g.op) z
  · intro r θ
    exact congrFun (congrArg (fun t => t.app (op W)) (π.naturality θ.op)) z
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (T : Scheme.{0}) [IsEmpty T] (a : Sec F T) : a = 0 :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F T).1 a 0 ⟨⊥, Scheme.bot_mem_grothendieckTopology T, fun _ _ h => h.elim⟩

private theorem free_sec_zero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) (U : Scheme.{0})
    (y : Sec ((free R).obj P) U) : y = 0 := by
  obtain ⟨S, hS, h⟩ := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 y
  refine (_root_.GlobalTheory.EtC.sec_ext_glue R _ U).1 y 0 ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨c, hc⟩ := h V g hg
  have h0 : Sec.res g (0 : Sec ((free R).obj P) U) = 0 := map_zero (((free R).obj P).obj.map g.op).hom
  rw [h0]
  by_cases hV : IsEmpty V
  · exact sec_empty _ _ _
  · rw [hc]
    have : IsEmpty (P.obj (op V)) := ⟨fun x => hV (hP V ⟨x⟩)⟩
    have hc0 : c = 0 := Subsingleton.elim _ _
    simp [hc0]

private theorem free_isZero (R : Type) [CommRing R] (P : PSh)
    (hP : ∀ T : Scheme.{0}, Nonempty (P.obj (op T)) → IsEmpty T) : IsZero ((free R).obj P) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext U y
  exact free_sec_zero R P hP U.unop y

private theorem sx_empty (E : Spc) (p : ℕ) (T : Scheme.{0})
    (x : Sx (pullback (triv E 0) (PGL.pr 0)) p T) : IsEmpty T := by
  have y : Sx (PGL 0) p T := Sx.map (pullback.snd (triv E 0) (PGL.pr 0)) x
  have v : Um 0 Γ(T, ⊤) := (show ComposableArrows (Um 0 Γ(T, ⊤)) p from y).obj 0
  have h : (⊥ : Ideal Γ(T, ⊤)) = ⊤ := by
    have := v.2
    rwa [Set.range_eq_empty, Ideal.span_empty] at this
  have hs : Subsingleton Γ(T, ⊤) := by
    rcases subsingleton_or_nontrivial Γ(T, ⊤) with hs | hn
    · exact hs
    · exact absurd h bot_ne_top
  refine ⟨fun t => ?_⟩
  have := (T.presheaf.germ ⊤ t trivial).hom.codomain_trivial
  exact not_subsingleton (T.presheaf.stalk t) this

private theorem chains_isZero (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (k : ℤ) :
    IsZero (((chains R).obj X).X k) := by
  by_cases hk : k ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact (free_isZero R _ (hX p)).of_iso (chainsXIso R X p)
  · refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat k fun i => ?_
    change -(i : ℤ) ≠ k
    omega

private theorem H_subsingleton (R : Type) [CommRing R] (X : Spc)
    (hX : ∀ (p : ℕ) (T : Scheme.{0}), Nonempty (Sx X p T) → IsEmpty T) (F : Shv R) (n : ℤ) :
    Subsingleton (H R X F n) := ⟨fun a b => by
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  congr 1
  exact Cocycle.ext (Cochain.ext _ _ fun p q h => (chains_isZero R X hX p).eq_of_src _ _)⟩

theorem UpperTheory.projectiveBundleFormula_rank_zero :
    ∀ (q : ℕ) [NeZero q] (E : Spc), PBF q E 0 := by
  intro q _ E n i
  haveI : Subsingleton (Ht q (pullback (triv E 0) (PGL.pr 0)) n i) :=
    H_subsingleton _ _ (fun p T ⟨x⟩ => sx_empty E p T x) _ _
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨fun j => j.elim0, Subsingleton.elim _ _⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.PsiCommDifferentialOfCocycle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Kun

private theorem map_units {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (ε : ℤˣ) (x : Sec F U) :
    Sec.map φ (ε • x) = ε • Sec.map φ x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

private theorem map_add' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y :=
  map_add _ _ _

private theorem mul_mid {R : Type} [CommRing R] {I Q P : Cx R} (μ : Pair Q P I) (U : Scheme.{0}) (k m m' w : ℤ) (e : m = m')
    (h : m + 1 = w) (h' : m' + 1 = w) (A : Sec (Q.X k) U) (B : Sec (P.X 1) U) :
    μ.mul U m 1 w h (Sec.map (Q.d k m) A) B = μ.mul U m' 1 w h' (Sec.map (Q.d k m') A) B := by
  subst e
  rfl

theorem UpperTheory.psi_comm_differential_of_cocycle :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W), Sec.map (P.d 1 2) z = 0 →
        ∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec ((LL I Q).X s) T),
          Sec.map (I.d s t) (psi W μ z T s a) = psi W μ z T t (Sec.map ((LL I Q).d s t) a) := by
  intro R _ W I Q P μ z hz T s t a
  by_cases hst : s + 1 = t
  · subst hst
    have hB : Sec.map (P.d 1 (1 + 1)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z) = 0 := by
      rw [← res_map]
      have h2 : Sec.map (P.d 1 (1 + 1)) z = 0 := hz
      rw [h2]
      exact map_zero _
    have hL := μ.leibniz (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a))
      (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [hB, map_zero, smul_zero, add_zero,
      mul_mid μ (W ⨯ T) (s + -1) (s + -1 + 1) (s + 1 + -1) (s + 1) (by omega) (by omega) (by omega)] at hL
    change Sec.map (I.d s (s + 1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
        s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
      Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ (Sec.map ((LL I Q).d s (s + 1)) a)) +
        (s + 1).negOnePow • μ.mul (W ⨯ T) (s + 1 + -1) 1 (s + 1) (by omega)
          (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ (Sec.map ((LL I Q).d s (s + 1)) a))) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)
    rw [map_add', map_units, hL, c₁_d, c₂_d, res_map, Int.negOnePow_succ]
    congr 1
    have hn : Sec.res (prod.snd : W ⨯ T ⟶ T) (- Sec.map (Q.d (s + -1) (s + 1 + -1)) (c₂ a)) =
        - Sec.map (Q.d (s + -1) (s + 1 + -1)) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) := by
      rw [← res_map]
      exact map_neg _ _
    rw [hn, map_neg, LinearMap.neg_apply, smul_neg, Units.neg_smul, neg_neg]
  · have h1 : I.d s t = 0 := I.shape _ _ hst
    have h2 : (LL I Q).d s t = 0 := (LL I Q).shape _ _ hst
    rw [h1, h2, map_zeroS, map_zeroS, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexIsAdmissible
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem sx_face_face {E : Spc} {p : ℕ} {U : Scheme} (y : Sx E (p+2) U) {a b : Fin (p+2)}
    (h : a ≤ b) : (y.face b.succ).face a = (y.face a.castSucc).face b := by
  unfold Sx.face
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← NatTrans.comp_app,
    SimplicialObject.δ_comp_δ E h]

private theorem sum_neg_one_pow_face_face_eq_zero {A : Type*} [AddCommGroup A] {E : Spc} {p : ℕ} {U : Scheme}
    (f : Sx E p U → A) (y : Sx E (p+2) U) :
    ∑ j : Fin (p+3), ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i) = 0 := by
  have ff : ∀ {a b : Fin (p+2)}, a ≤ b → (y.face b.succ).face a = (y.face a.castSucc).face b :=
    fun h => sx_face_face y h
  rw [← Finset.sum_product' (f := fun (j : Fin (p+3)) (i : Fin (p+2)) => ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) • f ((y.face j).face i)), Finset.univ_product_univ]
  let g : Fin (p+3) × Fin (p+2) → Fin (p+3) × Fin (p+2) := fun ji =>
    if h : (ji.1 : ℕ) ≤ ji.2 then (ji.2.succ, ji.1.castLT (by omega))
    else (ji.2.castSucc, ji.1.pred (by intro h0; simp [h0] at h))
  have gg : ∀ ji, g (g ji) = ji := by
    rintro ⟨j, i⟩
    by_cases h : (j : ℕ) ≤ i
    · have h1 : ¬ ((i.succ : Fin (p+3)) : ℕ) ≤ (j.castLT (by omega) : Fin (p+2)) := by simp; omega
      simp only [g, dif_pos h, dif_neg h1]
      ext <;> simp
    · have h1 : ((i.castSucc : Fin (p+3)) : ℕ) ≤ (j.pred (by intro h0; simp [h0] at h) : Fin (p+2)) := by simp; omega
      simp only [g, dif_neg h, dif_pos h1]
      ext <;> simp
  refine Finset.sum_involution (fun ji _ => g ji) ?_ ?_ (fun _ _ => Finset.mem_univ _) (fun ji _ => gg ji)
  · rintro ⟨j, i⟩ _
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h]
      have hj : j = (j.castLT (by omega) : Fin (p+2)).castSucc := by ext; simp
      have hle : j.castLT (by omega) ≤ i := by rw [Fin.le_def]; simpa using h
      rw [ff hle, ← hj]
      simp only [Fin.val_succ, Fin.coe_castLT]
      rw [← add_smul]
      convert zero_smul ℤ _
      rw [show (i : ℕ) + 1 + j = (j + i) + 1 by ring, pow_succ]; ring
    · simp only [g, dif_neg h]
      have hj0 : j ≠ 0 := by intro h0; simp [h0] at h
      have hle : i ≤ j.pred hj0 := by rw [Fin.le_def]; simp; omega
      have key : (y.face j).face i = (y.face i.castSucc).face (j.pred hj0) := by
        have := ff hle
        rwa [Fin.succ_pred] at this
      rw [key]
      simp only [Fin.coe_castSucc, Fin.coe_pred]
      rw [← add_smul]
      convert zero_smul ℤ _
      have : (j : ℕ) = (j : ℕ) - 1 + 1 := by omega
      rw [this, show (j : ℕ) - 1 + 1 - 1 = (j:ℕ) - 1 by omega, show (j:ℕ) - 1 + 1 + i = (i + (j - 1)) + 1 by ring, pow_succ]; ring
  · rintro ⟨j, i⟩ _ _ heq
    by_cases h : (j : ℕ) ≤ i
    · simp only [g, dif_pos h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega
    · simp only [g, dif_neg h, Prod.mk.injEq] at heq
      have := congrArg Fin.val heq.1; simp at this; omega

theorem UpperTheory.supportDoubleComplex_isAdmissible :
    ∀ (R : Type) [CommRing R] (E : Spc) (Z : Sub E) (K : Cx R) (m : ℤ), (famDC Z K m).Ok := by
  intro R _ E Z K m
  unfold famDC
  constructor
  · intro p s t u x
    apply Subtype.ext
    funext U y
    change Sec.map (K.d (s + m) (t + m) ≫ K.d (t + m) (u + m)) (x.1 U y) = 0
    rw [HomologicalComplex.d_comp_d]
    rfl
  · intro p s x
    apply Subtype.ext
    funext U y
    simp [Fam.δ]
    have hz := sum_neg_one_pow_face_face_eq_zero (fun z => (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U z) y
    have hj : ∀ j : Fin (p+3), (-1 : ℤ) ^ (j : ℕ) • m.negOnePow • ∑ i : Fin (p+2), (-1 : ℤ) ^ (i : ℕ) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) =
        m.negOnePow • ∑ i : Fin (p+2), ((-1 : ℤ) ^ ((j : ℕ) + (i : ℕ))) •
        (x : (V : Scheme) → Sx E p V → Sec (K.X (s + m)) V) U ((y.face j).face i) := by
      intro j
      rw [smul_comm, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, pow_add]
    simp_rw [hj, ← Finset.smul_sum]
    rw [hz, smul_zero, smul_zero]
  · intro p s t x
    apply Subtype.ext
    funext U y
    simp [Fam.map, Fam.δ]
end

