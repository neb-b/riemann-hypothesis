module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHEmptyBij
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.Onto

variable {R : Type} [CommRing R]

abbrev prodCx {I : Type} (K : I → Cx.{w} R) : Cx.{w} R where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => ((K i).d n).comp (LinearMap.proj i)
  dd n x := funext fun i => (K i).dd n (x i)

def prodHom {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) : Cx.Hom (prodCx K) (prodCx L) (RingHom.id R) where
  f n := LinearMap.pi fun i => ((φ i).f n).comp (LinearMap.proj i)
  comm n x := funext fun i => (φ i).comm n (x i)

theorem mem_B_prod {I : Type} (K : I → Cx.{w} R) (n : ℕ) (a : (prodCx K).X n) :
    a ∈ (prodCx K).B n ↔ ∀ i, a i ∈ (K i).B n := by
  cases n with
  | zero =>
    constructor
    · intro h i
      have h0 : a = 0 := h
      rw [h0]
      exact Submodule.zero_mem _
    · intro h
      exact funext fun i => h i
  | succ n =>
    constructor
    · rintro ⟨b, rfl⟩ i
      exact ⟨b i, rfl⟩
    · intro h
      choose b hb using h
      exact ⟨b, funext hb⟩

theorem prod_bij {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R))
    (h : ∀ i n, Function.Bijective ((φ i).mapH n)) (n : ℕ) :
    Function.Bijective ((prodHom φ).mapH n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx K) n).1 x
    have hb : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hb, mem_B_prod] at hx
    rw [(CrystallineSemistableComparison.P.cls_surj _ n).2.1, mem_B_prod]
    intro i
    have hai : (K i).d n (a i) = 0 := congrFun ha i
    have hbi : (L i).d n ((φ i).f n (a i)) = 0 := by rw [(φ i).comm, hai, map_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hai]
    apply (injective_iff_map_eq_zero _).1 (h i n).1
    rw [CrystallineSemistableComparison.P.mapH_cls _ n _ hai hbi, (CrystallineSemistableComparison.P.cls_surj _ n).2.1]
    exact hx i
  · intro y
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx L) n).1 y
    have hbi : ∀ i, (L i).d n (b i) = 0 := fun i => congrFun hb i
    have key : ∀ i, ∃ a, ∃ ha : (K i).d n a = 0, (φ i).f n a - b i ∈ (L i).B n := by
      intro i
      obtain ⟨x, hx⟩ := (h i n).2 ((L i).cls (b i) (hbi i))
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K i) n).1 x
      have hc : (L i).d n ((φ i).f n a) = 0 := by rw [(φ i).comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hc] at hx
      exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc (hbi i)).1 hx⟩
    choose a ha hab using key
    have ha' : (prodCx K).d n a = 0 := funext ha
    have hc : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha', map_zero]
    refine ⟨(prodCx K).cls a ha', ?_⟩
    rw [CrystallineSemistableComparison.P.mapH_cls (prodHom φ) n a ha' hc, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc hb, mem_B_prod]
    exact hab

variable {ι : Type} [DecidableEq ι]

abbrev cechCos (A : Sy.{w} R ι) : CosCx.{w} R where
  K p := prodCx fun i : Fin (p + 1) → ι => A.K (ent i)
  δ p k :=
    { f := fun q => (A.term q).cech.δ p k
      comm := fun q x => funext fun t => (A.res (ent_comp t k.succAbove)).comm q (x (t ∘ k.succAbove)) }
  rel p j i q x := (A.term q).cech.rel p j i x

def cechAug (A : Sy.{w} R ι) (hA : A.Desc) : DCx.AugRow (A.K ∅) (cechCos A).dcx where
  ε q := (A.term q).aug
  hε q x := (hA q).1 x
  comm q x := funext fun t => (A.res (Finset.empty_subset (ent t))).comm q x

theorem cechAug_row (A : Sy.{w} R ι) (hA : A.Desc) (q : ℕ) :
    ((cechCos A).dcx.row q).ResUpTo 1 ((cechAug A hA).ε q) := hA q

def cechHom {A B : Sy.{w} R ι} (m : A.Hom B) :
    DCx.Hom (cechCos A).dcx (cechCos B).dcx (RingHom.id R) where
  f p q := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).f q
  ch p q x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cos.d_apply, Cos.d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    refine congrArg _ (funext fun t => ?_)
    exact (m.nat (ent_comp t k.succAbove) q (x (t ∘ k.succAbove))).symm
  cv p q x := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).comm q x

theorem cechHom_col {A B : Sy.{w} R ι} (m : A.Hom B)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (p q : ℕ) :
    Function.Bijective (((cechHom m).col p).mapH q) :=
  prod_bij (fun i : Fin (p + 1) → ι => m.φ (ent i))
    (fun i n => h _ ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ n) q

theorem upTo_one {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) : UpTo (1 : R) f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ?_⟩
    · simpa using h1 x hx
    · simpa using h2 y
  · intro h
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · rw [one_smul]
      exact (injective_iff_map_eq_zero f).1 h.1 x hx
    · simpa using h.2 y

theorem cls_congr {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem edge_square {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc) (n : ℕ) (a : (A.K ∅).X n) :
    (cechHom m).tot.f n ((cechAug A hA).edge.f n a) = (cechAug B hB).edge.f n ((m.φ ∅).f n a) := by
  apply Subtype.ext
  funext p q
  by_cases h : p = 0 ∧ q = n
  · obtain ⟨rfl, rfl⟩ := h
    change (cechHom m).f 0 q ((cechCos A).dcx.sgl 0 q ((cechAug A hA).ε q a) 0 q) =
      (cechCos B).dcx.sgl 0 q ((cechAug B hB).ε q ((m.φ ∅).f q a)) 0 q
    rw [DCx.sgl_self, DCx.sgl_self]
    funext t
    exact m.nat (Finset.empty_subset (ent t)) q a
  · have h' : p ≠ 0 ∨ q ≠ n := by omega
    change (cechHom m).f p q ((cechCos A).dcx.sgl 0 n ((cechAug A hA).ε n a) p q) =
      (cechCos B).dcx.sgl 0 n ((cechAug B hB).ε n ((m.φ ∅).f n a)) p q
    rw [DCx.sgl_ne _ _ h', DCx.sgl_ne _ _ h', map_zero]

theorem mapH_empty_bij {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (n : ℕ) :
    Function.Bijective ((m.φ ∅).mapH n) := by
  have eA : Function.Bijective ((cechAug A hA).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug A hA) 1 (cechAug_row A hA) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eB : Function.Bijective ((cechAug B hB).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug B hB) 1 (cechAug_row B hB) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eT : Function.Bijective ((cechHom m).tot.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_map_col (cechHom m) 1 n fun p q _ => (upTo_one _).2 (cechHom_col m h p q)
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have sq : ∀ x, (cechAug B hB).edge.mapH n ((m.φ ∅).mapH n x) =
      (cechHom m).tot.mapH n ((cechAug A hA).edge.mapH n x) := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (A.K ∅) n).1 x
    have c1 : (B.K ∅).d n ((m.φ ∅).f n a) = 0 := by rw [(m.φ ∅).comm, ha, map_zero]
    have c2 : (cechCos B).dcx.tot.d n ((cechAug B hB).edge.f n ((m.φ ∅).f n a)) = 0 := by
      rw [(cechAug B hB).edge.comm, c1, map_zero]
    have c3 : (cechCos A).dcx.tot.d n ((cechAug A hA).edge.f n a) = 0 := by
      rw [(cechAug A hA).edge.comm, ha, map_zero]
    have c4 : (cechCos B).dcx.tot.d n ((cechHom m).tot.f n ((cechAug A hA).edge.f n a)) = 0 := by
      rw [(cechHom m).tot.comm, c3, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls (m.φ ∅) n a ha c1, CrystallineSemistableComparison.P.mapH_cls (cechAug B hB).edge n _ c1 c2,
      CrystallineSemistableComparison.P.mapH_cls (cechAug A hA).edge n a ha c3, CrystallineSemistableComparison.P.mapH_cls (cechHom m).tot n _ c3 c4]
    exact cls_congr (edge_square m hA hB n a).symm c2 c4
  constructor
  · intro x y hxy
    apply eA.1
    apply eT.1
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨u, hu⟩ := eT.2 ((cechAug B hB).edge.mapH n y)
    obtain ⟨x, rfl⟩ := eA.2 u
    refine ⟨x, eB.1 ?_⟩
    rw [sq, hu]

theorem mvBij : CrystallineSemistableComparison.Onto.MVBij := fun _ _ _ _ _ _ m hA hB h n => mapH_empty_bij m hA hB h n

end GlobalTheory.CompanionTheory.Onto
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatible
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero

variable {R : Type} [CommRing R]

section Chains

variable {C : Type} [Category.{0} C]

abbrev pt (a : C) : Fin (0 + 1) ⥤ C := (Functor.const _).obj a

theorem exists_pt (c : Fin (0 + 1) ⥤ C) : ∃ a, c = pt a := by
  have hX : ∀ X : Fin (0 + 1), X = 0 := fun X => Fin.ext (by have := X.isLt; simp only [Fin.val_zero]; omega)
  have hobj : ∀ X, c.obj X = (pt (c.obj 0)).obj X := fun X => congrArg c.obj (hX X)
  refine ⟨c.obj 0, CategoryTheory.Functor.ext hobj (fun X Y f => ?_)⟩
  obtain rfl := hX X
  obtain rfl := hX Y
  obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
  simp

theorem eval_chain (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1) ⥤ C) :
    x c = x (pt (c.obj (Fin.last 0))) := by
  obtain ⟨a, rfl⟩ := exists_pt c
  rfl

theorem pull_last (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    pullNC G (Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom x c = x (pt (c.obj (Fin.last (0 + 1)))) := by
  rw [pullNC_apply]
  show (G.map (c.map (homOfLE (le_refl (Fin.last (0 + 1)))))).hom
    (x ((Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom.monotone.functor ⋙ c)) = _
  rw [show homOfLE (le_refl (Fin.last (0 + 1))) = 𝟙 (Fin.last (0 + 1) : Fin (0 + 1 + 1)) from
    Subsingleton.elim _ _, c.map_id, G.map_id]
  exact eval_chain G x _

theorem pull_first (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    pullNC G (Fin.succAboveOrderEmb (1 : Fin (0 + 2))).toOrderHom x c =
      (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (x (pt (c.obj 0))) := by
  rw [pullNC_apply]
  exact congrArg (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (eval_chain G x _)

theorem dNC_zero_apply (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    dNC G 0 x c = (show G.obj (c.obj (Fin.last (0 + 1))) from x (pt (c.obj (Fin.last (0 + 1))))) -
      (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (x (pt (c.obj 0))) := by
  have hsum : dNC G 0 x c = pullNC G (Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom x c -
      pullNC G (Fin.succAboveOrderEmb (1 : Fin (0 + 2))).toOrderHom x c := by
    simp only [dNC, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]
    show ∑ i : Fin 2, (-1 : R) ^ (i : ℕ) • (pullNC G (Fin.succAboveOrderEmb i).toOrderHom) x c = _
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul, sub_eq_add_neg] <;> rfl
  rw [hsum, pull_last, pull_first] <;> rfl

end Chains

section Semilattice

variable {P : Type} [SemilatticeInf P] {κ : Type} (e : κ → P) (G : Pᵒᵖ ⥤ ModuleCat.{0} R)

def epsLin : NC G 0 →ₗ[R] Cube.Term (cubeOf e G) 1 where
  toFun x s hs := x (pt (op (s.1.inf' hs.down e)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev val (x : NC G 0) (a : P) : G.obj (op a) := x (pt (op a))

def Compat (x : NC G 0) : Prop :=
  ∀ ⦃a b : P⦄ (h : b ≤ a), val G x b = (G.map (homOfLE h).op).hom (val G x a)

theorem dNC_zero_iff (x : NC G 0) : dNC G 0 x = 0 ↔ Compat G x := by
  constructor
  · intro hx a b h
    have h1 := congrFun hx (ComposableArrows.mk₁ (homOfLE h).op)
    have hm : (ComposableArrows.mk₁ (homOfLE h).op).map (homOfLE (Fin.le_last (0 : Fin (0 + 1 + 1)))) =
        (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [dNC_zero_apply, Pi.zero_apply, sub_eq_zero, hm] at h1
    exact h1
  · intro hc
    funext c
    rw [dNC_zero_apply, Pi.zero_apply, sub_eq_zero]
    have h : (c.obj (Fin.last (0 + 1))).unop ≤ (c.obj 0).unop := leOfHom (c.map (homOfLE (Fin.le_last 0))).unop
    have hm : c.map (homOfLE (Fin.le_last 0)) = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hm]
    exact hc h

theorem epsLin_injective (he : Function.Surjective e) : Function.Injective (epsLin e G) := by
  intro x y hxy
  funext c
  rw [eval_chain G x c, eval_chain G y c]
  obtain ⟨k, hk⟩ := he (c.obj (Fin.last 0)).unop
  have h1 : x (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e))) =
      y (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e))) :=
    congrFun (congrFun hxy ⟨{k}, Finset.card_singleton k⟩) ⟨Finset.singleton_nonempty k⟩
  rw [Finset.inf'_singleton, hk] at h1
  exact h1

private theorem map_eqToHom_singleton_eq (z : Cube.Term (cubeOf e G) 1) {k' k : κ} (h : k' = k)
    (pr : op (({k'} : Finset κ).inf' (Finset.singleton_nonempty k') e) =
      op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e)) :
    (G.map (eqToHom pr)).hom (z ⟨{k'}, Finset.card_singleton k'⟩ ⟨Finset.singleton_nonempty k'⟩) =
      z ⟨{k}, Finset.card_singleton k⟩ ⟨Finset.singleton_nonempty k⟩ := by
  subst h
  rw [eqToHom_refl, G.map_id] <;> rfl

theorem epsLin_surjective (he : Function.Injective e) (he' : Function.Surjective e) :
    Function.Surjective (epsLin e G) := by
  intro z
  choose f hf using he'
  have hop : ∀ p : P, op (({f p} : Finset κ).inf' (Finset.singleton_nonempty (f p)) e) = op p := by
    intro p
    rw [Finset.inf'_singleton, hf]
  refine ⟨fun c => (G.map (eqToHom (hop (c.obj (Fin.last 0)).unop))).hom
      (z ⟨{f (c.obj (Fin.last 0)).unop}, Finset.card_singleton _⟩ ⟨Finset.singleton_nonempty _⟩), ?_⟩
  funext s hs
  obtain ⟨s, hs1⟩ := s
  obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp hs1
  have hk : f (({k} : Finset κ).inf' hs.down e) = k := by
    apply he
    rw [hf, Finset.inf'_singleton]
  exact map_eqToHom_singleton_eq e G z hk _

theorem d_pair (x : NC G 0) {κ : Type} [LinearOrder κ] (e : κ → P) {i j : κ} (hij : i < j)
    (hp : ({i, j} : Finset κ).Nonempty)
    (h1 : ({i, j} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e)
    (h2 : ({i, j} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e) :
    Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{i, j}, Finset.card_pair hij.ne⟩ ⟨hp⟩ =
      (G.map (homOfLE h1).op).hom (val G x _) - (G.map (homOfLE h2).op).hom (val G x _) := by
  erw [GlobalTheory.Cube.d_one_apply_pair (cubeOf e G) (epsLin e G x) hij, Pi.sub_apply]
  exact congrArg₂ (· - ·)
    (cubeRes_apply e G (by simp : ({j} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{j}, Finset.card_singleton j⟩)
      (Finset.singleton_nonempty j) ⟨hp⟩)
    (cubeRes_apply e G (by simp : ({i} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{i}, Finset.card_singleton i⟩)
      (Finset.singleton_nonempty i) ⟨hp⟩)

theorem step (x : NC G 0) {a a' b b' m : P} (ha : a' = a) (hb : b' = b) (hm : m = b) (h : b ≤ a)
    (h1 : m ≤ a') (h2 : m ≤ b')
    (E : (G.map (homOfLE h1).op).hom (val G x a') = (G.map (homOfLE h2).op).hom (val G x b')) :
    val G x b = (G.map (homOfLE h).op).hom (val G x a) := by
  subst ha hb hm
  have e2 : homOfLE h2 = 𝟙 _ := Subsingleton.elim _ _
  rw [e2, op_id, G.map_id] at E
  exact E.symm

theorem d_eps_zero_iff {κ : Type} [LinearOrder κ] (e : κ → P) (he : Function.Surjective e) (x : NC G 0) :
    Cube.d (cubeOf e G) 1 (epsLin e G x) = 0 ↔ Compat G x := by
  constructor
  · intro hd a b h
    obtain ⟨i, rfl⟩ := he a
    obtain ⟨j, rfl⟩ := he b
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hp : ({i, j} : Finset κ).Nonempty := Finset.insert_nonempty _ _
      have h1 : ({i, j} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({i, j} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{i, j}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0 := by
        rw [hd] <;> rfl
      rw [d_pair G x e hij hp h1 h2, sub_eq_zero] at E0
      exact step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_right.mpr h]) h h2 h1 E0.symm
    · have e2 : homOfLE h = 𝟙 _ := Subsingleton.elim _ _
      rw [e2, op_id, G.map_id] <;> rfl
    · have hp : ({j, i} : Finset κ).Nonempty := Finset.insert_nonempty _ _
      have h1 : ({j, i} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({j, i} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{j, i}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0 := by
        rw [hd] <;> rfl
      rw [d_pair G x e hij hp h1 h2, sub_eq_zero] at E0
      exact step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_left.mpr h]) h h1 h2 E0
  · intro hc
    have hc' : ∀ ⦃a b : P⦄ (h : b ≤ a), val G x b = (G.map (homOfLE h).op).hom (val G x a) := hc
    funext t ht
    obtain ⟨t, htc⟩ := t
    obtain ⟨i, j, hne, hs⟩ := Finset.card_eq_two.mp htc
    rcases lt_or_gt_of_ne hne with hij | hij
    · subst hs
      have h1 : ({i, j} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({i, j} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl
    · rw [Finset.pair_comm] at hs
      subst hs
      have h1 : ({j, i} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({j, i} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl

end Semilattice

theorem degZero {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P) :
    Function.Bijective e → ∃ ε : ∀ G : Pᵒᵖ ⥤ ModuleCat.{0} R, (nerveCx.obj G).X 0 ≅ ((cechOf e).obj G).X 0,
    (∀ {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G'),
      (nerveCx.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ ((cechOf e).map φ).f 0) ∧
    ∀ (G : Pᵒᵖ ⥤ ModuleCat.{0} R) (x : (nerveCx.obj G).X 0),
      ((nerveCx.obj G).d 0 1).hom x = 0 ↔ (((cechOf e).obj G).d 0 1).hom ((ε G).hom.hom x) = 0 := by
  intro hbij
  refine ⟨fun G => (LinearEquiv.ofBijective (epsLin e G)
      ⟨epsLin_injective e G hbij.2, epsLin_surjective e G hbij.1 hbij.2⟩).toModuleIso, ?_, ?_⟩
  · intro G G' φ
    ext x
    rfl
  · intro G x
    have hd1 : (nerveCx.obj G).d 0 1 = ModuleCat.ofHom (dNC G 0) := nerveCx_d G 0
    have hc1 : ((cechOf e).obj G).d 0 1 = ModuleCat.ofHom ((cubeOf e G).d 1) := GlobalTheory.cechComplex_d (cubeOf e G) 0
    rw [hd1, hc1]
    exact (dNC_zero_iff G x).trans (d_eps_zero_iff G e hbij.2 x).symm

end GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsDecomposition
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

private theorem valuation_lt_one_iff_mem_and_inv_not_mem {K : Type*} [Field K] (A : ValuationSubring K) (y : K) :
    A.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ A := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hp : 0 < A.valuation y := (Valuation.pos_iff _).2 hy
    rw [← A.valuation_le_one_iff, Valuation.map_inv, inv_le_one₀ hp, not_le]
    simp [hy]

theorem isPlaceOver_transfer_fieldIso :
    ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE eO eV hO hv A A' hA v
  have hlt : ∀ y : Ω, A'.valuation (E y) < 1 ↔ A.valuation y < 1 := by
    intro y
    rw [valuation_lt_one_iff_mem_and_inv_not_mem, valuation_lt_one_iff_mem_and_inv_not_mem, ← map_inv₀, hA, map_eq_zero_iff E E.injective]
  have hx : ∀ x : 𝓞 F, (A'.valuation (algebraMap F' Ω' ((eO x : 𝓞 F') : F')) < 1 ↔ eO x ∈ (eV v).asIdeal) ↔
      (A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hO x, ← hE, hlt, ← hv]
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  constructor
  · intro h x'
    obtain ⟨x, rfl⟩ := eO.surjective x'
    exact (hx x).2 (h x)
  · intro h x
    exact (hx x).1 (h (eO x))

end GlobalTheory.CompanionTheory.PTIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1DegreeZeroFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem shuffle_cup1_degree_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (u : Cn (box F) 1) (w : Cn (box F) 0) :
    Sh F 0 (cup1 (box F) 0 u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst 0 1) OrderHom.id w := by
  have hsum : GlobalTheory.CompanionTheory.HopfC.Sh F 0 = AlgHom.toLinearMap
      (GlobalTheory.CompanionTheory.HopfC.bv F (N := 0 + 1) (p := 1) (q := 0)
        (GlobalTheory.CompanionTheory.HopfC.sI 0) (Fin.predAboveOrderHom 0)) := by
    rw [GlobalTheory.CompanionTheory.HopfC.Sh]
    first
    | (rw [Fin.sum_univ_one]; simp)
    | simp
    | (ext; simp)
  rw [hsum, AlgHom.toLinearMap_apply, GlobalTheory.CompanionTheory.HopfC.cup1_apply, map_mul,
    GlobalTheory.CompanionTheory.HopfC.bv_pr, GlobalTheory.CompanionTheory.HopfC.bv_pr]
  congr 1
  all_goals
    first
    | rfl
    | (refine GlobalTheory.CompanionTheory.HopfC.bv_congr (fun i => ?_) (fun i => ?_) _ <;>
        fin_cases i <;> first | rfl | decide | exact Subsingleton.elim (α := Fin 1) _ _)

end GlobalTheory.CompanionTheory.HopfC
end
end

