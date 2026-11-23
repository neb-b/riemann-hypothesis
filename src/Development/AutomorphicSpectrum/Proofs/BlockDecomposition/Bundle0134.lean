module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0128
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRight
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

private theorem cochainReindex_apply_const_obj (F : C ⥤ CommAlgCat.{0} R) {n m : ℕ}
    (e : Fin (n + 1) →o Fin (m + 1)) (x : MainStatements.Hodge.Cn F n) (T₀ : C) :
    GlobalTheory.CompanionTheory.HopfC.pr F e x ((Functor.const (Fin (m + 1))).obj T₀) =
      x ((Functor.const (Fin (n + 1))).obj T₀) := by
  first
  | exact GlobalTheory.CatCoh.mp_id F T₀ _
  | exact (GlobalTheory.CatCoh.mp_id F T₀ (x ((Functor.const (Fin (n + 1))).obj T₀)) : _)
  | (simp only [GlobalTheory.CompanionTheory.HopfC.pr]; exact GlobalTheory.CatCoh.mp_id F T₀ _)

theorem cocycle_const (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (x : Cn F 1) (hx : dn F 1 x = 0) :
    x ((Functor.const (Fin (1 + 1))).obj T₀) = 0 := by
  have h : MainStatements.Hodge.dn F 1 x ((Functor.const (Fin (1 + 1 + 1))).obj T₀) = 0 := by
    rw [hx]; rfl
  rw [GlobalTheory.CompanionTheory.HopfC.dn_eq] at h
  first
  | rw [Fin.sum_univ_three] at h
  | simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simp only [Pi.add_apply, Pi.smul_apply, cochainReindex_apply_const_obj] at h
  first
  | simpa using h
  | (norm_num at h; exact h)

theorem evL_tmul_one (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (a : F.obj T₀) :
    evL F T₀ T ε (a ⊗ₜ[R] 1) = algebraMap R (F.obj T) (ε a) := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem evL_one_tmul (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (b : F.obj T) :
    evL F T₀ T ε (1 ⊗ₜ[R] b) = b := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem boxE_pull_boxL_boxR (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1)
    (hx : dn F 1 x = 0) :
    pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  have h0 := GlobalTheory.CompanionTheory.HopfC.cocycle_const F T₀ x hx
  refine ⟨?_, ?_⟩
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε
          (x ((Functor.const (Fin (1 + 1))).obj T₀) ⊗ₜ[R] 1) := rfl
      _ = algebraMap R _ (ε (x ((Functor.const (Fin (1 + 1))).obj T₀))) :=
          GlobalTheory.CompanionTheory.HopfC.evL_tmul_one F T₀ _ ε _
      _ = 0 := by rw [h0, map_zero, map_zero]
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε (1 ⊗ₜ[R] x c) := rfl
      _ = x c := GlobalTheory.CompanionTheory.HopfC.evL_one_tmul F T₀ _ ε _

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDApply
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.CechOne

variable {R : Type} [CommRing R]

theorem mem_B_of_cls {K : Cx.{w} R} {n : ℕ} {x : K.X n} (hx : K.d n x = 0) (h : K.cls x hx = 0) : x ∈ K.B n :=
  (Submodule.Quotient.mk_eq_zero ((K.B n).submoduleOf (K.Z n))).1 h

theorem d_of_mem_B (K : Cx.{w} R) (n : ℕ) (x : K.X n) (h : x ∈ K.B n) : K.d n x = 0 := by
  cases n with
  | zero =>
    have h0 : x = 0 := h
    rw [h0, map_zero]
  | succ n =>
    obtain ⟨g, rfl⟩ := h
    exact K.dd n g

section Tic

variable {K : DCx.{w} R} {E : Cx.{w'} R} (e : DCx.AugRow E K) {a : ℕ}

def LowB (q : ℕ) : Prop :=
  (∀ p (b : K.X (p + 1) q), b ∈ (K.col (p + 1)).B q → K.dh (p + 1) q b = 0 →
    ∃ b' ∈ (K.col p).B q, K.dh p q b' = b) ∧
  (∀ b : K.X 0 q, b ∈ (K.col 0).B q → K.dh 0 q b = 0 → ∃ z ∈ E.B q, e.ε q z = b)

theorem lowB (hr0 : ∀ q x, K.dh 0 q x = 0 → ∃ y, e.ε q y = x)
    (hr : ∀ p q x, K.dh (p + 1) q x = 0 → ∃ y, K.dh p q y = x)
    (hc : ∀ p q, q ≠ a → ∀ x, K.dv p q x = 0 → x ∈ (K.col p).B q) : ∀ q, q ≤ a → LowB e q := by
  intro q
  induction q with
  | zero =>
    intro _
    constructor
    · intro p b hb _
      have h0 : b = 0 := hb
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
    · intro b hb _
      have h0 : b = 0 := hb
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
  | succ q ih =>
    intro hq
    obtain ⟨i1, -⟩ := ih (by omega)
    have L1 : ∀ p (x : K.X (p + 1) q), K.dv (p + 1) q x = 0 → K.dh (p + 1) q x = 0 →
        ∃ y, K.dh p q y = x ∧ K.dv p q y = 0 := by
      intro p x hv hh
      obtain ⟨b', hb', e'⟩ := i1 p x (hc _ _ (by omega) x hv) hh
      exact ⟨b', e', d_of_mem_B (K.col p) q b' hb'⟩
    constructor
    · rintro p b ⟨c, rfl⟩ hb
      change K.dh (p + 1) (q + 1) (K.dv (p + 1) q c) = 0 at hb
      rw [K.hv] at hb
      obtain ⟨y, hy, hyv⟩ := L1 (p + 1) (K.dh (p + 1) q c) hb (K.hh _ _ _)
      obtain ⟨v, hv⟩ := hr p q (c - y) (by rw [map_sub, hy, sub_self])
      refine ⟨K.dv p q v, ⟨v, rfl⟩, ?_⟩
      change K.dh p (q + 1) (K.dv p q v) = K.dv (p + 1) q c
      rw [K.hv, hv, map_sub, hyv, sub_zero]
    · rintro b ⟨c, rfl⟩ hb
      change K.dh 0 (q + 1) (K.dv 0 q c) = 0 at hb
      rw [K.hv] at hb
      obtain ⟨y, hy, hyv⟩ := L1 0 (K.dh 0 q c) hb (K.hh _ _ _)
      obtain ⟨z, hz⟩ := hr0 q (c - y) (by rw [map_sub, hy, sub_self])
      refine ⟨E.d q z, ⟨z, rfl⟩, ?_⟩
      change e.ε (q + 1) (E.d q z) = K.dv 0 q c
      rw [← e.comm, hz, map_sub, hyv, sub_zero]

theorem mem_B_of_eps (hinj : ∀ q, Function.Injective (e.ε q)) (h : ∀ q, q ≤ a → LowB e q) {q : ℕ} (hq : q ≤ a)
    (z : E.X q) (hz : e.ε q z ∈ (K.col 0).B q) : z ∈ E.B q := by
  obtain ⟨z', hz', h'⟩ := (h q hq).2 _ hz (e.hε q z)
  rwa [← hinj q h']

theorem exists_lift (hinj : ∀ q, Function.Injective (e.ε q)) (hr0 : ∀ q x, K.dh 0 q x = 0 → ∃ y, e.ε q y = x)
    (h : ∀ q, q ≤ a → LowB e q) (u : K.X 0 a) (hu : K.dv 0 a u = 0) (hd : K.dh 0 a u ∈ (K.col 1).B a) :
    ∃ z b, E.d a z = 0 ∧ b ∈ (K.col 0).B a ∧ e.ε a z + b = u := by
  obtain ⟨b, hb, eb⟩ := (h a le_rfl).1 0 _ hd (K.hh _ _ _)
  obtain ⟨z, hz⟩ := hr0 a (u - b) (by rw [map_sub, eb, sub_self])
  refine ⟨z, b, hinj (a + 1) ?_, hb, by rw [hz, sub_add_cancel]⟩
  rw [← e.comm, hz, map_zero, map_sub, hu, d_of_mem_B (K.col 0) a b hb, sub_zero]

end Tic

variable {ι : Type} [DecidableEq ι]

theorem cech_d_apply (P : PM.{w} R ι) (p : ℕ) (x : P.cech.X p) (t : Fin (p + 2) → ι) :
    P.cech.d p x t = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • P.res (ent_comp t k.succAbove) (x (t ∘ k.succAbove)) := by
  rw [Cos.d_apply, Finset.sum_apply]
  rfl

theorem d_aug (P : PM.{w} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  funext t
  rw [cech_d_apply, Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • P.res _ (P.res _ x) + (-1 : ℤ) ^ 1 • P.res _ (P.res _ x) = 0
  rw [P.res_comp, P.res_comp]
  simp

theorem ent_nonempty {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty :=
  Finset.univ_nonempty.image i

variable (A : Sy.{w} R ι)

abbrev dcx : DCx.{w} R where
  X p q := (A.term q).cech.X p
  dh p q := (A.term q).cech.d p
  dv p q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  hh p q := (A.term q).cech.dd p
  vv p q x := by
    funext i
    exact (A.K (ent i)).dd q (x i)
  hv p q x := by
    funext t
    rw [cech_d_apply]
    change _ = (A.K (ent t)).d q ((A.term q).cech.d p x t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cech_d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    exact congrArg _ ((A.res _).comm q _).symm

def aug : DCx.AugRow (A.K ∅) (dcx A) where
  ε q := (A.term q).aug
  hε q x := d_aug (A.term q) x
  comm q x := by
    funext i
    exact (A.res _).comm q x

theorem mem_col_B {p q : ℕ} (x : (dcx A).X p q) (h : ∀ i, x i ∈ (A.K (ent i)).B q) : x ∈ ((dcx A).col p).B q := by
  cases q with
  | zero =>
    have h0 : x = 0 := funext h
    exact h0
  | succ q =>
    choose c hc using h
    exact ⟨c, funext hc⟩

theorem col_B_mem {p q : ℕ} (x : (dcx A).X p q) (h : x ∈ ((dcx A).col p).B q) (i) : x i ∈ (A.K (ent i)).B q := by
  cases q with
  | zero =>
    have h0 : x = 0 := h
    rw [h0]
    exact Submodule.zero_mem _
  | succ q =>
    obtain ⟨c, rfl⟩ := h
    exact ⟨c i, rfl⟩

theorem oneLow : OneLow := by
  intro R _ ι _ A a hD hO
  have hinj : ∀ q, Function.Injective ((aug A).ε q) := fun q =>
    (injective_iff_map_eq_zero _).2 fun x hx => by simpa using (hD q).2.1 x hx
  have hr0 : ∀ q x, (dcx A).dh 0 q x = 0 → ∃ y, (aug A).ε q y = x := fun q x hx => by
    obtain ⟨y, hy⟩ := (hD q).2.2.1 x hx
    exact ⟨y, hy.trans (one_smul _ _)⟩
  have hr : ∀ p q x, (dcx A).dh (p + 1) q x = 0 → ∃ y, (dcx A).dh p q y = x := fun p q x hx => by
    obtain ⟨y, hy⟩ := (hD q).2.2.2 p x hx
    exact ⟨y, hy.trans (one_smul _ _)⟩
  have hc : ∀ p q, q ≠ a → ∀ x, (dcx A).dv p q x = 0 → x ∈ ((dcx A).col p).B q := by
    intro p q hq x hx
    refine mem_col_B A x fun i => ?_
    have hi : (A.K (ent i)).d q (x i) = 0 := congrFun hx i
    have := hO (ent i) (ent_nonempty i) q hq
    exact mem_B_of_cls hi (Subsingleton.elim _ _)
  have hL := lowB (aug A) hr0 hr hc
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine mem_B_of_eps (aug A) hinj hL hj.le z.1 (hc 0 j hj.ne _ ?_)
    rw [(aug A).comm, show (A.K ∅).d j z.1 = 0 from z.2, map_zero]
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine mem_B_of_eps (aug A) hinj hL le_rfl z.1 (mem_col_B A _ fun i => ?_)
    have hz : (A.K (ent i)).d a ((A.res (Finset.empty_subset _)).f a z.1) = 0 := by
      rw [(A.res _).comm, show (A.K ∅).d a z.1 = 0 from z.2, map_zero]
    exact mem_B_of_cls hz (congrFun hx i)
  · intro y
    constructor
    · intro hy
      have hs : ∀ i, ∃ u : (A.K (ent i)).Z a, Submodule.Quotient.mk u = y i := fun i =>
        Submodule.Quotient.mk_surjective _ (y i)
      choose u hu using hs
      let u' : (dcx A).X 0 a := fun i => (u i).1
      have hv : (dcx A).dv 0 a u' = 0 := funext fun i => (u i).2
      have hd : (dcx A).dh 0 a u' ∈ ((dcx A).col 1).B a := by
        refine mem_col_B A _ fun t => ?_
        have h := congrFun hy t
        rw [cech_d_apply, Fin.sum_univ_two, ← hu, ← hu] at h
        have hz : (A.K (ent t)).d a ((dcx A).dh 0 a u' t) = 0 := congrFun ((dcx A).hv 0 a u' ▸ (by rw [hv, map_zero] : (dcx A).dh 0 (a + 1) ((dcx A).dv 0 a u') = 0)) t
        refine mem_B_of_cls hz ?_
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h
        have e : (⟨(dcx A).dh 0 a u' t, hz⟩ : (A.K (ent t)).Z a) =
            (A.res (ent_comp t (Fin.succAbove 0))).mapZ a (u (t ∘ Fin.succAbove 0)) -
              (A.res (ent_comp t (Fin.succAbove 1))).mapZ a (u (t ∘ Fin.succAbove 1)) := by
          refine Subtype.ext ?_
          change (A.term a).cech.d 0 u' t = _
          rw [cech_d_apply, Fin.sum_univ_two]
          simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
          exact (sub_eq_add_neg _ _).symm
        change Submodule.Quotient.mk (⟨(dcx A).dh 0 a u' t, hz⟩ : (A.K (ent t)).Z a) = 0
        rw [e, Submodule.Quotient.mk_sub, sub_eq_add_neg]
        exact h
      obtain ⟨z, b, hz, hb, e⟩ := exists_lift (aug A) hinj hr0 hL u' hv hd
      refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
      funext i
      rw [← hu]
      change Submodule.Quotient.mk ((A.res (Finset.empty_subset _)).mapZ a ⟨z, hz⟩) = Submodule.Quotient.mk (u i)
      refine (Submodule.Quotient.eq _).2 ?_
      have hbi := col_B_mem A b hb i
      have e' : (A.term a).aug z i + b i = (u i).1 := congrFun e i
      have e2 : (A.term a).aug z i - (u i).1 = -(b i) := by
        rw [← e']
        abel
      change (A.term a).aug z i - (u i).1 ∈ (A.K (ent i)).B a
      rw [e2]
      exact neg_mem hbi
    · rintro ⟨x, rfl⟩
      exact d_aug _ x

end GlobalTheory.CompanionTheory.CechOne

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]

theorem secMap_eq_restrictGlobal
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    (W : X.Opens) (r : R) :
    (GlobalTheory.CechDR.secMap s W).hom r = GlobalTheory.restrictGlobal X W (algebraMap R Γ(X, ⊤) r) := by
  rw [← GlobalTheory.map_restrictGlobal (homOfLE (le_top : W ≤ ⊤)) (algebraMap R Γ(X, ⊤) r),
    GlobalTheory.restrictGlobal_top, hs]
  rfl

def secRes (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) : GlobalTheory.CechDR.Sec s U →ₗ[R] GlobalTheory.sectionsOn (GlobalTheory.structureModule X) W where
  toFun x := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (X.presheaf.map (homOfLE h).op (x : Γ(X, U)))
  map_add' x y := map_add (X.presheaf.map (homOfLE h).op).hom (x : Γ(X, U)) (y : Γ(X, U))
  map_smul' r x := by
    apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
    rw [RingHom.id_apply, GlobalTheory.sectionsOn.toΓ_smul, ← secMap_eq_restrictGlobal s hs W r]
    have e : (GlobalTheory.CechDR.secMap s W).hom r =
        X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r) :=
      (congrArg (fun q ↦ q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (s.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)).symm
    have key : ∀ y : Γ(X, U), X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r * y) =
        (GlobalTheory.CechDR.secMap s W).hom r * X.presheaf.map (homOfLE h).op y := fun y ↦ by
      rw [e]
      exact map_mul (X.presheaf.map (homOfLE h).op).hom _ y
    exact key x

private theorem sectionsOn_toΓ_secRes_eq_presheaf_map
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) (x : GlobalTheory.CechDR.Sec s U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W (secRes s hs h x) =
      X.presheaf.map (homOfLE h).op (x : Γ(X, U)) :=
  AddEquiv.apply_symm_apply _ _

theorem secRes_bijective
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W = U) : Function.Bijective (secRes s hs h.le) := by
  subst h
  have key : ∀ x : GlobalTheory.CechDR.Sec s W, secRes s hs (le_refl W) x =
      (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (x : Γ(X, W)) := by
    intro x
    have hx : X.presheaf.map (homOfLE (le_refl W)).op (x : Γ(X, W)) = (x : Γ(X, W)) := by
      change (X.presheaf.map (𝟙 (op W))) (x : Γ(X, W)) = x
      rw [X.presheaf.map_id]
      rfl
    exact congrArg (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm hx
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · rw [key, key] at hxy
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm.injective hxy
  · refine ⟨(show GlobalTheory.CechDR.Sec s W from GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W y), ?_⟩
    rw [key]
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm_apply_apply y

private theorem sectionsOn_toΓ_res_eq_presheaf_map {U V : X.Opens} (h : V ≤ U)
    (y : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) V (GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) h y) =
      (GlobalTheory.structureModule X).presheaf.map (homOfLE h).op (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) U y) :=
  GlobalTheory.WithAction.toBase_linearMap _ _ R _ _ y

theorem secRes_square
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U V V' W : X.Opens} (a : V ≤ U) (b : W ≤ V) (c : V' ≤ U) (d : W ≤ V') (x : GlobalTheory.CechDR.Sec s U) :
    secRes s hs b (GlobalTheory.CechDR.Sec.res s a x) =
      GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) d (secRes s hs c x) := by
  apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
  rw [sectionsOn_toΓ_secRes_eq_presheaf_map, sectionsOn_toΓ_res_eq_presheaf_map, sectionsOn_toΓ_secRes_eq_presheaf_map]
  change (X.presheaf.map (homOfLE b).op) ((X.presheaf.map (homOfLE a).op) (x : Γ(X, U))) =
    (X.presheaf.map (homOfLE d).op) ((X.presheaf.map (homOfLE c).op) (x : Γ(X, U)))
  have h1 : X.presheaf.map (homOfLE a).op ≫ X.presheaf.map (homOfLE b).op =
      X.presheaf.map (homOfLE c).op ≫ X.presheaf.map (homOfLE d).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun f : X.presheaf.obj (op U) ⟶ X.presheaf.obj (op W) => f (x : Γ(X, U))) h1

end

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]
  {P : Type} [SemilatticeInf P] (S : MainStatements.Hodge.Sys X P) {κ : Type} (e : κ → P)

theorem sys_inf' (t : Finset κ) (ht : t.Nonempty) :
    (S.u (t.inf' ht e)).1 = ⊤ ⊓ ⨅ i ∈ t, (S.u (e i)).1 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · rw [Finset.inf'_insert hs, S.map_inf, ih hs, Finset.iInf_insert]
      simp only [top_inf_eq]
    · obtain rfl : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp

variable (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))

def sysVertex (t : Finset κ) :
    (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t →ₗ[R]
      (GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1).obj t :=
  if ht : t.Nonempty then
    (secRes s hs (sys_inf' S e t ht).ge) ∘ₗ
      LinearMap.proj (R := R) (φ := fun h : PLift t.Nonempty ↦
        ((toMod (MainStatements.Hodge.OSys s S)).obj (op (t.inf' h.down e)) : Type)) ⟨ht⟩
  else 0

theorem sysVertex_apply (t : Finset κ) (ht : t.Nonempty) (x : (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t) :
    sysVertex s S e hs t x = secRes s hs (sys_inf' S e t ht).ge (x ⟨ht⟩) := by
  unfold sysVertex
  rw [dite_eq_left ht]
  rfl

theorem sysVertex_of_not_nonempty (t : Finset κ) (ht : ¬ t.Nonempty) : sysVertex s S e hs t = 0 := by
  unfold sysVertex
  rw [dite_eq_right ht]

theorem sysVertex_bijective (t : Finset κ) (ht : t.Nonempty) : Function.Bijective (sysVertex s S e hs t) := by
  have hf : ⇑(sysVertex s S e hs t) = (secRes s hs (sys_inf' S e t ht).ge) ∘ (fun x => x ⟨ht⟩) :=
    funext fun x => sysVertex_apply s S e hs t ht x
  rw [hf]
  refine (secRes_bijective s hs (sys_inf' S e t ht).symm).comp ⟨fun x y hxy => ?_, fun y => ?_⟩
  · funext h
    obtain ⟨h⟩ := h
    exact hxy
  · exact ⟨fun _ => y, rfl⟩

def sysCube : cubeOf e (toMod (MainStatements.Hodge.OSys s S)) ⟶
    GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1 :=
  GlobalTheory.Cube.homMk κ R (sysVertex s S e hs) fun {t t'} h x ↦ by
    by_cases ht : t.Nonempty
    · have ht' : t'.Nonempty := ht.mono h
      rw [sysVertex_apply s S e hs t' ht', sysVertex_apply s S e hs t ht]
      have e1 := cubeRes_apply e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
      refine (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans ?_
      exact secRes_square s hs _ _ _ _ (x ⟨ht⟩)
    · rw [sysVertex_of_not_nonempty s S e hs t ht, LinearMap.zero_apply, map_zero]
      by_cases ht' : t'.Nonempty
      · rw [sysVertex_apply s S e hs t' ht']
        have e1 := cubeRes_empty e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
        exact (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans (map_zero _)
      · rw [sysVertex_of_not_nonempty s S e hs t' ht', LinearMap.zero_apply]

theorem isIso_sysCube [LinearOrder κ] : IsIso (GlobalTheory.cechComplexMap (sysCube s S e hs)) := by
  apply GlobalTheory.isIso_cechComplexMap
  intro t ht
  rw [sysCube, GlobalTheory.Cube.homMk_app, ModuleCat.hom_ofHom]
  exact sysVertex_bijective s S e hs t ht

end

theorem cech_OSys_homology_equiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) := by
  intro R _ X s P _ S κ _ e n
  letI := GlobalTheory.algebraΓOfHom s
  have hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
    fun r => rfl
  haveI := isIso_sysCube s S e hs
  exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (asIso (GlobalTheory.cechComplexMap (sysCube s S e hs)))).toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyBaseChangeOfCochainEquivsStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_cohomology_base_change_of_cochain_equivs : ∀ (R R' C : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F') (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'), (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) → (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) → (∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x)) → (∀ x : R' ⊗[R] C1 F, (d1 F).lTensor R' x = 0 → ∃ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F), (Z1 F).subtype.lTensor R' t + (d0 F).lTensor R' y = x) → (∀ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F), (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' y → ∃ y' : R' ⊗[R] C0 F, ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)).lTensor R' y' = t) → ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  first | exact @GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange | exact GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange | (intros; apply GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange <;> assumption)
end

