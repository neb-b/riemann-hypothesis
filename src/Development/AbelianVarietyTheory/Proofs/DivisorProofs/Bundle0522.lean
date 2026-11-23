module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

abbrev Var (ι : Type) (d a : ℕ) : Type := ι × Fin d × Fin a

abbrev Pol (ι : Type) (d a : ℕ) : Type := MvPolynomial (Var ι d a) ℂ

abbrev Tup (ι : Type) (a d : ℕ) (n : ι → ℕ) : Type := ∀ τ, Fin (n τ) → {s : Fin a → Fin d // StrictMono s}

variable {ι : Type}

def minorAt (τ : ι) {a d : ℕ} (s : Fin a → Fin d) : Pol ι d a :=
  (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)).det

variable [Fintype ι]

def prodMinors {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : Pol ι d a := ∏ τ, ∏ j, minorAt τ (T τ j).1

def rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ i' : Fin d, C (κ y.1 i' y.2.1) * X (y.1, i', y.2.2)

def colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ j' : Fin a, C (g y.1 j' y.2.2) * X (y.1, y.2.1, j')

def detChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) : ℂ := ∏ τ, (g τ).det ^ n τ

def inv (a d : ℕ) (n : ι → ℕ) : Submodule ℂ (Pol ι d a) where
  carrier := {P | ∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
    colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P = detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • P}
  add_mem' := by
    intro P Q hP hQ g
    simp only [Set.mem_setOf_eq] at *
    rw [map_add (f := _), hP g, hQ g, smul_add]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c P hP g
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hP g, smul_comm]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem colSub_minorAt {a d : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (s : Fin a → Fin d) :
    colSub g (minorAt τ s) = (g τ).det • minorAt τ s := by
  unfold minorAt
  rw [AlgHom.map_det]
  have hM : (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).mapMatrix (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) =
      (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) * (g τ).map C := by
    ext i i'
    simp [colSub, Matrix.mul_apply, mul_comm]
  rw [hM, Matrix.det_mul, show ((g τ).map C).det = C (g τ).det from ((C : ℂ →+* Pol ι d a).map_det (g τ)).symm, smul_eq_C_mul, mul_comm]

theorem colSub_prodMinors {a d : ℕ} {n : ι → ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (T : Tup ι a d n) :
    colSub g (prodMinors T) = detChar n g • prodMinors T := by
  unfold prodMinors detChar
  simp only [map_prod, colSub_minorAt, smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, map_prod, map_pow]

theorem prodMinors_mem_inv {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : prodMinors T ∈ inv a d n :=
  fun g => colSub_prodMinors _ T

theorem colSub_rowSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    colSub g (rowSub κ P) = rowSub κ (colSub g P) := by
  have : (colSub g).comp (rowSub κ) = (rowSub κ).comp (colSub g) := by
    apply MvPolynomial.algHom_ext
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowSub, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_mem_inv {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) {P : Pol ι d a} (hP : P ∈ inv a d n) :
    rowSub κ P ∈ inv a d n := by
  intro g
  rw [colSub_rowSub, hP g, map_smul]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

open Classical

variable {ι : Type} [Fintype ι]

theorem fockS_conj {σ : Type} (f g : MvPolynomial σ ℂ) :
    Formalism.L2.DIV.fockS f g = starRingEnd ℂ (Formalism.L2.DIV.fockS g f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.L2.DIV.fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, RCLike.star_def, Complex.conj_conj]
  ring

theorem fockS_self_re_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.L2.DIV.fockS f f).re := by
  unfold Formalism.L2.DIV.fockS
  rw [Complex.re_sum]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hf
  have hms : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have key : ∀ k ∈ f.support, (star (f.coeff k) * f.coeff k * (Formalism.L2.DIV.mfact k : ℂ)).re =
      ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ) := by
    intro k _
    rw [RCLike.star_def, mul_comm (starRingEnd ℂ _), Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl key]
  have hpos : 0 < ‖f.coeff m‖ ^ 2 * (Formalism.L2.DIV.mfact m : ℝ) := by
    have : (0 : ℝ) < Formalism.L2.DIV.mfact m := by
      unfold Formalism.L2.DIV.mfact; exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ))
    (fun k _ => by positivity) hms)

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullColIsoPbfMap
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg
variable (R : Type) [CommRing R]
open GlobalTheory.EtC.DiscChains

def colCx (X : SimplicialObject Spc) (a : ℕ) :
    (biChains R X).X (-(a : ℤ)) ≅ (chains R).obj (X.obj (op (SimplexCategory.mk a))) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapIso (Iso.refl _)

theorem colCx_f (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X a b).inv ≫ (colCx R X a).hom.f (-(b : ℤ)) =
      (chainsXIso R (X.obj (op (SimplexCategory.mk a))) b).inv := by
  have h1 := (HomologicalComplex.extendXIso (((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj ((dblF R).obj ((freeBi R).obj X))) ComplexShape.embeddingDownNat (i := a) (i' := -(a:ℤ)) rfl).inv_hom_id
  have h2 := congrArg (fun f => HomologicalComplex.Hom.f f (-(b:ℤ))) h1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h2
  erw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.trans_inv]
  erw [Category.assoc, reassoc_of% h2]
  erw [Functor.mapIso_refl, Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
  rfl

def prE (E : Spc) (a : ℕ) : (chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))) ⟶
    sgl (((chains R).obj E).X (-(a : ℤ))) :=
  (he R _).inv ≫ (CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv

def prEquiv (E : Spc) (a : ℕ) : HomotopyEquiv ((chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))))
    (sgl (((chains R).obj E).X (-(a : ℤ)))) :=
  (he R _).symm.trans (HomotopyEquiv.ofIso ((CochainComplex.singleFunctor (Shv R) 0).mapIso (chainsXIso R E a).symm))

theorem prE_zero (E : Spc) (a : ℕ) :
    (chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
  set P := E.obj (op (SimplexCategory.mk a))
  have hφψ : (he R P).hom.f 0 ≫ (he R P).inv.f 0 = 𝟙 _ := by
    have hc := (he R P).homotopyHomInvId.comm 0
    have hz1 : IsZero ((sgl ((free R).obj P)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    have hzm : IsZero ((sgl ((free R).obj P)).X (-1)) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp), prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      hz1.eq_of_tgt ((sgl ((free R).obj P)).d 0 1) 0, hzm.eq_of_tgt ((he R P).homotopyHomInvId.hom 0 (-1)) 0] at hc
    simp at hc
    exact hc
  have hinv0 : (chainsXIso R (disc.obj P) 0).inv ≫ (he R P).inv.f 0 = sglι ((free R).obj P) := by
    rw [← he_hom_f_zero R P, Category.assoc, hφψ, Category.comp_id]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (chainsXIso R E a).inv).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [prE, HomologicalComplex.comp_f, ← Category.assoc, hinv0, h1]

theorem mk_sum_cocycle {K L : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι) (γ : ι → Cocycle K L n) :
    ∑ j ∈ s, CohomologyClass.mk (γ j) = CohomologyClass.mk (∑ j ∈ s, γ j) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (CohomologyClass.mk_zero (K := K) (L := L) (n := n)).symm
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, CohomologyClass.mk_add]

theorem pull_colIso_pbfMap (q : ℕ) [NeZero q] (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N))
    (hP : Inv q (disc.obj P)) (m i : ℤ) (x : ∀ j : Fin N, Ht q (disc.obj P) (m - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (colIso P V₀).hom _ m (pbfMap q V₀ m i x) =
      ∑ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _ (x j))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) := by
  unfold pbfMap
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast, (a6nat_holds q).1, ← pull_comp, colIso_hom_fst, pull_cpow q a6nat_holds _ (inv_pullback_pgl q V₀ hP),
    (a6nat_holds q).2.2.1 _ _ (inv_pullback_pgl q V₀ hP), colIso_line]

theorem ev_prE_pos (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (s : ℕ) (t : ℤ) (h : -(s : ℤ) + d = t) (U : Scheme.{0})
    (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) s U) (hs : 0 < s) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) s t h U x = 0 := by
  have hz : IsZero ((sgl (((chains R).obj E).X (-(a : ℤ)))).X (-(s : ℤ))) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (-(s : ℤ)) (by omega)
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, hz.eq_of_src (c.v (-(s : ℤ)) t h) 0, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U x))

theorem ev_prE_zero (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (t : ℤ) (h : -((0 : ℕ) : ℤ) + d = t) (U : Scheme.{0}) (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0 U) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) 0 t h U x =
      Sec.map ((chainsXIso R E a).inv ≫ sglι _ ≫ c.v 0 t (by simpa using h)) (freeGen R _ U x) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change Sec.map ((chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 ≫ c.v 0 t _) _ = _
  rw [reassoc_of% prE_zero R E a]
  rfl

end GlobalTheory.PBFg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurAndTensorSubmodule
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.IrrTensor

section General
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (A : ι → Module.End ℂ V)

theorem density [Nontrivial V]
    (hirr : ∀ N : Submodule ℂ V, (∀ Z, ∀ y ∈ N, A Z y ∈ N) → N = ⊥ ∨ N = ⊤)
    (hsch : ∀ T : V →ₗ[ℂ] V, (∀ Z, T ∘ₗ A Z = A Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id)
    (f : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ m ∈ s, f m = r m := by
  let R := Algebra.adjoin ℂ (Set.range A)
  have hA : ∀ Z, A Z ∈ R := fun Z => Algebra.subset_adjoin ⟨Z, rfl⟩
  haveI : IsSimpleModule R V := by
    refine (isSimpleModule_iff R V).2 ?_
    refine { toNontrivial := (Submodule.nontrivial_iff R).2 inferInstance, eq_bot_or_eq_top := fun N => ?_ }
    rcases hirr (N.restrictScalars ℂ) (fun Z y hy => N.smul_mem (⟨A Z, hA Z⟩ : R) hy) with h | h
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  let F : Module.End (Module.End R V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g x => by
        obtain ⟨c, hc⟩ := hsch (g.restrictScalars ℂ) (fun Z => LinearMap.ext fun y =>
          g.map_smul (⟨A Z, hA Z⟩ : R) y)
        have hg : ∀ y, g y = c • y := fun y => LinearMap.congr_fun hc y
        show f (g x) = g (f x)
        rw [hg, hg, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density (R := R) F s
  exact ⟨r.1, r.2, fun m hm => hr m hm⟩

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end General

variable {p q : ℕ}

theorem mem_wtSub {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} : v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem root_shift {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (hl : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : v ∈ wtSub act μ) (a b : Ix p q) :
    act (Eab a b) v ∈ wtSub act (fun c => μ c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wtSub] at hv ⊢
  intro c
  have h := LinearMap.congr_fun (hl (Eab c c) (Eab a b)) v
  have e : (Eab c c * Eab a b - Eab a b * Eab c c : Mat p q) =
      (((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) : ℂ) • Eab a b := by
    unfold Eab
    have e1 : (Matrix.single c c 1 * Matrix.single a b 1 : Mat p q) =
        (if c = a then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, h]
    have e2 : (Matrix.single a b 1 * Matrix.single c c 1 : Mat p q) =
        (if c = b then (1 : ℂ) else 0) • Matrix.single a b 1 := by
      split_ifs with h
      · subst h; simp
      · simp [Matrix.single_mul_single_of_ne, Ne.symm h]
    rw [e1, e2, ← sub_smul]
    congr 1
    split_ifs <;> simp
  rw [e, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, hv c, map_smul, eq_sub_iff_add_eq] at h
  rw [← h, Rat.cast_add, add_smul, add_comm]

theorem exists_highest (M : GKMod p q) [Nontrivial M.V] : ∃ μ v, IsHW M.act μ v := by
  obtain ⟨μ₀, v₀, hv₀, hv₀'⟩ : ∃ μ v, v ∈ wtSub M.act μ ∧ v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (0 : M.V)
    have : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) = ⊥ :=
      iSup_eq_bot.2 fun μ => (Submodule.eq_bot_iff _).2 (h μ)
    have h2 := M.wts x
    rw [this] at h2
    exact hx h2
  obtain ⟨U, hfd, hU, hK⟩ := M.kfin v₀
  let k : Ix p q → ℚ := Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun i => -((i : ℕ) : ℚ))
  let h : (Ix p q → ℚ) → ℚ := fun μ => ∑ a, k a * μ a
  let H : Mat p q := ∑ a, ((k a : ℚ) : ℂ) • Eab a a
  have hKE : ∀ a b : Ix p q, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    unfold Eab
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd hab
  have hH : ∀ x ∈ U, M.act H x ∈ U := by
    intro x hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact U.sum_mem fun a _ => U.smul_mem _ (hK _ (hKE a a (by cases a <;> trivial)) x hx)
  let S : Set (Ix p q → ℚ) := {μ | ∃ v ∈ U, v ∈ wtSub M.act μ ∧ v ≠ 0}
  have hfin : (h '' S).Finite := by
    have h1 := Module.End.finite_hasEigenvalue ((M.act H).restrict hH)
    refine (h1.preimage (f := fun x : ℚ => (x : ℂ)) Rat.cast_injective.injOn).subset ?_
    rintro _ ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvU⟩) ⟨?_, fun e => hv0 (congrArg Subtype.val e)⟩
    rw [Module.End.mem_eigenspace_iff]
    apply Subtype.ext
    show M.act H v = ((h μ : ℚ) : ℂ) • v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      mem_wtSub.1 hv, smul_smul, ← Finset.sum_smul]
    push_cast
    rfl
  obtain ⟨_, ⟨μ, ⟨v, hvU, hv, hv0⟩, rfl⟩, hmax⟩ :=
    Set.exists_max_image (h '' S) id hfin ⟨_, μ₀, ⟨v₀, hU, hv₀, hv₀'⟩, rfl⟩
  refine ⟨μ, v, hv0, hv, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a b hab
  by_contra hne
  have hs : sameBlock a b := by cases a <;> cases b <;> first | trivial | exact hab
  have hlt : k b < k a := by
    cases a <;> cases b <;> first | exact hab.elim | skip
    all_goals
      simp only [k, Sum.elim_inl, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      exact hab
  have := hmax _ ⟨_, ⟨_, hK _ (hKE a b hs) v hvU, root_shift M.lie hv a b, hne⟩, rfl⟩
  simp only [id, h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

theorem schur (M : GKMod p q) (hI : IrrGK M) (hA : AdmGK M) (T : M.V →ₗ[ℂ] M.V)
    (hT : ∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) : ∃ c : ℂ, T = c • LinearMap.id := by
  haveI := hI.1
  obtain ⟨μ, v, hv0, hv⟩ := exists_highest M
  have hf : ∀ Z x, T (M.act Z x) = M.act Z (T x) := fun Z x => LinearMap.congr_fun (hT Z) x
  have hst : ∀ x ∈ hwSub M.act μ, T x ∈ hwSub M.act μ := by
    intro x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    refine ⟨fun c => ?_, fun c d h => ?_⟩
    · rw [← hf, ← map_smul, ← map_sub, hx.1 c, map_zero]
    · rw [← hf, hx.2 c d h, map_zero]
  haveI := hA μ
  haveI : Nontrivial (hwSub M.act μ) := ⟨⟨⟨v, hv⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hst)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx1 : T x = c • (x : M.V) := congrArg Subtype.val hx.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hI.2 (LinearMap.ker (T - c • LinearMap.id)) (fun Z y hy => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hy ⊢
    rw [hf, hy, map_smul]) with h | h
  · exact absurd (Subtype.ext ((Submodule.eq_bot_iff _).1 h x (by simp [hx1]))) hx.2
  · exact sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)

end GlobalTheory.IrrTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sectionComponents_preimage_of_isPullback :
    ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X)
      (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ →
      e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e →
      q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} =
        {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  intro X S X' S' f f' p q e e' hf hq he he' hee
  ext x'
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hfq : f (q x') = p (f' x') := by
    rw [← Scheme.Hom.comp_apply, hq.w, Scheme.Hom.comp_apply]
  rw [hfq]

  have hY := IsPullback.of_hasPullback f (S.fromSpecResidueField (p (f' x')))
  have hY' := IsPullback.of_hasPullback f' (S'.fromSpecResidueField (f' x'))
  have hsq : S'.fromSpecResidueField (f' x') ≫ p =
      Spec.map (p.residueFieldMap (f' x')) ≫ S.fromSpecResidueField (p (f' x')) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p (f' x')).symm

  let eY : Spec (S.residueField (p (f' x'))) ⟶ pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (S.fromSpecResidueField (p (f' x')) ≫ e) (𝟙 _) (by simp [he])
  let eY' : Spec (S'.residueField (f' x')) ⟶ pullback f' (S'.fromSpecResidueField (f' x')) :=
    pullback.lift (S'.fromSpecResidueField (f' x') ≫ e') (𝟙 _) (by simp [he'])

  let r : pullback f' (S'.fromSpecResidueField (f' x')) ⟶
      pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ Spec.map (p.residueFieldMap (f' x')))
      (by simp only [Category.assoc]; rw [hq.w, ← Category.assoc, pullback.condition, Category.assoc, hsq])
  have hbig := hY'.paste_horiz hq
  have hr : IsPullback r (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (p.residueFieldMap (f' x'))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hY
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    rw [h1, ← hsq]
    exact hbig
  have hsec : eY ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hsec' : eY' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hcomm : eY' ≫ r = Spec.map (p.residueFieldMap (f' x')) ≫ eY := by
    apply pullback.hom_ext
    · simp only [r, eY, eY', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [hee, reassoc_of% hsq]
    · simp only [r, eY, eY', Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
  have hsm : Smooth (pullback.snd f (S.fromSpecResidueField (p (f' x')))) := inferInstance
  have key := _root_.GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange (S.residueField (p (f' x'))) (S'.residueField (f' x')) _ _
    (pullback.snd _ _) (pullback.snd _ _) (Spec.map (p.residueFieldMap (f' x'))) r eY eY'
    hsm hr hsec hsec' hcomm

  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f') (g := S'.fromSpecResidueField (f' x')) x' (IsLocalRing.closedPoint _)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have hy₀ : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (eY (IsLocalRing.closedPoint _)) =
      e (p (f' x')) := by
    have h1 : eY ≫ pullback.fst _ _ = S.fromSpecResidueField (p (f' x')) ≫ e := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e (Scheme.fromSpecResidueField_apply _ _))
  have hy₀' : pullback.fst f' (S'.fromSpecResidueField (f' x')) (eY' (IsLocalRing.closedPoint _)) =
      e' (f' x') := by
    have h1 : eY' ≫ pullback.fst _ _ = S'.fromSpecResidueField (f' x') ≫ e' := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY' (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e' (Scheme.fromSpecResidueField_apply _ _))
  have hqx : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (r y') = q x' := by
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply r (pullback.fst _ _) _).symm.trans ?_
    rw [h1, Scheme.Hom.comp_apply, hy'1]
  have A := _root_.GlobalTheory.component_in_fibre_iff_of_isPullback X S f e (p (f' x')) _ (pullback.snd _ _) (pullback.fst _ _) _ hY hy₀ (r y')
  have B := _root_.GlobalTheory.component_in_fibre_iff_of_isPullback X' S' f' e' (f' x') _ (pullback.snd _ _) (pullback.fst _ _) _ hY' hy₀' y'
  rw [hqx] at A
  rw [hy'1] at B
  rw [A, B, ← key]
  rfl

end GlobalTheory
end

