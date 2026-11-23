module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedCechAcyclic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type}

abbrev BV (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) : Type :=
  ∀ _ : PLift (∀ j ∈ s, b ≤ e j), M b

def bRes (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s t : Finset κ} (h : s ⊆ t) :
    BV e M b s →ₗ[R] BV e M b t where
  toFun x ht := x ⟨fun j hj ↦ ht.down j (h hj)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cubeB (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : Cube.{0} κ R :=
  Cube.mk (fun s ↦ ModuleCat.of R (BV e M b s)) (fun h ↦ bRes e M b h) (fun _ _ ↦ rfl)
    (fun _ _ _ ↦ rfl)

theorem cubeB_bijective [DecidableEq κ] (e : κ → P) (M : P → ModuleCat.{0} R) {b : P} {i : κ} (hi : e i = b)
    (s : Finset κ) (_his : i ∉ s) :
    Function.Bijective (Cube.res (cubeB e M b) (Finset.subset_insert i s)) := by
  have key : ∀ hs : PLift (∀ j ∈ s, b ≤ e j), ∀ j ∈ insert i s, b ≤ e j := fun hs j hj ↦ by
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hi.ge
    · exact hs.down j hj
  constructor
  · intro x y h
    exact funext fun hs ↦ congrFun h ⟨key hs⟩
  · intro y
    exact ⟨fun hs ↦ (show BV e M b (insert i s) from y) ⟨key hs⟩, rfl⟩

abbrev AV (e : κ → P) (M : P → ModuleCat.{0} R) (s : Finset κ) : Type :=
  ∀ hs : PLift s.Nonempty, ∀ b : {b : P // b ≤ s.inf' hs.down e}, M b.1

def prj (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) :
    (cubeOf e (coind M)).obj s →ₗ[R] (cubeB e M b).obj s where
  toFun x := fun h ↦ if hs : s.Nonempty then
    (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ else 0
  map_add' x y := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; exact (add_zero _).symm
  map_smul' r x := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; show (0 : M b) = r • (0 : M b); exact (smul_zero r).symm

theorem prj_apply (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) (h : PLift (∀ j ∈ s, b ≤ e j)) :
    (show BV e M b s from prj e M b s x) h =
      (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ :=
  dif_pos hs

theorem prj_empty (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : ¬ s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) : prj e M b s x = 0 :=
  funext fun _ ↦ dif_neg hs

def prjHom (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : cubeOf e (coind M) ⟶ cubeB e M b :=
  Cube.homMk κ R (prj e M b) fun {s t} h x ↦ by
    by_cases hs : s.Nonempty
    · refine funext fun ht ↦ ?_
      have hs' : t.Nonempty := hs.mono h
      refine (prj_apply e M b hs' _ ht).trans ?_
      refine Eq.trans ?_ (prj_apply e M b hs x ⟨fun j hj ↦ ht.down j (h hj)⟩).symm
      have := cubeRes_apply e (coind M) h x hs ⟨hs'⟩
      exact congrFun this _
    · rw [prj_empty e M b hs, map_zero]
      by_cases ht : t.Nonempty
      · refine funext fun hh ↦ ?_
        refine (prj_apply e M b ht _ hh).trans ?_
        have := cubeRes_empty e (coind M) h x hs ⟨ht⟩
        exact congrFun this _
      · exact prj_empty e M b ht _

theorem term_ext (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (u v : Cube.Term (cubeOf e (coind M)) (q + 1))
    (h : ∀ b, Cube.termMap (prjHom e M b) (q + 1) u = Cube.termMap (prjHom e M b) (q + 1) v) :
    u = v := by
  funext s
  refine funext fun hs ↦ funext fun b ↦ ?_
  have hle : ∀ j ∈ s.1, b.1 ≤ e j := fun j hj ↦ b.2.trans (Finset.inf'_le e hj)
  have h1 := congrFun (congrFun (h b.1) s) ⟨hle⟩
  exact (prj_apply e M b.1 hs.down (u s) ⟨hle⟩).symm.trans (h1.trans (prj_apply e M b.1 hs.down (v s) ⟨hle⟩))

def asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ} (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) :
    Cube.Term (cubeOf e (coind M)) (q + 1) :=
  fun s ↦ (show AV e M s.1 from fun _ b ↦
    (show BV e M b.1 s.1 from y b.1 s) ⟨fun _ hj ↦ b.2.trans (Finset.inf'_le e hj)⟩)

theorem termMap_asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) (b : P) :
    Cube.termMap (prjHom e M b) (q + 1) (asm e M y) = y b := by
  funext s
  refine funext fun h ↦ ?_
  have hs : s.1.Nonempty := Finset.card_pos.1 (by have := s.2; omega)
  exact prj_apply e M b hs (asm e M y s) h

variable [LinearOrder κ]

theorem exact_d (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (p : ℕ) :
    Function.Exact (Cube.d (cubeOf e (coind M)) (p + 1)) (Cube.d (cubeOf e (coind M)) (p + 2)) := by
  intro x
  refine ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact Cube.d_d _ _ y⟩
  have hb : ∀ b, ∃ y : Cube.Term (cubeB e M b) (p + 1),
      Cube.d (cubeB e M b) (p + 1) y = Cube.termMap (prjHom e M b) (p + 2) x := by
    intro b
    obtain ⟨i, hi⟩ := he b
    refine (Cube.exact_d_of_bijective (cubeB e M b) i (cubeB_bijective e M hi) (p + 1) _).1 ?_
    rw [← Cube.termMap_d, hx, map_zero]
  choose y hy using hb
  refine ⟨asm e M y, term_ext e M _ _ fun b ↦ ?_⟩
  rw [Cube.termMap_d, termMap_asm, hy]

theorem isZero_homology (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (n : ℕ) :
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff (cubeOf e (coind M)) n).2 (exact_d e he M n))

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedNerveAcyclic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]

theorem chain_ext {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : ∀ i, c.obj i = c'.obj i) : c = c' :=
  CategoryTheory.Functor.ext h (fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

theorem chain_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {i j : Fin (n + 1)} (h : i ≤ j) :
    (c.obj j).unop ≤ (c.obj i).unop :=
  leOfHom (c.map (homOfLE h)).unop

def snocObj {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) : Fin (n + 2) → Pᵒᵖ :=
  Fin.snoc (α := fun _ ↦ Pᵒᵖ) (fun i ↦ c.obj i) (op b)

@[simp] theorem snocObj_last {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) :
    snocObj c b (Fin.last _) = op b :=
  Fin.snoc_last (α := fun _ ↦ Pᵒᵖ) _ _

@[simp] theorem snocObj_castSucc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (i : Fin (n + 1)) :
    snocObj c b i.castSucc = c.obj i :=
  Fin.snoc_castSucc (α := fun _ ↦ Pᵒᵖ) _ _ _

theorem snocObj_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P} (hb : b ≤ (c.obj (Fin.last n)).unop)
    {i j : Fin (n + 2)} (h : i ≤ j) : (snocObj c b j).unop ≤ (snocObj c b i).unop := by
  induction j using Fin.lastCases with
  | last =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
    induction i using Fin.lastCases with
    | last => exact le_of_eq (by rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last])
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last i))
  | cast j =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    induction i using Fin.lastCases with
    | last => exact absurd h (not_le.mpr (Fin.castSucc_lt_last j))
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.castSucc_le_castSucc_iff.mp h)

def snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    Fin (n + 2) ⥤ Pᵒᵖ where
  obj := snocObj c b
  map h := (homOfLE (snocObj_anti c hb (leOfHom h))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem snoc_last_le {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    b ≤ ((snoc c b hb).obj (Fin.last _)).unop :=
  le_of_eq (congrArg Opposite.unop (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last c b)).symm

abbrev face {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) : Fin (n + 1) ⥤ Pᵒᵖ :=
  (Fin.succAboveOrderEmb i).toOrderHom.monotone.functor ⋙ c

theorem face_le {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : b ≤ ((face i c).obj (Fin.last _)).unop :=
  hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last _))

theorem face_castSucc_snoc {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) :
    face i.castSucc (snoc c b hb) = snoc (face i c) b (face_le i c hb) := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  induction k using Fin.lastCases with
  | last =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.last _)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.last _)
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)),
      Fin.succ_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
  | cast k =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.castSucc k)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.castSucc k)
    rw [Fin.castSucc_succAbove_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    all_goals rfl

theorem face_last_snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : face (Fin.last _) (snoc c b hb) = c := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.last _).succAbove k) = c.obj k
  rw [Fin.succAbove_last_apply, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]

def valL (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) : NC (coind M) n →ₗ[R] M b where
  toFun f := f c ⟨b, hb⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valL_congr (M : P → ModuleCat.{0} R) {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : c = c') (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) (hb' : b ≤ (c'.obj (Fin.last n)).unop) (f : NC (coind M) n) :
    valL M c b hb f = valL M c' b hb' f := by
  subst h
  rfl

theorem valL_dNC (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 2) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last _)).unop) (f : NC (coind M) n) :
    valL M c b hb (dNC (coind M) n f) =
      ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • valL M (face i c) b (face_le i c hb) f := by
  first
    | (simp only [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul];
        all_goals exact Finset.sum_congr rfl fun i _ => rfl)
    | (rw [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, map_sum];
        exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, map_smul]; rfl)

def contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) : NC (coind M) n :=
  fun c b ↦ valL M (snoc c b.1 b.2) b.1 (snoc_last_le c b.1 b.2) f

theorem valL_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) :
    valL M c b hb (contr M f) = valL M (snoc c b hb) b (snoc_last_le c b hb) f := rfl

theorem NC_ext (M : P → ModuleCat.{0} R) {n : ℕ} {f g : NC (coind M) n}
    (h : ∀ c b hb, valL M c b hb f = valL M c b hb g) : f = g := by
  funext c b
  exact h c b.1 b.2

theorem dNC_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1))
    (hf : dNC (coind M) (n + 1) f = 0) :
    dNC (coind M) n (((-1 : R) ^ (n + 1)) • contr M f) = f := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.NC_ext
  intro c b hb
  have hcoc : GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc c b hb) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc_last_le c b hb)
      (GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) f) = 0 := by
    rw [hf, map_zero]
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, Fin.sum_univ_castSucc] at hcoc
  have hsum : ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_le i c hb)
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M f) =
      -((-1 : R) ^ (n + 1 + 1) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M c b hb f) := by
    rw [eq_neg_iff_add_eq_zero, ← hcoc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_contr]
      exact congrArg ((-1 : R) ^ (i : ℕ) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_castSucc_snoc i c hb).symm b _ _ f)
    · rw [Fin.val_last]
      exact congrArg ((-1 : R) ^ (n + 1 + 1) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_last_snoc c hb).symm b _ _ f)
  have hp : (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [map_smul, map_smul, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, hsum, smul_neg, smul_smul,
    pow_succ (-1 : R) (n + 1), ← mul_assoc, hp, one_mul, neg_smul, one_smul, neg_neg]

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc


open GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc in
theorem GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (M : P → ModuleCat.{0} R) (n : ℕ) : IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) x = 0 := by
    change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d (n + 1) (n + 1 + 1)).hom x = 0 at hx
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d] at hx
    exact hx
  refine ⟨((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x, ?_⟩
  change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d n (n + 1)).hom
    (((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x) = x
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d]
  exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.dNC_contr M x hx'
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
open scoped TensorProduct
open GlobalTheory.TopForm

def allE (n d : ℕ) : Gam n d := ∑ e, oneE e

theorem allE_apply {n d : ℕ} (e : E n d) : allE n d e = 1 := by
  classical
  simp [allE, oneE, Finset.sum_apply, Pi.single_apply]

theorem allE_mem {n d : ℕ} (S : Finset (Fin d)) : allE n d ∈ (cone S : AddSubmonoid (Gam n d)) :=
  sum_mem fun e _ => oneE_mem S e

theorem exists_add_nsmul_mem {n d : ℕ} (S : Finset (Fin d)) (g : Gam n d) :
    ∃ N : ℕ, g + N • allE n d ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨(∑ e, |g e|).toNat, ?_⟩
  have hall : ∀ e, 0 ≤ (g + (∑ e, |g e|).toNat • allE n d) e := by
    intro e
    have h1 : |g e| ≤ ∑ e, |g e| :=
      Finset.single_le_sum (f := fun e => |g e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
    have h2 : ((∑ e, |g e|).toNat : ℤ) = ∑ e, |g e| :=
      Int.toNat_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have h3 := neg_abs_le (g e)
    rw [Pi.add_apply, Pi.smul_apply, allE_apply, nsmul_eq_mul, mul_one, h2]
    linarith
  exact ⟨fun _ => hall _, fun _ _ => hall _, Finset.sum_nonneg fun _ _ => hall _⟩

theorem injective_of_isBaseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {f : M →ₗ[A] N} (hf : IsBaseChange B f)
    (hinj : Function.Injective (algebraMap A B)) : Function.Injective f := by
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap A B) hinj
  intro x y hxy
  have h3 : (1 : B) ⊗ₜ[A] x = (1 : B) ⊗ₜ[A] y := by
    apply hf.equiv.injective
    simp [IsBaseChange.equiv_tmul, hxy]
  have h4 : (1 : A) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] y := by
    apply h2
    simpa using h3
  simpa using congrArg (TensorProduct.lid A M) h4

theorem omMap_incl_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ),
    Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  intro K _ n d S a
  letI : Algebra (R0 K n d S) (Lr K n d) :=
    (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d S) (Lr K n d) :=
    IsScalarTower.of_algHom (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤))
  haveI hl : IsLocalization.Away (mon K (allE n d) (allE_mem S)) (Lr K n d) :=
    Away.isLocalization_away le_top (allE n d) (allE_mem S) (AddSubmonoid.mem_top _)
      (fun g _ => exists_add_nsmul_mem S g)
  haveI : Algebra.FormallyEtale (R0 K n d S) (Lr K n d) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (allE n d) (allE_mem S)))
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale K (R0 K n d S) (Lr K n d)
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hb a
  haveI : Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := _root_.GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om S
  have hinj := injective_of_isBaseChange hE (Away.incl_injective le_top)
  have heq : ∀ ω, omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a ω =
      exteriorPowerMapOver (Lr K n d) a (KaehlerDifferential.map K K (R0 K n d S) (Lr K n d)) ω := by
    intro ω
    have hs : ω ∈ (⊤ : Submodule (R0 K n d S) (Om K (R0 K n d S) a)) := trivial
    rw [← exteriorPower.ιMulti_span] at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [omMap_ιMulti, exteriorPowerMapOver_ιMulti]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [omMap_smul, hx, map_smul]
      exact algebraMap_smul (Lr K n d) c _
  intro x y hxy
  exact hinj (by rw [← heq, ← heq, hxy])

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLinearInFunctional
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem con_add_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (Ξ Ξ' : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (Ξ + Ξ') u = con V M Ξ u + con V M Ξ' u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (Ξ + Ξ') u = GlobalTheory.CompanionTheory.HopfC.con V M Ξ u + GlobalTheory.CompanionTheory.HopfC.con V M Ξ' u)
    ?_ ?_ ?_ u
  · simp only [map_zero, add_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.add_apply, add_smul]
  · intro u v hu hv
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
    abel

theorem con_smul_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (r : R) (Ξ : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (r • Ξ) u = r • con V M Ξ u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (r • Ξ) u = r • GlobalTheory.CompanionTheory.HopfC.con V M Ξ u)
    ?_ ?_ ?_ u
  · simp only [map_zero, smul_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.smul_apply, smul_eq_mul, mul_smul]
  · intro u v hu hv
    rw [map_add (f := _), map_add (f := _), hu, hv, smul_add]

theorem Con_linear_form {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ Ξ' : Cn F p →ₗ[R] R) (r : R) (B : Bi F p q) :
    Con F (Ξ + Ξ') q B = Con F Ξ q B + Con F Ξ' q B ∧ Con F (r • Ξ) q B = r • Con F Ξ q B := by
  have key : ∀ (Θ : MainStatements.Hodge.Cn F p →ₗ[R] R) (b : Fin (q + 1) ⥤ C),
      GlobalTheory.CompanionTheory.HopfC.Con F Θ q B b =
        GlobalTheory.CompanionTheory.HopfC.con (fun a : Fin (p + 1) ⥤ C => (F.obj (a.obj (Fin.last p)) : Type))
          (F.obj (b.obj (Fin.last q)) : Type) Θ (fun a => B a b) := fun _ _ => rfl
  refine ⟨funext fun b => ?_, funext fun b => ?_⟩
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_add_form]
    rfl
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_smul_form]
    rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZero
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem pr_eq_zero_of_degenerate :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {m : ℕ} (x : Cn F 1)
      (_ : dn F 1 x = 0) (e : Fin (1 + 1) →o Fin (m + 1)) (_ : e 0 = e 1), pr F e x = 0 := by
  intro R _ C _ F m x hx e h01
  have key : ∀ i : Fin (1 + 1 + 1),
      GlobalTheory.CompanionTheory.HopfC.pr F ((GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0)).comp (GlobalTheory.CompanionTheory.HopfC.dl i)) x =
        GlobalTheory.CompanionTheory.HopfC.pr F e x := by
    intro i
    refine GlobalTheory.CompanionTheory.HopfC.pr_congr (fun j => ?_) x
    show e 0 = e j
    fin_cases j
    · rfl
    · exact h01
  have h := congrArg (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))) hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))),
    GlobalTheory.CompanionTheory.HopfC.dn_eq, map_sum] at h
  simp only [map_smul, map_zsmul, GlobalTheory.CompanionTheory.HopfC.pr_pr] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, key] at h
  norm_num at h
  exact h

end GlobalTheory.CompanionTheory.HopfC
end

