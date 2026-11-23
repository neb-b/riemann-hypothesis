module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsStrictlyLE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerPullbackSectionExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.QuotSec

variable {X : Scheme.{0}}

abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (s : Γ(X, U)) :
    rs h' (rs h s) = rs (h'.trans h) s := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem coe_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = rs h (u : Γ(X, U)) := rfl

theorem rs_coe_inv {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    rs h ((u⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (((res h u)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := by
  rw [← map_inv]; rfl

theorem res_g_self (L : LB X) (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i ⊓ L.U i) :
    res h (L.g i i) = 1 := by
  apply Units.ext
  rw [coe_res, ← rs_rs (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (h.trans inf_le_left), ← coe_res,
    hL.g_self]
  simp

def GenRel (P Q : LB X) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Prop :=
  ∀ p₁ q p₁' q', res (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q) (a p₁ q) =
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁ ⊓ P.U p₁') (P.g p₁ p₁') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ Q.U q ⊓ Q.U q') (Q.g q q'))⁻¹ *
      res (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q') ≤ P.U p₁' ⊓ Q.U q') (a p₁' q')

theorem genRel_of_isGen (P Q : LB X) (α : LB.Gen (LB.div P Q)) (hα : α.IsGen) :
    GenRel P Q (fun p₁ q => α.s (p₁, q)) :=
  fun p₁ q p₁' q' => hα (p₁, q) (p₁', q')

theorem quot_compat (P Q : LB X) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ) (ha : GenRel P Q a)
    (σ : LB.Sec P) (q : Q.ι) (p₁ p₁' : P.ι) :
    rs (inf_le_left : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ Q.U q)
      ((((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁)) =
    rs (inf_le_right : (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁' ⊓ Q.U q)
      ((((a p₁' q)⁻¹ : Γ(X, P.U p₁' ⊓ Q.U q)ˣ) : Γ(X, P.U p₁' ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁' ⊓ Q.U q ≤ P.U p₁') (σ.f p₁')) := by
  have e := ha p₁ q p₁' q
  rw [res_g_self Q hQ q, inv_one, _root_.mul_one] at e
  have hσ := congrArg (rs (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁' ⊓ Q.U q) ≤ P.U p₁ ⊓ P.U p₁')) (σ.compat p₁ p₁')
  simp only [map_mul, rs_rs] at hσ ⊢
  rw [rs_coe_inv, rs_coe_inv, e, hσ, ← coe_res, mul_inv_rev, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem exists_quot_sec (P Q : LB X) (hP : P.IsLB) (hQ : Q.IsLB) (a : ∀ p₁ q, Γ(X, P.U p₁ ⊓ Q.U q)ˣ)
    (ha : GenRel P Q a) (σ : LB.Sec P) :
    ∃ s : LB.Sec Q, ∀ p₁ q, rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) =
      ((a p₁ q : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) (s.f q) := by
  have hcov : ∀ (V : X.Opens), V ≤ ⨆ p₁, P.U p₁ ⊓ V := fun V x hx => by
    have : x ∈ (⨆ p₁, P.U p₁ : X.Opens) := by rw [hP.cover]; trivial
    obtain ⟨p₁, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p₁, hp, hx⟩
  have hglue : ∀ q, ∃ t : Γ(X, Q.U q), ∀ p₁, rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q) t =
      (((a p₁ q)⁻¹ : Γ(X, P.U p₁ ⊓ Q.U q)ˣ) : Γ(X, P.U p₁ ⊓ Q.U q)) *
        rs (inf_le_left : P.U p₁ ⊓ Q.U q ≤ P.U p₁) (σ.f p₁) := fun q =>
    (X.sheaf.existsUnique_gluing' (fun p₁ => P.U p₁ ⊓ Q.U q) (Q.U q) (fun _ => homOfLE inf_le_right)
      (hcov (Q.U q)) _ (fun p₁ p₁' => quot_compat P Q hQ a ha σ q p₁ p₁')).exists
  choose t ht using hglue
  refine ⟨⟨t, fun q q' => ?_⟩, fun p₁ q => ?_⟩
  · refine X.sheaf.eq_of_locally_eq' (fun p₁ => P.U p₁ ⊓ (Q.U q ⊓ Q.U q')) (Q.U q ⊓ Q.U q')
      (fun _ => homOfLE inf_le_right) (hcov _) _ _ (fun p₁ => ?_)
    change rs _ (rs _ (t q)) = rs _ ((Q.g q q' : Γ(X, Q.U q ⊓ Q.U q')) * rs _ (t q'))
    simp only [map_mul, rs_rs]
    rw [      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q ≤ Q.U q)
        (le_inf inf_le_left (inf_le_right.trans inf_le_left) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q),
      ← rs_rs (inf_le_right : P.U p₁ ⊓ Q.U q' ≤ Q.U q')
        (le_inf inf_le_left (inf_le_right.trans inf_le_right) : P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ P.U p₁ ⊓ Q.U q'),
      ht, ht]
    have e := congrArg (fun u : Γ(X, (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q'))ˣ =>
      rs (le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right)) :
          P.U p₁ ⊓ (Q.U q ⊓ Q.U q') ≤ (P.U p₁ ⊓ Q.U q) ⊓ (P.U p₁ ⊓ Q.U q')) (u⁻¹ : Γ(X, _)ˣ)) (ha p₁ q p₁ q')
    rw [res_g_self P hP p₁, _root_.one_mul, mul_inv_rev, inv_inv] at e
    simp only [map_mul, rs_rs, rs_coe_inv, Units.val_mul, ← coe_res] at e ⊢
    simp only [map_inv, ReciprocityTheory.ChartRestriction.G.DVR.res_res'] at e ⊢
    rw [e]
    ring
  · rw [ht, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]

end GlobalTheory.QuotSec

namespace GlobalTheory.HomFixMat

theorem divSec_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  intro X Z₁ Z₂ L M f g a α hα hL hM σ
  obtain ⟨s, hs⟩ := GlobalTheory.QuotSec.exists_quot_sec (powPull M g a) (powPull L f a)
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB M hM _ _) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _)
    (fun p₁ q => α.s (p₁, q)) (GlobalTheory.QuotSec.genRel_of_isGen _ _ α hα) σ
  exact ⟨s, fun p => hs p.1 p.2⟩

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModInt
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobStep

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_comp (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = ((substAlgHom (R := Q) (S := Q) (HasSubst.X_pow (σ := σ) (S := Q) hp)).toRingHom.comp
      (MvPowerSeries.map s)) f := by
  simp [frob]

theorem frob_smul (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) (b : B) (f : MvPowerSeries σ Q) :
    frob p s (algebraMap B Q b • f) = algebraMap B Q (τ b) • frob p s f := by
  unfold frob
  rw [smul_eq_C_mul, map_mul, map_C, hs, ← smul_eq_C_mul,
    subst_smul (HasSubst.X_pow (σ := σ) (S := Q) hp)]

theorem frob_comb (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) {ι : Type} [Fintype ι]
    (w : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb w e) = ∑ i, algebraMap B Q (τ (w i)) • frob p s (e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb, frob_eq_comp p hp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← frob_eq_comp p hp, frob_smul p hp τ s hs]

theorem in_top_sum_smul {σ : Type} {ι : Type} [Fintype ι] (c : ι → B)
    (g : ι → MvPowerSeries σ Q) (h : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  intro α
  choose b _ hb using fun i => h i α
  refine ⟨∑ i, c i * b i, Submodule.mem_top, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, hb, map_mul]

theorem comb_mulVec {σ : Type} {ι : Type} [Fintype ι] (M : Matrix ι ι B) (v : ι → B)
    (e : ι → MvPowerSeries σ Q) :
    comb (M.mulVec v) e = ∑ i, algebraMap B Q (v i) • comb (fun l => M l i) e := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul, Finset.smul_sum, smul_smul,
    ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem frob_comb_step : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q]
    (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) →
    ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B),
    (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) →
    ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  intro p hp B Q _ _ _ σ s hs d ι _ e M hM w
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have key : frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e =
      ∑ i, algebraMap B Q (σ (w i)) • (frob p s (e i) - comb (fun l => M l i) e) := by
    rw [frob_comb p hp0 σ s hs, comb_mulVec]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [key]
  exact in_top_sum_smul _ _ hM

end GlobalTheory.FrobStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpaces
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFg
open GlobalTheory.EtC

def invPSh (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Scheme.Γ.obj U))
  map f := TypeCat.ofHom fun h => ⟨(map_natCast (Scheme.Γ.map f).hom q) ▸ h.down.map (Scheme.Γ.map f).hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev lineSp (q : ℕ) : Spc := ptimes (invPSh q) (ofCat (glCat 1))

abbrev lineSp.line (q : ℕ) : lineSp q ⟶ ofCat (glCat 1) := ptimes.snd _ _

theorem inv_lineSp (q : ℕ) : Inv q (lineSp q) := fun _ ⟨y⟩ => y.1.down

theorem inv_of_map {E E' : Spc} (f : E ⟶ E') {q : ℕ} (h : Inv q E') : Inv q E := fun U ⟨x⟩ =>
  h U ⟨((f.app (op (SimplexCategory.mk 0))).app (op U)) x⟩

theorem isUnit_of_simplex {q : ℕ} {E : Spc} (hE : Inv q E) (p : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ)
    (x : (E.obj p).obj U) : IsUnit (q : Scheme.Γ.obj U) :=
  hE U.unop ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) p.unop 0).op).app U x⟩

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E)

def colInv (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ disc.obj (invPSh q) where
  app n := { app := fun U => TypeCat.ofHom (fun y => ⟨isUnit_of_simplex hE p U y.1⟩), naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def colLine (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ lineSp q :=
  (ptimesIsLimit _ _).lift (BinaryFan.mk (colInv q hE p) (ptimes.snd _ _ ≫ Fib.line N))

theorem colLine_line (p : SimplexCategoryᵒᵖ) : colLine q hE p ≫ lineSp.line q = ptimes.snd (E.obj p) (Fib N) ≫ Fib.line N :=
  (ptimesIsLimit _ _).fac _ ⟨WalkingPair.right⟩

def ellB : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (lineSp q) where
  app p := colLine q hE p
  naturality _ _ _ := rfl

theorem pull_cast {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E₂ n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f (tw q i) n x : Ht q E₁ n i) := by
  subst hn hi; rfl

theorem pull_cpow [NeZero q] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) (h : Inv q E₂) (x : Ht q E₂ 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (a6nat_holds q).2.1 f h]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (a6nat_holds q).1, ih]

theorem mk_zcomp_ofHom {R : Type} [CommRing R] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {F : Shv R} {n : ℤ}
    (z : Cocycle ((chains R).obj E₂) (res R F) n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _)) = pull R f F n (CohomologyClass.mk z) :=
  rfl

theorem diag_line : (bidiag.map (ellB q V hE) ≫ (bidiagConst (lineSp q)).hom) ≫ lineSp.line q =
    bidiag.map (twLine E V) ≫ (bidiagConst _).hom := rfl

theorem pbf_of_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ),
    (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) →
      ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  intro q _ N hD E V hE
  have hB := inv_lineSp q
  have hP : Inv q (pullback V (PGL.pr N)) := inv_of_map (pullback.fst V (PGL.pr N)) hE
  choose z hz using fun j : Fin N => CohomologyClass.mk_surjective (cpow q (c1 q (lineSp.line q)) (j : ℕ))
  refine GlobalTheory.PBFc.pbf_of_model q V (ellB q V hE) hE z (fun j => ?_) (fun a j => ?_) hD
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB, pull_cpow q _ hP,
      (a6nat_holds q).2.2.1 _ _ hP, twIso_line, diag_line]
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB]
    exact congrArg (fun L => cpow q (c1 q L) (j : ℕ)) (colLine_line q hE _)

end GlobalTheory.PBFg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBound
section
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.GridIntProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem adj_pow_apply (x U : Module.End ℚ V) (k : ℕ) :
    (adj x ^ k) U = ∑ t ∈ Finset.range (k + 1),
      (((-1 : ℚ) ^ (k - t) * (k.choose t : ℚ)) • (x ^ t * U * x ^ (k - t))) := by
  have hc : Commute (LinearMap.mulLeft ℚ x) ((-1 : ℚ) • LinearMap.mulRight ℚ x) :=
    (LinearMap.commute_mulLeft_right x x).smul_right _
  have h1 : adj x = LinearMap.mulLeft ℚ x + (-1 : ℚ) • LinearMap.mulRight ℚ x := by
    simp [adj, sub_eq_add_neg]
  rw [h1, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℚ, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]

def IntOn (L M : Submodule ℤ V) (c : ℕ) (U : Module.End ℚ V) : Prop := ∀ x ∈ L, ((c : ℕ) : ℤ) • U x ∈ M

theorem intOn_divAdj (L M : Submodule ℤ V) (e : Module.End ℚ V)
    (hL : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ L)
    (hM : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ M)
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) (k : ℕ) :
    IntOn L M c (((k.factorial : ℚ)⁻¹) • (adj e ^ k) U) := by
  intro y hy
  have hE : ((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj e ^ k) U) y) =
      ∑ t ∈ Finset.range (k + 1), ((-1 : ℤ) ^ (k - t)) • ((t.factorial : ℚ)⁻¹ •
        (e ^ t) (((c : ℕ) : ℤ) • U (((k - t).factorial : ℚ)⁻¹ • (e ^ (k - t)) y))) := by
    rw [LinearMap.smul_apply, adj_pow_apply, LinearMap.sum_apply, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hch := Nat.choose_mul_factorial_mul_factorial ht'
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      LinearMap.sum_apply, Finset.smul_sum]
    congr 1
    have h1 : ((k.choose t : ℕ) : ℚ) * (t.factorial : ℚ) * ((k - t).factorial : ℚ) = (k.factorial : ℚ) := by
      exact_mod_cast hch
    have h2 : (t.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((k - t).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h5 : ((k.choose t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ht').ne'
    rw [← h1]
    push_cast
    field_simp
  rw [hE]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  exact hM t _ (hU _ (hL (k - t) y hy))

theorem intOn_proj (L M : Submodule ℤ V) (X Y : Module.End ℚ V)
    (hLX : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ L)
    (hMX : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ M)
    (hLY : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ L)
    (hMY : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ M)
    (K j₀ Λ : ℕ) (hΛ : ∀ k ≤ K, (j₀ + k + 1).factorial ∣ Λ * (j₀.factorial * k.factorial))
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) :
    IntOn L M (c * Λ) (proj K j₀ (adj X) (adj Y) U) := by
  intro y hy
  simp only [proj, LinearMap.sum_apply, Finset.smul_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, hm⟩ := hΛ k hkK
  have hE : ((c * Λ : ℕ) : ℤ) • ((coef j₀ k • (adj Y ^ k * adj X ^ k)) U) y =
      ((-1 : ℤ) ^ k * (m : ℤ)) • (((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj Y ^ k)
        ((k.factorial : ℚ)⁻¹ • (adj X ^ k) U)) y)) := by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    have h2 : (j₀.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((j₀ + k + 1).factorial : ℚ) ≠ 0 := by positivity
    have hΛq : (Λ : ℚ) = ((j₀ + k + 1).factorial : ℚ) * (m : ℚ) / ((j₀.factorial : ℚ) * (k.factorial : ℚ)) := by
      rw [eq_div_iff (by positivity)]
      exact_mod_cast hm
    have hkj : k + j₀ + 1 = j₀ + k + 1 := by omega
    simp only [coef, hkj]
    push_cast
    rw [hΛq]
    field_simp
  rw [hE]
  refine Submodule.smul_mem _ _ ?_
  exact intOn_divAdj L M Y hLY hMY c _ (intOn_divAdj L M X hLX hMX c U hU k) k y hy

theorem intOn_listProd (L M : Submodule ℤ V) (n : ℕ) :
    ∀ (l : List (Module.End ℚ (Module.End ℚ V))), (∀ f ∈ l, ∀ c U, IntOn L M c U → IntOn L M (c * n) (f U)) →
      ∀ c U, IntOn L M c U → IntOn L M (c * n ^ l.length) (l.prod U)
  | [], _, c, U, hU => by simpa using hU
  | f :: l, hf, c, U, hU => by
      rw [List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, ← mul_assoc]
      exact hf f (List.mem_cons_self ..) _ _
        (intOn_listProd L M n l (fun g hg => hf g (List.mem_cons_of_mem _ hg)) c U hU)

end GlobalTheory.LeviCut.GridIntProof

namespace GlobalTheory.LeviCut


open GridIntProof in
theorem gridInt_holds : GridInt := by
  intro V _ _ a b K w Λ e L M hL hM hw hΛ c T hT
  have hstep : ∀ i < a, ∀ j, a ≤ j → j < a + b → ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ) (rootP (fun c d => adj (e c d)) K i j U) := by
    intro i hi j hj1 hj2 c U hU
    have hij : i ≠ j := by omega
    have hji : j ≠ i := by omega
    exact intOn_proj L M (e i j) (e j i) (fun k x hx => hL i (by omega) j hj2 hij k x hx)
      (fun k x hx => hM i (by omega) j hj2 hij k x hx) (fun k x hx => hL j hj2 i (by omega) hji k x hx)
      (fun k x hx => hM j hj2 i (by omega) hji k x hx) K (j - i - 1) Λ (fun k hk => hΛ _ _ (by omega)) c U hU
  have hrow : ∀ i < a, ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ ^ b) (rowP (fun c d => adj (e c d)) K i a b U) := by
    intro i hi c U hU
    have h := intOn_listProd L M Λ ((List.range' a b).map (rootP (fun c d => adj (e c d)) K i)) (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      rw [List.mem_range'_1] at hj
      exact hstep i hi j hj.1 hj.2) c U hU
    simpa [rowP] using h
  have h := intOn_listProd L M (Λ ^ b) ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b)
    (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨i, hi, rfl⟩ := hf
      rw [List.mem_reverse, List.mem_range] at hi
      exact hrow i hi) c T hT
  have e1 : (Λ ^ b) ^ ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b).length =
      Λ ^ (a * b) := by
    simp [← pow_mul, mul_comm]
  rw [e1] at h
  exact h

end GlobalTheory.LeviCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisTransitionMatricesInverse
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.BasisTrans

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_add {g h : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) (hh : In (⊤ : Ideal B) h) :
    In (⊤ : Ideal B) (g + h) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  obtain ⟨b, -, hb⟩ := hh α
  exact ⟨a + b, trivial, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩

theorem in_smul (c : B) {g : MvPowerSeries σ Q} (hg : In (⊤ : Ideal B) g) :
    In (⊤ : Ideal B) (algebraMap B Q c • g) := fun α => by
  obtain ⟨a, -, ha⟩ := hg α
  exact ⟨c * a, trivial, by rw [coeff_smul, ha, map_mul]⟩

theorem in_sum {κ : Type} (s : Finset κ) (g : κ → MvPowerSeries σ Q)
    (hg : ∀ j ∈ s, In (⊤ : Ideal B) (g j)) : In (⊤ : Ideal B) (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hg a (Finset.mem_insert_self _ _)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem comb_one {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → MvPowerSeries σ Q) (i : ι) :
    comb ((1 : Matrix ι ι B) i) e = e i := by
  simp [comb, Matrix.one_apply]

theorem comb_mul {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι → MvPowerSeries σ Q)
    (f : κ → MvPowerSeries σ Q) (P : ι → κ → B) (P' : κ → ι → B) (i : ι) :
    e i - comb ((Matrix.of P * Matrix.of P') i) e =
      (e i - comb (P i) f) + ∑ j, algebraMap B Q (P i j) • (f j - comb (P' j) e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, Matrix.mul_apply, Matrix.of_apply, smul_sub, Finset.sum_sub_distrib,
    Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun j k => algebraMap B Q (P i j * P' j k) • e k)]
  abel

theorem mul_eq_one {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq ι] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q)
    (he : IsBasis μ e) (P : ι → κ → B) (P' : κ → ι → B)
    (h1 : ∀ i, In (⊤ : Ideal B) (e i - comb (P i) f))
    (h2 : ∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) :
    Matrix.of P * Matrix.of P' = 1 := by
  funext i
  obtain ⟨b, -, hb⟩ := he.2 (e i) (he.1 i)
  have hA : In (⊤ : Ideal B) (e i - comb ((Matrix.of P * Matrix.of P') i) e) := by
    rw [comb_mul e f P P' i]
    exact in_add (h1 i) (in_sum _ _ fun j _ => in_smul _ (h2 j))
  have hB : In (⊤ : Ideal B) (e i - comb ((1 : Matrix ι ι B) i) e) := by
    rw [comb_one, sub_self]; exact in_zero
  exact (hb _ hA).trans (hb _ hB).symm

theorem trans_inverse : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι → MvPowerSeries (Fin d) Q) (f : κ → MvPowerSeries (Fin d) Q), IsBasis μ e → IsBasis μ f → ∀ (P : ι → κ → B) (P' : κ → ι → B), (∀ i, In (⊤ : Ideal B) (e i - comb (P i) f)) → (∀ j, In (⊤ : Ideal B) (f j - comb (P' j) e)) → Matrix.of P * Matrix.of P' = 1 ∧ Matrix.of P' * Matrix.of P = 1 := by
  intro B Q _ _ _ d μ ι κ _ _ _ _ e f he hf P P' h1 h2
  exact ⟨mul_eq_one μ e f he P P' h1 h2, mul_eq_one μ f e hf P' P h2 h1⟩

end GlobalTheory.BasisTrans
end

