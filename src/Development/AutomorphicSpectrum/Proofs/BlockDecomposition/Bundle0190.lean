module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0185
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0177
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftSurjectiveKernelLevel
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PerfFil

section Generic

theorem tensor_ringHom_ext {R S T B : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing B]
    [Algebra R S] [Algebra R T] {f g : S ⊗[R] T →+* B} (h : ∀ a b, f (a ⊗ₜ b) = g (a ⊗ₜ b)) : f = g := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem mem_span_pow_of_compatible {T : Type*} [CommRing T] (p : ℕ) {B : ℕ → Type*} [∀ n, CommRing (B n)]
    (f : ∀ n, T →+* B n) (red : ∀ n, B (n + 1) →+* B n) (r : ∀ n, B (n + 1) →+* B 1)
    (hred : ∀ n z, red n (f (n + 1) z) = f n z) (hr : ∀ n z, r n (f (n + 1) z) = f 1 z)
    (hmul : ∀ n x, (p : B (n + 1)) ^ n * x = 0 → r n x = 0)
    (hone : ∀ z, f 1 z = 0 → z ∈ Ideal.span {(p : T)}) (n : ℕ) (z : T) (hz : f n z = 0) :
    z ∈ Ideal.span {(p : T) ^ n} := by
  induction n generalizing z with
  | zero => rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  | succ n ih =>
    have h1 : f n z = 0 := by rw [← hred n z, hz, map_zero]
    obtain ⟨z', rfl⟩ := Ideal.mem_span_singleton'.1 (ih z h1)
    have h2 : (p : B (n + 1)) ^ n * f (n + 1) z' = 0 := by
      rw [map_mul, map_pow, map_natCast, mul_comm] at hz
      exact hz
    have h3 := hmul n _ h2
    rw [hr] at h3
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (hone z' h3)
    exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩

theorem map_eq_zero_of_mem_span_pow {T B : Type*} [CommRing T] [CommRing B] (p n : ℕ) (f : T →+* B)
    (hp : (p : B) ^ n = 0) {z : T} (hz : z ∈ Ideal.span {(p : T) ^ n}) : f z = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_mul, map_pow, map_natCast, hp, mul_zero]

theorem surjective_of_span {Wr C B T : Type*} [CommRing Wr] [CommRing C] [CommRing B] [CommRing T] [Algebra Wr C]
    (mk : C →+* B) (hmk : Function.Surjective mk) (f : T →+* B) (g : Wr →+* B)
    (hg : ∀ c x, mk (c • x) = g c * mk x) (hgr : ∀ c, g c ∈ f.range) (S : Set C)
    (hS : ∀ x ∈ S, mk x ∈ f.range) (hspan : ∀ x, x ∈ Submodule.span Wr S) : Function.Surjective f := by
  intro b
  obtain ⟨y, rfl⟩ := hmk b
  have hy := hspan y
  suffices h : mk y ∈ f.range from h
  induction hy using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [hg]; exact mul_mem (hgr c) hx

end Generic

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

def tensMap (n : ℕ) : TensorProduct (Ainf l) (Acris l) A.W →+* A.Acr n :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n))
    (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)).toRingHom

theorem tensMap_tmul (n : ℕ) (a : Acris l) (w : A.W) :
    tensMap A n (a ⊗ₜ w) = A.cris n a * A.toAcr n w :=
  Algebra.TensorProduct.lift_tmul _ _ _ a w

theorem red_cris {m n : ℕ} (h : n ≤ m) (a : Acris l) : A.red h (A.cris m a) = A.cris n a :=
  RingHom.congr_fun (ACris.ringHom_ext (F := (A.red h).comp (A.cris m)) (G := A.cris n) fun y => by
    rw [RingHom.comp_apply, cris_of, cris_of, red_mk]) a

theorem red_toAcr {m n : ℕ} (h : n ≤ m) (w : A.W) : A.red h (A.toAcr m w) = A.toAcr n w := rfl

theorem red_tensMap {m n : ℕ} (h : n ≤ m) (z : TensorProduct (Ainf l) (Acris l) A.W) :
    A.red h (tensMap A m z) = tensMap A n z :=
  RingHom.congr_fun (tensor_ringHom_ext (f := (A.red h).comp (tensMap A m)) (g := tensMap A n) fun a w => by
    rw [RingHom.comp_apply, tensMap_tmul, tensMap_tmul, map_mul, red_cris, red_toAcr]) z

theorem dxi_eq_cris (n k : ℕ) : A.dxi n k =
    A.cris n (AdicCompletion.of _ _ ⟨ACris.dpow k (xi0 l), ACris.dpow_mem xi0_mem k⟩) := by
  rw [cris_of]
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  exact (awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)).symm

theorem tensMap_surjective (n : ℕ) : Function.Surjective (tensMap A n) := by
  refine surjective_of_span (Wr := A.W) (A.mkAcr n) Ideal.Quotient.mk_surjective (tensMap A n) (A.toAcr n)
    (fun c x => ?_) (fun c => ⟨(1 : Acris l) ⊗ₜ c, ?_⟩) {z | ∃ k, 0 ≤ k ∧ z = A.dxi0 k} ?_ (mem_spanFrom_zero A)
  · rw [Algebra.smul_def, map_mul]
    rfl
  · rw [tensMap_tmul, map_one, one_mul]
  · rintro _ ⟨k, -, rfl⟩
    refine ⟨(AdicCompletion.of _ _ ⟨ACris.dpow k (xi0 l), ACris.dpow_mem xi0_mem k⟩ : Acris l) ⊗ₜ 1, ?_⟩
    rw [tensMap_tmul, map_one, mul_one, ← dxi_eq_cris]
    rfl

theorem mem_span_of_tensMap_eq_zero (n : ℕ) (z : TensorProduct (Ainf l) (Acris l) A.W) (hz : tensMap A n z = 0) :
    z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} :=
  mem_span_pow_of_compatible l (B := A.Acr) (tensMap A) (fun n => A.red (Nat.le_succ n))
    (fun n => A.red (Nat.le_add_left 1 n)) (fun n z => red_tensMap A _ z) (fun n z => red_tensMap A _ z)
    (fun n x => ((_root_.GlobalTheory.CompanionTheory.PerfAlg.lseq A n 1).2.2.1 x).1) (_root_.GlobalTheory.CompanionTheory.TensOne.main A) n z hz

theorem tensMap_eq_zero_of_mem (n : ℕ) (z : TensorProduct (Ainf l) (Acris l) A.W)
    (hz : z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n}) : tensMap A n z = 0 :=
  map_eq_zero_of_mem_span_pow l n (tensMap A n) (A.pow_l_acr n) hz

theorem tens_base_change : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ),
    Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n))
      (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧
    ∀ z : TensorProduct (Ainf l) (Acris l) A.W,
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n))
        (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔
      z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} :=
  fun A n => ⟨tensMap_surjective A n, fun z =>
    ⟨mem_span_of_tensMap_eq_zero A n z, tensMap_eq_zero_of_mem A n z⟩⟩

end GlobalTheory.CompanionTheory.PerfFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToH0BijectiveOfInitial
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

section Initial

universe u v w

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {D : C} (hD : Limits.IsInitial D)

def toH0 : F.obj D →ₗ[R] CH.H F 0 where
  toFun x := (CH.cx F).cls (CH.aug F (fun T => (F.map (hD.to T)).hom) x) ((CrystallineSemistableComparison.P.initial F D hD).1 x)
  map_add' x y := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.1 _ _ ((CrystallineSemistableComparison.P.initial F D hD).1 x) ((CrystallineSemistableComparison.P.initial F D hD).1 y)
      (by rw [map_add (f := _), (CrystallineSemistableComparison.P.initial F D hD).1 x, (CrystallineSemistableComparison.P.initial F D hD).1 y, add_zero])
    exact (cls_congr (map_add _ x y) _ _).trans this
  map_smul' r x := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.2 r _ ((CrystallineSemistableComparison.P.initial F D hD).1 x)
      (by rw [map_smul, (CrystallineSemistableComparison.P.initial F D hD).1 x, smul_zero])
    exact (cls_congr (map_smul _ r x) _ _).trans this

theorem toH0_bijective_of_initial : Function.Bijective (toH0 F hD) := by
  obtain ⟨h1, h2, h3, -⟩ := CrystallineSemistableComparison.P.initial F D hD
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h := ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.1 _ (h1 x)).1 hx
    have h' := h2 x ((Submodule.mem_bot R).1 h)
    rwa [one_smul] at h'
  · intro c
    obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).1 c
    obtain ⟨x, hx⟩ := h3 f hf
    rw [one_smul] at hx
    exact ⟨x, cls_congr hx _ _⟩

include hD in
theorem H_succ_sub (j : ℕ) : Subsingleton (CH.H F (j + 1)) := by
  obtain ⟨-, -, -, hex⟩ := CrystallineSemistableComparison.P.initial F D hD
  have key : ∀ x : CH.H F (j + 1), x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).2.1 a ha).2 ?_
    obtain ⟨y, hy⟩ := hex j a ha
    rw [one_smul] at hy
    exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end Initial

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

section Base

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem base_case {D : C} {D' : C'} (hD : Limits.IsInitial D) (hD' : Limits.IsInitial D') (e : D ⟶ m.G.obj D')
    (ν : ∀ i, N i → R') (a b : ι → IdF Φ.A) (a' b' : IdF Φ'.A) (ha : ∀ i n, m.LeC (ν i n) (a i) a')
    (hb : ∀ i n, m.LeC (ν i n) (b i) b')
    (h : Tens R (N := N) (M := fun i => (sq (a i) (b i)).obj D) (M' := (sq a' b').obj D')
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i) (b i)) j) (M' := CH.H (sq a' b') j)
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).pull j x := by
  cases j with
  | zero =>
    refine tens_transfer (fun i => LinearEquiv.ofBijective (toH0 (sq (a i) (b i)) hD) (toH0_bijective_of_initial _ hD))
      (LinearEquiv.ofBijective (toH0 (sq a' b') hD') (toH0_bijective_of_initial _ hD')).toAddEquiv _ _ (fun i n x => ?_) h
    change (m.sqC (ν i n) (ha i n) (hb i n)).hom.mapH 0 (toH0 (sq (a i) (b i)) hD x) = toH0 (sq a' b') hD' _
    have h1 := (CrystallineSemistableComparison.P.initial (sq (a i) (b i)) D hD).1 x
    refine (CrystallineSemistableComparison.P.mapH_cls _ 0 _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ h1)).trans (cls_congr (funext fun s => ?_) _ _)
    change (m.sqC (ν i n) (ha i n) (hb i n)).τ _ (((sq (a i) (b i)).map (hD.to (m.G.obj (s.obj (Fin.last 0))))).hom x) =
      ((sq a' b').map (hD'.to (s.obj (Fin.last 0)))).hom ((m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x))
    rw [← (m.sqC (ν i n) (ha i n) (hb i n)).nat]
    congr 1
    have h2 := congrArg (fun t => ((sq (a i) (b i)).map t).hom x)
      (hD.hom_ext (hD.to (m.G.obj (s.obj (Fin.last 0)))) (e ≫ m.G.map (hD'.to (s.obj (Fin.last 0)))))
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    exact h2
  | succ j => exact tens_zero (fun i => H_succ_sub _ hD j) (H_succ_sub _ hD' j) _

end Base

section Step

variable [Algebra R R'] [∀ i, Module.Flat R (N i)] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
  {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
  (hρ : ∀ T, Function.Injective (m.ρ T)) (ν : ∀ i, N i →ₗ[R] R')

theorem step (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r)
    (hQ' : Q'.Ladder a' b' r) (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r'))
    (c1 : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => CH.H (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) j)
      (M' := CH.H (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) j)
      fun i n x => ((m1 m E E' e he hρ).sqC (ν i n) (le_cover_restrict_compat m E E' e he hρ (ha i n r₀)) (le_cover_restrict_compat m E E' e he hρ (hb i n r₀))).pull j x)
    (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  have hle : r - 1 ≤ r := by omega
  choose β hinj hex hsurj hform using fun i => GlobalTheory.T.filtration_critical_comparison_map Q E (a i) (b i) r (hQ i).le ((hQ i).ca r le_rfl)
    ((hQ i).ca _ hle) ((hQ i).cb r le_rfl) ((hQ i).cb _ hle)
  obtain ⟨β', hinj', hex', hsurj', hform'⟩ := GlobalTheory.T.filtration_critical_comparison_map Q' E' a' b' r hQ'.le (hQ'.ca r le_rfl)
    (hQ'.ca _ hle) (hQ'.cb r le_rfl) (hQ'.cb _ hle)
  have sI := fun i => CrystallineSemistableComparison.P.ses_cochains (alpha Q (a i r) (b i r)) (β i) (hinj i) (hex i) (hsurj i)
  have sP := CrystallineSemistableComparison.P.ses_cochains (alpha Q' (a' r) (b' r)) β' hinj' hex' hsurj'
  have hP : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => (CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r₀) (b i r₀))).H j)
      (M' := (CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r₀) (b' r₀))).H j)
      fun i n x => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀)).hom.mapH j x := by
    intro r₀ hr₀ j
    exact tens_transfer
      (fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) (Cut.P0 Q)).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q) (Cut.inc E) (Cut.adj Q) j))
      ((LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) (Cut.P0 Q')).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q') (Cut.inc E') (Cut.adj Q') j)).toAddEquiv) _ _
      (fun i n x => pull_restrict_first_piece_compat m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀) j x) (c1 r₀ hr₀ j)
  have hPt := tens_les
    (K := fun i => CH.cx (Pt.U E ⋙ sq (a i r) (b i r)))
    (L := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r) (b i r)))
    (M := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i (r - 1)) (b i (r - 1))))
    (K' := CH.cx (Pt.U E' ⋙ sq (a' r) (b' r)))
    (L' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r)))
    (M' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1))))
    (fun i => (CH.Mor.ofNatTrans (alpha Q (a i r) (b i r))).hom) (fun i => (CH.Mor.ofNatTrans (β i)).hom)
    (fun i => (sI i).1) (fun i => (sI i).2.1) (fun i => (sI i).2.2)
    (CH.Mor.ofNatTrans (alpha Q' (a' r) (b' r))).hom (CH.Mor.ofNatTrans β').hom sP.1 sP.2.1 sP.2.2
    (fun i n => (mPt m E E' e (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n (r - 1)) (hb i n (r - 1))).hom)
    (fun i n k x => alpha_hom m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r) k x)
    (fun i n k x => funext fun s => beta_τ m E E' e he hρ Q Q' (ν i n) (ha i n) (hb i n) ((hQ i).ca r le_rfl)
      ((hQ i).ca _ hle) (β i) (hform i) β' hform' _ _)
    (hP r (Or.inl rfl)) (hP (r - 1) (Or.inr rfl))
    (fun i j => hadd_Pt m E E' e (ν i) (ha i · r) (hb i · r) j) j
  let u := fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a i r) (b i r)) (Pt.U E)).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E) (Pt.S E) (Pt.adj E) j)
  let u' := LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a' r) (b' r)) (Pt.U E')).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E') (Pt.S E') (Pt.adj E') j)
  refine tens_transfer (fun i => (u i).symm) u'.toAddEquiv.symm _ _ (fun i n x => ?_) hPt
  obtain ⟨z, rfl⟩ := (u i).surjective x
  rw [LinearEquiv.symm_apply_apply]
  symm
  refine (AddEquiv.symm_apply_eq u'.toAddEquiv).2 ?_
  exact pull_U m E E' e (ν i n) (ha i n r) (hb i n r) j z

end Step

section Main

variable [Algebra R R'] [∀ i, Module.Flat R (N i)]

theorem ladder_mono {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Q : Poly Φ} {a b : ℤ → IdF Φ.A} {r r₀ : ℤ}
    (h : Q.Ladder a b r) (hr : r₀ ≤ r) : Q.Ladder a b r₀ :=
  ⟨h.le, fun r' hr' => h.ca r' (hr'.trans hr), fun r' hr' => h.cb r' (hr'.trans hr)⟩

theorem main (ν : ∀ i, N i →ₗ[R] R') : ∀ (d : ℕ) {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
    (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
    (hρ : ∀ T, Function.Injective (m.ρ T)) (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ)
    (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro d
  induction d with
  | zero =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    exact base_case m (Frame.initial E) (Frame.initial E') e (fun i n => ν i n) (fun i => a i r) (fun i => b i r) (a' r) (b' r)
      (fun i n => ha i n r) (fun i n => hb i n r) (h r (by simp) le_rfl) j
  | succ d ih =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    refine step m Q Q' E E' e he hρ ν a b a' b' r hQ hQ' ha hb (fun r₀ hr₀ j => ?_) j
    have hle : r₀ ≤ r := by rcases hr₀ with rfl | rfl <;> omega
    have hlo : r - 1 ≤ r₀ := by rcases hr₀ with rfl | rfl <;> omega
    exact ih (m1 m E E' e he hρ) (Cut.Q1 Q) (Cut.Q1 Q') (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) (fr1 m E E' e he hρ)
      (fun T => hρ T.T) (fun i r => (a i r).res (Cut.U E)) (fun i r => (b i r).res (Cut.U E))
      (fun r => (a' r).res (Cut.U E')) (fun r => (b' r).res (Cut.U E')) r₀
      (fun i => Cut.ladder_truncation Q (ladder_mono (hQ i) hle)) (Cut.ladder_truncation Q' (ladder_mono hQ' hle))
      (fun i n r' => le_cover_restrict_compat m E E' e he hρ (ha i n r')) (fun i n r' => le_cover_restrict_compat m E E' e he hρ (hb i n r'))
      (fun r' h1 h2 => h r' (by push_cast; omega) (h2.trans hle)) j

end Main

theorem local_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d)
    (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module.Flat R (N i)] (ν : ∀ i, N i →ₗ[R] R')
    (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro R R' _ _ _ C C' _ _ Φ Φ' m Q Q' d E E' e he hρ ι _ _ N _ _ _ ν a b a' b' r hQ hQ' ha hb h j
  exact main ν d m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpMemCE
section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveWords

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun hc continuous_const

section Good

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Good (T : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ f, ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (T f) (GLs n)) ∧
  (∀ (f h : Mat n → V) (a b : ℂ), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) →
    ∀ x ∈ GLs n, T (fun y => a • f y + b • h y) x = a • T f x + b • T h x) ∧
  (∀ f f', Set.EqOn f f' (GLs n) → Set.EqOn (T f) (T f') (GLs n))

theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ h => h⟩

theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun _ _ => contDiffOn_const, fun _ _ a b _ _ x _ => by simp, fun _ _ _ _ _ => rfl⟩

theorem good_Rd (hR : RCalc) (X : Mat n) : Good (n := n) (V := V) (Rd X) := by
  refine ⟨fun f hf => ((hR n).1 V f hf).1 X, ?_, ?_⟩
  · intro f h a b hf hh x hx
    have hn : GLs n ∈ nhds x := (isOpen_GLs n).mem_nhds hx
    have df : DifferentiableAt ℝ f x := (hf.contDiffAt hn).differentiableAt (by simp)
    have dh : DifferentiableAt ℝ h x := (hh.contDiffAt hn).differentiableAt (by simp)
    have key : HasFDerivAt (fun y => a • f y + b • h y)
        (a • fderiv ℝ f x + b • fderiv ℝ h x) x :=
      (df.hasFDerivAt.const_smul a).add (dh.hasFDerivAt.const_smul b)
    simp only [Rd]
    rw [key.fderiv]
    simp
  · intro f f' hE x hx
    have hn : GLs n ∈ nhds x := (isOpen_GLs n).mem_nhds hx
    have : f =ᶠ[nhds x] f' := Filter.eventuallyEq_of_mem hn hE
    simp only [Rd]
    rw [this.fderiv_eq]

theorem good_comp {T T' : (Mat n → V) → (Mat n → V)} (hT : Good T) (hT' : Good T') :
    Good (fun f => T (T' f)) := by
  refine ⟨fun f hf => hT.1 _ (hT'.1 f hf), ?_, fun f f' hE => hT.2.2 _ _ (hT'.2.2 f f' hE)⟩
  intro f h a b hf hh x hx
  have e : Set.EqOn (T' (fun y => a • f y + b • h y)) (fun y => a • T' f y + b • T' h y) (GLs n) :=
    fun y hy => hT'.2.1 f h a b hf hh y hy
  beta_reduce
  rw [hT.2.2 _ _ e hx]
  exact hT.2.1 _ _ a b (hT'.1 f hf) (hT'.1 h hh) x hx

theorem good_add {T T' : (Mat n → V) → (Mat n → V)} (hT : Good T) (hT' : Good T') :
    Good (fun f => T f + T' f) := by
  refine ⟨fun f hf => (hT.1 f hf).add (hT'.1 f hf), ?_, ?_⟩
  · intro f h a b hf hh x hx
    simp only [Pi.add_apply]
    rw [hT.2.1 f h a b hf hh x hx, hT'.2.1 f h a b hf hh x hx]
    module
  · intro f f' hE x hx
    simp only [Pi.add_apply]
    rw [hT.2.2 f f' hE hx, hT'.2.2 f f' hE hx]

theorem good_smul (c : ℂ) {T : (Mat n → V) → (Mat n → V)} (hT : Good T) :
    Good (fun f => c • T f) := by
  refine ⟨fun f hf => (hT.1 f hf).const_smul c, ?_, ?_⟩
  · intro f h a b hf hh x hx
    simp only [Pi.smul_apply]
    rw [hT.2.1 f h a b hf hh x hx]
    module
  · intro f f' hE x hx
    simp only [Pi.smul_apply]
    rw [hT.2.2 f f' hE hx]

theorem good_sum {ι : Type} (s : Finset ι) (T : ι → (Mat n → V) → (Mat n → V))
    (h : ∀ i, Good (T i)) : Good (fun f => ∑ i ∈ s, T i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a) ih

theorem good_Eu (hR : RCalc) (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul (1 / 2 : ℂ) (good_add (good_Rd hR _) (good_smul _ (good_Rd hR _)))

theorem good_Epow (hR : RCalc) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Good (n := n) (V := V) (Epow s m a b) := by
  induction m with
  | zero =>
    intro a b
    by_cases h : a = b
    · have e : Epow (n := n) (V := V) s 0 a b = fun f => f := by
        funext f; simp [Epow, h]
      rw [e]; exact good_id
    · have e : Epow (n := n) (V := V) s 0 a b = fun _ => 0 := by
        funext f; simp [Epow, h]
      rw [e]; exact good_zero
  | succ m ih =>
    intro a b
    exact good_sum Finset.univ (fun c f => Eu s a c (Epow s m c b f))
      (fun c => good_comp (good_Eu hR s a c) (ih c b))

theorem good_gel (hR : RCalc) (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ (fun a => Epow s m a a) (fun a => good_Epow hR s m a a)

theorem good_zOp (hR : RCalc) (w : List (Bool × ℕ)) : Good (n := n) (V := V) (zOp w) := by
  induction w with
  | nil => exact good_id
  | cons p w ih =>
    have e : zOp (n := n) (V := V) (p :: w) = fun f => gel p.1 p.2 (zOp w f) := rfl
    rw [e]
    exact good_comp (good_gel hR p.1 p.2) ih

end Good

end GlobalTheory.CompanionTheory.WaveWords
end
end

