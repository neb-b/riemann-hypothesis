module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0284
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0328
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellLeviUnipotentConjugation
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LeviPart

section Order

variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

def pos : (Σ a, Fin (d a)) ≃ Fin N := (stdBlocks d hd).trans (wOpen d hd).symm

theorem wOpen_pos (x : Σ a, Fin (d a)) : wOpen d hd (pos d hd x) = stdBlocks d hd x := by
  simp [pos]

theorem wKey_injective : Function.Injective (wKey d hd) := by
  intro x y hxy
  exact congrArg (fun z => (ofLex z).2) hxy

theorem key_strictMono : StrictMono (wKey d hd ∘ wOpen d hd) :=
  (Tuple.monotone_sort (wKey d hd)).strictMono_of_injective
    ((wKey_injective d hd).comp (wOpen d hd).injective)

theorem blk_std (x : Σ a, Fin (d a)) : blk (stdBlocks d hd) (stdBlocks d hd x) = x.1 := by
  simp [blk]

theorem key_lt (x y : Σ a, Fin (d a)) :
    wKey d hd (stdBlocks d hd x) < wKey d hd (stdBlocks d hd y) ↔
      y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [wKey, wKey, Prod.Lex.lt_iff]
  simp [blk_std]

theorem std_lt (a : Fin h) (i j : Fin (d a)) :
    stdBlocks d hd ⟨a, i⟩ < stdBlocks d hd ⟨a, j⟩ ↔ i < j := by
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, Fin.lt_def]
  omega

theorem pos_lt_iff (x y : Σ a, Fin (d a)) :
    pos d hd x < pos d hd y ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [← (key_strictMono d hd).lt_iff_lt, Function.comp, Function.comp, wOpen_pos, wOpen_pos, key_lt]

theorem pos_lt (a : Fin h) (i j : Fin (d a)) : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ ↔ i < j := by
  rw [pos_lt_iff, std_lt]
  simp

theorem pos_succ (a : Fin h) (i j : Fin (d a)) (hij : (j : ℕ) = i + 1) :
    (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1 := by
  have hlt : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ := (pos_lt d hd a i j).2 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hN := (pos d hd ⟨a, j⟩).2
  let t : Fin N := ⟨pos d hd ⟨a, i⟩ + 1, by omega⟩
  obtain ⟨⟨b, l⟩, hl⟩ := (pos d hd).surjective t
  have h1 : pos d hd ⟨a, i⟩ < pos d hd ⟨b, l⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp [t])
  have h2 : pos d hd ⟨b, l⟩ < pos d hd ⟨a, j⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp only [t]; omega)
  rw [pos_lt_iff] at h1 h2
  have hab : a = b := by
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h1 (lt_asymm h2)
      · exact absurd h2.1 (ne_of_lt h1)
    · exact h1.1
  subst hab
  have h3 := (std_lt d hd a i l).1 (h1.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have h4 := (std_lt d hd a l j).1 (h2.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have := Fin.lt_def.1 h3
  have := Fin.lt_def.1 h4
  omega

theorem pos_succ' (a : Fin h) (i j : Fin (d a)) (hij : (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1) :
    (j : ℕ) = i + 1 := by
  have hlt : i < j := (pos_lt d hd a i j).1 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hj := j.2
  let l : Fin (d a) := ⟨i + 1, by omega⟩
  have h1 := Fin.lt_def.1 ((pos_lt d hd a i l).2 (Fin.lt_def.2 (by simp [l])))
  have h2 := Fin.lt_def.1 ((pos_lt d hd a l j).2 (Fin.lt_def.2 (by simp only [l]; omega)))
  omega

theorem sum_superdiag {R : Type} [AddCommMonoid R] (A : Fin N → Fin N → R)
    (hA : ∀ x y : Σ a, Fin (d a), x.1 ≠ y.1 → A (pos d hd x) (pos d hd y) = 0) :
    ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, A p.1 p.2 =
      ∑ b, ∑ p : Fin (d b) × Fin (d b) with (p.2 : ℕ) = p.1 + 1, A (pos d hd ⟨b, p.1⟩) (pos d hd ⟨b, p.2⟩) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => (pos d hd ⟨x.1, x.2.1⟩, pos d hd ⟨x.1, x.2.2⟩)) ?_ ?_ ?_ ?_
  · rintro ⟨b, i, j⟩ hx -
    have hx' : (j : ℕ) = i + 1 := by simpa using hx
    simpa using pos_succ d hd b i j hx'
  · rintro ⟨b, i, j⟩ - - ⟨c, i', j'⟩ - - hxy
    have h1 := (pos d hd).injective (Prod.ext_iff.1 hxy).1
    have h2 := (pos d hd).injective (Prod.ext_iff.1 hxy).2
    simp only [Sigma.mk.injEq] at h1 h2
    obtain ⟨rfl, h1⟩ := h1
    obtain ⟨-, h2⟩ := h2
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    rfl
  · rintro ⟨p, q⟩ hpq hne
    have hpq' : (q : ℕ) = p + 1 := by simpa using hpq
    obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    have hbc : b = c := by
      by_contra hbc
      exact hne (hA _ _ hbc)
    subst hbc
    refine ⟨⟨b, i, j⟩, ?_, hne, rfl⟩
    simpa using pos_succ' d hd b i j hpq'
  · intro x _ _
    rfl

end Order

section Entries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

theorem conj_apply (w : Equiv.Perm (Fin N)) (A : GL (Fin N) k) (p q : Fin N) :
    ((pm k w * A * (pm k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (w p) (w q) =
      (A : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]
  simp

variable {d hd}
variable {A : GL (Fin N) k} {m : Levi k fun a => Fin (d a)}

theorem ent_same (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (b : Fin h) (i j : Fin (d b)) :
    (m b : Matrix (Fin (d b)) (Fin (d b)) k) i j =
      (A : Matrix (Fin N) (Fin N) k) (pos d hd ⟨b, i⟩) (pos d hd ⟨b, j⟩) := by
  rw [← leviEmb_apply_same k (stdBlocks d hd) m b i j, ← hm, ← wOpen_pos d hd, ← wOpen_pos d hd, conj_apply]

theorem ent_ne (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (x y : Σ a, Fin (d a)) (hxy : x.1 ≠ y.1) :
    (A : Matrix (Fin N) (Fin N) k) (pos d hd x) (pos d hd y) = 0 := by
  obtain ⟨b, i⟩ := x
  obtain ⟨c, j⟩ := y
  rw [← conj_apply (wOpen d hd) A, wOpen_pos, wOpen_pos, hm]
  exact leviEmb_apply_ne k (stdBlocks d hd) m hxy i j

theorem mem_unipM_of (hA : A ∈ unipB k (Fin N))
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    m ∈ unipM k d := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hA
  refine fun b _ => (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [ent_same hm]
    exact h1 _ _ ((pos_lt d hd b j i).2 hij)
  · rw [ent_same hm]
    exact h2 _

theorem addChar_sum {ι : Type} (ψ : AddChar k Circle) (s : Finset ι) (f : ι → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem whit_eq (ψ : AddChar k Circle) (hA : A ∈ unipB k (Fin N)) (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    whitChar ψ N ⟨A, hA⟩ = whitM d ψ ⟨m, hm'⟩ := by
  show Circle.toUnits (ψ _) = ∏ a : Fin h, Circle.toUnits (ψ _)
  rw [← map_prod, ← addChar_sum]
  refine congrArg _ (congrArg _ ?_)
  refine (sum_superdiag d hd (fun p q => (A : Matrix (Fin N) (Fin N) k) p q) (ent_ne hm)).trans ?_
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => (ent_same hm b p.1 p.2).symm

theorem mem_unipB_of (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    A ∈ unipB k (Fin N) := by
  refine (mem_unipB k).2 ⟨fun p q hpq => ?_, fun p => ?_⟩
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    by_cases hbc : b = c
    · subst hbc
      rw [← ent_same hm]
      exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).1 i j ((pos_lt d hd b j i).1 hpq)
    · exact ent_ne hm _ _ hbc
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    rw [← ent_same hm]
    exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).2 i

end Entries

theorem levi_part : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (hb : a ∈ unipB k (Fin N)), ∃ m : unipM k d, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 ∧ whitChar ψ N ⟨a, hb⟩ = whitM d ψ m) ∧ ∀ m : unipM k d, ∃ a ∈ unipL k d hd, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by
  intro k _ _ _ _ ψ h N d hd
  refine ⟨fun a ha hb => ?_, fun m => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := MonoidHom.mem_range.mp ((OpenFactor.mem_unipL k d hd).mp ha).2
    have hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m₀ := hm₀.symm
    have hm' := mem_unipM_of hb hm
    exact ⟨⟨m₀, hm'⟩, hm, whit_eq ψ hb hm' hm⟩
  · have hc : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * leviEmb k (stdBlocks d hd) m.1 * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by group
    exact ⟨_, (OpenFactor.mem_unipL k d hd).mpr
      ⟨mem_unipB_of m.2 hc, MonoidHom.mem_range.mpr ⟨m.1, hc.symm⟩⟩, hc⟩

end GlobalTheory.CompanionTheory.Rodier.LeviPart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelNullCast
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

theorem relNull_cast {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of K))
    {Q : ObjectProperty (Thick (smFun Y q))} {a n c c' N N' : ℕ} (hc : 1 + a = c) (hc' : 1 + a = c') (hN : 2 + n = N)
    (hN' : 2 + n = N') (r : CH.Cn (G q 1) 2) (z : CH.Cn (G q a) n)
    (h : RelNull (G q c) Q N (cupC q (a := 1) (a' := a) hc hN r z)) :
    RelNull (G q c') Q N' (cupC q (a := 1) (a' := a) hc' hN' r z) := by
  subst hc hc' hN hN'
  exact h

theorem relKillOf : TopRes → FormUniq → OmRes → RelKillOf := by
  intro hTop hFU hOR hSL hCD hZR hAO hON hAR hFL hDW hDL hFC hC1 hDC hCK K _ _ W Z Y q _ _ i π _ D d hd hB r hr hc1 a n z hz hzr
  obtain ⟨B⟩ := hB
  haveI := B.closed
  obtain ⟨m, U, σ, hσ, hU, haff, hcov⟩ := hDC K W Z Y q i π D d B
  obtain ⟨-, hQ, -⟩ := hSL K (pullback i π) Y Y (π ≫ q) (pullback.snd i π) (𝟙 Y)
  exact relNull_cast (π ≫ q) _ _ _ _ r z
    (kill_over hTop hFU hOR hSL hCD hZR hAO hAR hFL hDW hDL hFC hC1 hCK D hQ B.f B.f_nat B.f_u U σ hσ hU haff hcov
      r hr hc1 a n z hz hzr)

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightWordLaplacianPowerBound
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth.WordBd

open GlobalTheory.CompanionTheory.CurveJ (sob_comb)
open GlobalTheory.CompanionTheory.SobOpsPf (sob_bs sob_congr sob_smul sob_sum)
open GlobalTheory.CompanionTheory.SecBd (cls_sum cls_congr cls_eq cls_sub)

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Rw_zero (w : List (Bool × Fin n × Fin n)) : Rw w (0 : Mat n → V) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    show Rd (bs p) (Rw w (0 : Mat n → V)) = 0
    rw [ih]
    funext g
    simp [Rd]

theorem sob_zero : Sob μ (0 : Mat n → V) :=
  ⟨contDiffOn_const, fun w => by rw [Rw_zero]; exact MemLp.zero⟩

theorem cls_zero : cls μ (0 : Mat n → V) = 0 := by
  have h : MemLp (fun y : G n => (0 : Mat n → V) y.val) 2 μ := MemLp.zero
  rw [cls_eq μ h]
  exact MemLp.toLp_zero h

theorem cls_mem {f : Mat n → V} (hf : Sob μ f) : cls μ f ∈ Msob μ V :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem exists_rep (x : Lp V 2 μ) (hx : x ∈ Msob μ V) : ∃ f : Mat n → V, Sob μ f ∧ cls μ f = x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨0, sob_zero, cls_zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨f', hf', rfl⟩ := hy
    have h := sob_comb 1 hf hf'
    refine ⟨_, h.1, ?_⟩
    simpa [Rw] using h.2 []
  | smul a x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h := sob_comb a hf (sob_zero (μ := μ) (V := V))
    refine ⟨_, h.1, ?_⟩
    simpa [Rw, cls_zero] using h.2 []

def rp (x : Msob μ V) : Mat n → V := Classical.choose (exists_rep x.1 x.2)

theorem rp_sob (x : Msob μ V) : Sob μ (rp x) := (Classical.choose_spec (exists_rep x.1 x.2)).1

theorem rp_cls (x : Msob μ V) : cls μ (rp x) = x := (Classical.choose_spec (exists_rep x.1 x.2)).2

def Uniq (μ : Measure (G n)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Prop :=
  ∀ f f' : Mat n → V, Sob μ f → Sob μ f' → cls μ f = cls μ f' → ∀ g ∈ GLs n, f g = f' g

def Xf (p : Bool × Fin n × Fin n) (x : Msob μ V) : Msob μ V :=
  ⟨cls μ (Rd (bs p) (rp x)), cls_mem (sob_bs p (rp_sob x))⟩

theorem Xf_cls (hu : Uniq μ V) (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) (x : Msob μ V)
    (hx : (x : Lp V 2 μ) = cls μ f) : (Xf p x : Lp V 2 μ) = cls μ (Rd (bs p) f) := by
  have e : Set.EqOn (rp x) f (GLs n) := fun g hg =>
    hu _ _ (rp_sob x) hf ((rp_cls x).trans hx) g hg
  exact cls_congr μ ((sob_bs p (rp_sob x)).2 [])
    fun g hg => GlobalTheory.CompanionTheory.RCalc.Rd_congr (bs p) e hg

theorem Xf_comb (hu : Uniq μ V) (p : Bool × Fin n × Fin n) (a : ℂ) (x y : Msob μ V) :
    Xf p (a • x + y) = a • Xf p x + Xf p y := by
  have h := sob_comb a (rp_sob x) (rp_sob y)
  apply Subtype.ext
  have e : ((a • x + y : Msob μ V) : Lp V 2 μ) = cls μ (fun z => a • rp x z + rp y z) := by
    have := h.2 []
    simp only [Rw, id] at this
    rw [this, rp_cls, rp_cls]
    rfl
  rw [Xf_cls hu p h.1 _ e]
  exact h.2 [p]

def X (hu : Uniq μ V) (p : Bool × Fin n × Fin n) : Module.End ℂ (Msob μ V) where
  toFun := Xf p
  map_add' x y := by simpa using Xf_comb hu p 1 x y
  map_smul' a x := by
    have h0 : Xf p (0 : Msob μ V) = 0 := by simpa using Xf_comb hu p 1 0 0
    simpa [h0] using Xf_comb hu p a x 0

theorem X_cls (hu : Uniq μ V) (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) :
    (X hu p ⟨cls μ f, cls_mem hf⟩ : Msob μ V) = ⟨cls μ (Rd (bs p) f), cls_mem (sob_bs p hf)⟩ :=
  Subtype.ext (Xf_cls hu p hf _ rfl)

theorem X_skew (hu : Uniq μ V) (hI : ∀ f f' : Mat n → V, Sob μ f → Sob μ f' → ∀ Y : Mat n,
      ⟪cls μ (Rd Y f), cls μ f'⟫_ℂ = -⟪cls μ f, cls μ (Rd Y f')⟫_ℂ)
    (p : Bool × Fin n × Fin n) (u v : Msob μ V) : ⟪X hu p u, v⟫_ℂ = -⟪u, X hu p v⟫_ℂ := by
  obtain ⟨f, hf, hfu⟩ := exists_rep u.1 u.2
  obtain ⟨f', hf', hfv⟩ := exists_rep v.1 v.2
  have eu : u = ⟨cls μ f, cls_mem hf⟩ := Subtype.ext hfu.symm
  have ev : v = ⟨cls μ f', cls_mem hf'⟩ := Subtype.ext hfv.symm
  rw [eu, ev, X_cls hu p hf, X_cls hu p hf']
  exact hI f f' hf hf' (bs p)

theorem memS {f : Mat n → V} (hf : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []

theorem cls_smul (a : ℂ) {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    cls μ (fun g => a • f g) = a • cls μ f := by
  rw [cls_eq μ h, cls_eq μ (f := fun g => a • f g) (h.const_smul a)]
  exact MemLp.toLp_const_smul a h

theorem X_bracket (hu : Uniq μ V)
    (hB : ∀ f : Mat n → V, Sob μ f → ∀ Y Z, ∀ g ∈ GLs n,
      Rd Y (Rd Z f) g - Rd Z (Rd Y f) g = Rd (Y * Z - Z * Y) f g)
    (i j : Bool × Fin n × Fin n) (c : Bool × Fin n × Fin n → ℝ)
    (hc : bs i * bs j - bs j * bs i = ∑ k, c k • bs k) :
    X hu i * X hu j - X hu j * X hu i = ∑ k, (c k : ℂ) • X hu k := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨f, hf, hfu⟩ := exists_rep u.1 u.2
  have eu : u = ⟨cls μ f, cls_mem hf⟩ := Subtype.ext hfu.symm
  rw [eu]
  apply Subtype.ext
  have hm : ∀ k, MemLp (fun y : G n => (c k : ℂ) • Rd (bs k) f y.val) 2 μ := fun k =>
    ((sob_bs k hf).2 []).const_smul _
  have h1 := cls_sum μ Finset.univ (fun k g => (c k : ℂ) • Rd (bs k) f g) fun k _ => hm k
  have hij : ∀ a b, ((X hu a * X hu b) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 =
      cls μ (Rd (bs a) (Rd (bs b) f)) := fun a b => by
    rw [Module.End.mul_apply, X_cls hu b hf, X_cls hu a (sob_bs b hf)]
  have hs : ∀ k, (((c k : ℂ) • X hu k) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 =
      cls μ (fun g => (c k : ℂ) • Rd (bs k) f g) := fun k => by
    rw [LinearMap.smul_apply, X_cls hu k hf, cls_smul _ (memS (sob_bs k hf))]
    rfl
  rw [LinearMap.sub_apply, Submodule.coe_sub, hij, hij, LinearMap.sum_apply, Submodule.coe_sum]
  simp only [hs]
  rw [← h1.2, ← cls_sub μ (memS (sob_bs i (sob_bs j hf))) (memS (sob_bs j (sob_bs i hf)))]
  refine cls_congr μ ((memS (sob_bs i (sob_bs j hf))).sub (memS (sob_bs j (sob_bs i hf)))) fun g hg => ?_
  rw [hB f hf _ _ g hg, GlobalTheory.CompanionTheory.FcCalc.Ibp.Rd_expand f hc g]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (Complex.coe_smul _ _).symm

theorem word_apply (hu : Uniq μ V) (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) :
    (((w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩ : Msob μ V) : Lp V 2 μ) = cls μ (Rw w f) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    have hw := GlobalTheory.CompanionTheory.SobOpsPf.sob_Rw w hf
    have e : (w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩ = ⟨cls μ (Rw w f), cls_mem hw⟩ := Subtype.ext ih
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, e, X_cls hu p hw]
    rfl

theorem sob_Lap {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap f) := by
  refine sob_congr (sob_smul (-1 : ℂ) (sob_sum Finset.univ hf fun p => sob_bs p (sob_bs p hf))) fun g _ => ?_
  simp [Lap]

theorem lap_apply (hu : Uniq μ V) {f : Mat n → V} (hf : Sob μ f) :
    (-∑ i, X hu i * X hu i) ⟨cls μ f, cls_mem hf⟩ = (⟨cls μ (Lap f), cls_mem (sob_Lap hf)⟩ : Msob μ V) := by
  apply Subtype.ext
  have hm : ∀ p, MemLp (fun y : G n => Rd (bs p) (Rd (bs p) f) y.val) 2 μ := fun p =>
    (sob_bs p (sob_bs p hf)).2 []
  have h1 := cls_sum μ Finset.univ (fun p g => Rd (bs p) (Rd (bs p) f) g) fun p _ => hm p
  have e : cls μ (Lap f) = -∑ p, cls μ (Rd (bs p) (Rd (bs p) f)) := by
    have e1 : Lap f = fun g => (-1 : ℂ) • ∑ p, Rd (bs p) (Rd (bs p) f) g := by
      funext g; simp [Lap]
    rw [e1, cls_smul _ h1.1, h1.2]
    simp
  show ((-∑ i, X hu i * X hu i) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 = cls μ (Lap f)
  rw [e, LinearMap.neg_apply, LinearMap.sum_apply, Submodule.coe_neg, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Module.End.mul_apply, X_cls hu p hf, X_cls hu p (sob_bs p hf)]

theorem pow_apply (hu : Uniq μ V) (j : ℕ) {f : Mat n → V} (hf : Sob μ f) :
    (((-∑ i, X hu i * X hu i) ^ j) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 = cls μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, lap_apply hu hf, ih (sob_Lap hf)]
    rfl

theorem word_bound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    LgFacts → Unimod → RCalc → AlgEst → ClsFacts → IbpSob →
    ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f : Mat n → V, Sob μ f →
      ‖cls μ (Rw w f)‖ ≤ C * ∑ j ∈ range (w.length + 1), ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ := by
  intro n _ _ μ _ V _ _ _ hL hU hR hA hC hI w
  have hu : Uniq μ V := fun f f' hf hf' e g hg =>
    (hC n μ V hU).1 f f' hf.1.continuousOn hf'.1.continuousOn (hf.2 []) (hf'.2 []) e g hg
  choose c hc using fun ij : (Bool × Fin n × Fin n) × (Bool × Fin n × Fin n) =>
    GlobalTheory.CompanionTheory.FcCalc.Ibp.exists_coeff (bs ij.1 * bs ij.2 - bs ij.2 * bs ij.1)
  obtain ⟨C, hCb⟩ := hA (Msob μ V) (Bool × Fin n × Fin n) (X hu) (fun i j k => c (i, j) k)
    (X_skew hu fun f f' hf hf' Y => hI n μ V hL hU hR f f' hf hf' Y)
    (fun i j => X_bracket hu (fun f hf Y Z g hg => ((hR n).1 V f hf.1).2.1 Y Z g hg) i j _ (hc (i, j))) w
  refine ⟨C, fun f hf => ?_⟩
  have h := hCb ⟨cls μ f, cls_mem hf⟩
  have e1 : ‖cls μ (Rw w f)‖ = ‖(w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩‖ := by
    rw [← word_apply hu w hf]; rfl
  rw [e1]
  refine h.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_apply hu j hf]
  rfl

end GlobalTheory.CompanionTheory.FcSmooth.WordBd
end
end

