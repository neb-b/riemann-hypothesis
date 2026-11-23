module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0340
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectiveChartAffineCoords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellLeviUnipotentConjugationStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

-- Re-elaborate the proof so its type uses the current `leviEmb` instance arguments.
namespace GlobalTheory.CompanionTheory.Rodier.LeviPartPort

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

end GlobalTheory.CompanionTheory.Rodier.LeviPartPort

alias GlobalTheory.T.open_cell_levi_unipotent_conjugation :=
  GlobalTheory.CompanionTheory.Rodier.LeviPartPort.levi_part
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivial
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.TensorIrr

theorem nontrivial_space_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.ext (Subsingleton.elim _ _))

theorem nontrivial_piTensorProduct_of_nontrivial {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  have hv : ∀ i, ∃ v : V i, v ≠ 0 := fun i => exists_ne 0
  choose v hv using hv
  have hf : ∀ i, ∃ f : Module.Dual ℂ (V i), f (v i) ≠ 0 := fun i => by
    by_contra hc
    exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1
      fun f => not_not.1 (not_exists.1 hc f))
  choose f hf using hf
  let F : (Π i, V i) →ₘₗ[ℂ] ℂ := (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f
  have hF : PiTensorProduct.lift F (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [PiTensorProduct.lift.tprod]
    simpa [F] using Finset.prod_ne_zero_iff.2 fun i _ => hf i
  refine ⟨PiTensorProduct.tprod ℂ v, 0, fun h => hF ?_⟩
  rw [h, map_zero]

theorem nontrivial_piTensorProduct_irrGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  intro k _ _ _ _ h x
  have : ∀ a, Nontrivial (x a).2.rep.V := fun a =>
    nontrivial_space_of_isIrreducible _ (x a).2.rep.irr
  exact nontrivial_piTensorProduct_of_nontrivial

end GlobalTheory.CompanionTheory.TensorIrr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectiveChartAffineCoordsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_affine_coords : KH.LocGr → KH.PolyTf → KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] {N : ℕ} (i : X ⟶ PSpace K N) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K),
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, uy i y k)) →
    ∀ (V : X.Opens) (hV : ∀ S : Finset (Fin (n + 2)), V ≤ ⨅ k ∈ S, uy i y k) (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (g : Fin (n + 1) → Γ(X, ⨅ k ∈ Finset.univ, uy i y k)), (∀ k, IsUnit (g k)) →
    ∀ (ĝ : Fin (n + 1) → ∀ T : (capS (wK q i y (n + 2)) Finset.univ).FullSubcategory, T.obj.B),
    (∀ k T (h : InU (⨅ k ∈ Finset.univ, uy i y k) T.obj), Ideal.Quotient.mk _ (ĝ k T) = ev T.obj h (g k)) →
    ∀ (c0 : HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS (wK q i y (n + 2)) Finset.univ) (n + 1)),
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      (cupListC ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q)) fun k =>
        dlogC (capS (wK q i y (n + 2)) Finset.univ) (n + 2) (ĝ k)) c0 →
    ∀ (ω : ∀ j, HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS (wK q i y (n + 2)) (Finset.univ.erase j)) (n + 1))
      (f : CH.Cn (CH.modF ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q))) n),
    (∀ σ, f σ ∈ (thFil (smFun X q) n).S _) → (∀ σ, CH.d _ n f σ ∈ (thFil (smFun X q) ((n : ℤ) + 1)).S _) →
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι) (CH.d _ n f)
      (c0 - ∑ j, ((resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS_univ_le (wK q i y (n + 2)) (Finset.univ.erase j))).pull (n + 1)) (ω j)) →
    ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
      (∀ j, x j ∈ jacSpan (hV (Finset.univ.erase j)) (RingHom.id _) (fun k => D k) id) ∧
      (∀ k, η k ∈ jacSpan (hV Finset.univ) (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
      (Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k) ∨
        -(Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det) =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k)) := by
  first | exact @GlobalTheory.CompanionTheory.ConeTransfer.main | exact GlobalTheory.CompanionTheory.ConeTransfer.main | (intros; apply GlobalTheory.CompanionTheory.ConeTransfer.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.QdetCoeff

theorem coeff_mem_span_values {M : Type*} [AddCommGroup M] [Module ℂ M] (n : ℕ) (a : ℕ → M)
    (f : ℂ → M) (hf : ∀ u : ℂ, f u = ∑ k ∈ Finset.range (n + 1), u ^ k • a k) (k : ℕ) (hk : k ≤ n) :
    a k ∈ Submodule.span ℂ (Set.range f) := by
  set v : Fin (n + 1) → ℂ := fun i => ((i : ℕ) : ℂ) with hv
  have hinj : Function.Injective v := by
    intro i j h
    simp only [hv, Nat.cast_inj] at h
    exact Fin.ext h
  set V := Matrix.vandermonde v
  have hdet : IsUnit V.det := (Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  set k' : Fin (n + 1) := ⟨k, by omega⟩
  have key : ∑ i : Fin (n + 1), V⁻¹ k' i • f (v i) = a k := by
    simp_rw [hf, Finset.sum_range (fun j => _ • a j), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have : ∀ j : Fin (n + 1), ∑ i, V⁻¹ k' i * v i ^ (j : ℕ) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) k' j := by
      intro j
      rw [← hWV, Matrix.mul_apply]
      rfl
    simp_rw [this, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp [k']
  rw [← key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩)


open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
theorem qdet_eq_sum_coeff {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (w : ℂ) :
    Formalism.REAL.qdet E w = ∑ j ∈ Finset.range (n + 1), w ^ j • (qdetPoly E).coeff j := by
  rw [← evU_qdetPoly E w, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]

open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists in
theorem qdetPoly_coeff_top {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) :
    (qdetPoly E).coeff n = 1 := by
  rw [coeff_qdetPoly_top E n (by omega), (prod_linear n _).2.1]

theorem qdet_shift_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (c : ℂ),
    ∃ a : ℕ → A, a n = 1 ∧ (∀ k, a k ∈ Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet X (u + c))) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
  intro A _ _ n X c
  set b : ℕ → A := fun j => (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly X).coeff j with hb
  set a : ℕ → A := fun k => ∑ j ∈ Finset.range (n + 1), (c ^ (j - k) * (Nat.choose j k : ℂ)) • b j with ha
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X (u + c) = ∑ k ∈ Finset.range (n + 1), u ^ k • a k := by
    intro u
    rw [qdet_eq_sum_coeff]
    have hj : ∀ j ∈ Finset.range (n + 1), (u + c) ^ j =
        ∑ m ∈ Finset.range (n + 1), u ^ m * (c ^ (j - m) * (Nat.choose j m : ℂ)) := by
      intro j hj
      rw [add_pow]
      have hsub : Finset.range (j + 1) ⊆ Finset.range (n + 1) := by
        have hj' := Finset.mem_range.mp hj
        intro m hm
        have hm' := Finset.mem_range.mp hm
        exact Finset.mem_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      · exact Finset.sum_congr rfl fun m _ => by ring
      · intro m _ hm
        simp only [Finset.mem_range, not_lt] at hm
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [Finset.sum_congr rfl fun j hjm => by rw [hj j hjm]]
    simp_rw [ha, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine ⟨a, ?_, ?_, hexp⟩
  · simp only [ha]
    rw [Finset.sum_eq_single n]
    · simp [hb, qdetPoly_coeff_top]
    · intro j hj hjn
      simp only [Finset.mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · intro h; simp at h
  · intro k
    by_cases hk : k ≤ n
    · exact coeff_mem_span_values n a _ hexp k hk
    · have : a k = 0 := by
        simp only [ha]
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [this]; exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.CTFin.QdetCoeff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompression
section
open Finset

namespace GlobalTheory.CompanionTheory.LevelCompress

open PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def lowCount (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

theorem lowCount_lt (lev : Fin n → ℕ) (a : Fin n) : lowCount lev a < n := by
  have h : (univ.filter fun b => lev b < lev a).card < (univ : Finset (Fin n)).card :=
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, lt_irrefl (lev a)⟩)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem lowCount_le_of_le {lev : Fin n → ℕ} {a b : Fin n} (h : lev a ≤ lev b) :
    lowCount lev a ≤ lowCount lev b := by
  unfold lowCount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 h⟩

theorem lowCount_lt_of_lt {lev : Fin n → ℕ} {a b : Fin n} (h : lev a < lev b) :
    lowCount lev a < lowCount lev b := by
  unfold lowCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ a, h⟩
    · simp only [Finset.mem_filter, lt_irrefl, and_false, not_false_eq_true]
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.trans h⟩

theorem lowCount_lt_iff {lev : Fin n → ℕ} {a b : Fin n} :
    lowCount lev a < lowCount lev b ↔ lev a < lev b := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (lowCount_le_of_le (not_lt.1 h')))
  · exact lowCount_lt_of_lt

theorem rhoU_lowCount (lev : Fin n → ℕ) : rhoU (lowCount lev) = rhoU lev := by
  funext a
  simp only [rhoU, lowCount_lt_iff]

theorem muQ_lowCount (lam : Fin n → ℤ) (lev : Fin n → ℕ) : muQ lam (lowCount lev) = muQ lam lev := by
  unfold muQ
  rw [rhoU_lowCount]

theorem isLev_lowCount {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    IsLev lam (lowCount lev) := by
  refine ⟨fun a b hab => lowCount_le_of_le (h.1 hab), fun a b hab => h.2 a b ?_⟩
  rcases lt_trichotomy (lev a) (lev b) with h1 | h1 | h1
  · exact absurd hab (ne_of_lt (lowCount_lt_of_lt h1))
  · exact h1
  · exact absurd hab (ne_of_gt (lowCount_lt_of_lt h1))

theorem exists_compress (lam : Fin n → ℤ) (lev : Fin n → ℕ) (h : IsLev lam lev) :
    ∃ l : Fin n → Fin n, (IsLev lam fun a => (l a : ℕ)) ∧ (muQ lam fun a => (l a : ℕ)) = muQ lam lev := by
  exact ⟨fun a => ⟨lowCount lev a, lowCount_lt lev a⟩, isLev_lowCount h, muQ_lowCount lam lev⟩

theorem muQ_mem_harmSet {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    muQ lam lev ∈ harmSet lam := by
  obtain ⟨l, hl, he⟩ := exists_compress lam lev h
  unfold harmSet
  rw [Finset.mem_image]
  refine ⟨l, ?_, he⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hl

end GlobalTheory.CompanionTheory.LevelCompress
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishingOfGradedNoetherianStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_vanishing_of_graded_noetherian : GradedNoeth → UniformVanishing := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | exact GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | (intros; apply GlobalTheory.CompanionTheory.GE.UV.uniformVanishing <;> assumption)
end

