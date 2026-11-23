module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
section
open MeasureTheory Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.GLUnimod

variable {n : ℕ}

noncomputable def dg (d : Fin n → ℂˣ) : GL (Fin n) ℂ where
  val := diagonal fun i => (d i : ℂ)
  inv := diagonal fun i => (((d i)⁻¹ : ℂˣ) : ℂ)
  val_inv := by simp [diagonal_mul_diagonal, diagonal_one]
  inv_val := by simp [diagonal_mul_diagonal, diagonal_one]

theorem dg_mul (d e : Fin n → ℂˣ) : dg (d * e) = dg d * dg e := by
  apply Units.ext
  simp [dg, diagonal_mul_diagonal]

theorem dg_one : dg (1 : Fin n → ℂˣ) = 1 := by
  apply Units.ext
  simp [dg, diagonal_one]

noncomputable def pm (σ : Equiv.Perm (Fin n)) : GL (Fin n) ℂ where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.one_apply]
  inv_val := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext i j
    simp [Matrix.one_apply]

theorem pm_mul_dg (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂˣ) :
    pm σ * dg d = dg (d ∘ σ) * pm σ := by
  ext1
  ext i j
  simp only [pm, dg, Units.val_mul, mul_diagonal, diagonal_mul, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Function.comp_apply]
  split_ifs with h
  · subst h
    ring
  · ring

noncomputable def tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) : GL (Fin n) ℂ where
  val := transvection i j c
  inv := transvection i j (-c)
  val_inv := by rw [transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [transvection_mul_transvection_same _ _ hij]; simp

theorem tv_mul {i j : Fin n} (hij : i ≠ j) (c : ℂ) : tv hij c * tv hij c = tv hij (2 * c) := by
  ext1
  simp only [tv, Units.val_mul]
  rw [transvection_mul_transvection_same _ _ hij, two_mul]

theorem dg_mul_tv {i j : Fin n} (hij : i ≠ j) (c : ℂ) (d : Fin n → ℂˣ) (hi : (d i : ℂ) = 2)
    (hj : (d j : ℂ) = 1) : dg d * tv hij c = tv hij (2 * c) * dg d := by
  ext1
  ext k l
  simp only [dg, tv, Units.val_mul, transvection, diagonal_mul, mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hk : i = k <;> by_cases hl : j = l
  · subst hk hl
    simp [hij, hi, hj]
  · subst hk
    simp [hl]
    split_ifs with h <;> simp only [h]
  · subst hl
    simp [hk]
    split_ifs with h <;> simp only [h]
  · simp [hk, hl]
    split_ifs with h <;> simp only [h]

theorem char_ne_zero {H : Type*} [Group H] (χ : H →* ℝ≥0) (g : H) : χ g ≠ 0 := by
  intro h
  have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem char_tv (χ : GL (Fin n) ℂ →* ℝ≥0) {i j : Fin n} (hij : i ≠ j) (c : ℂ) :
    χ (tv hij c) = 1 := by
  have h1 : χ (tv hij c) * χ (tv hij c) = χ (tv hij (2 * c)) := by rw [← map_mul, tv_mul]
  let d : Fin n → ℂˣ := fun k => if k = i then Units.mk0 2 two_ne_zero else 1
  have hi : (d i : ℂ) = 2 := by simp [d]
  have hj : (d j : ℂ) = 1 := by simp [d, hij.symm]
  have h2 : χ (dg d) * χ (tv hij c) = χ (tv hij (2 * c)) * χ (dg d) := by
    rw [← map_mul, ← map_mul, dg_mul_tv hij c d hi hj]
  have h3 : χ (tv hij c) = χ (tv hij (2 * c)) := by
    rw [mul_comm (χ (tv hij (2 * c)))] at h2
    exact mul_left_cancel₀ (char_ne_zero χ _) h2
  have h4 : χ (tv hij c) * χ (tv hij c) = χ (tv hij c) * 1 := by rw [mul_one, h1, h3]
  exact mul_left_cancel₀ (char_ne_zero χ _) h4

theorem char_dg (χ : GL (Fin n) ℂ →* ℝ≥0) (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1)
    (d : Fin n → ℂˣ) : χ (dg d) = 1 := by
  let D : (Fin n → ℂˣ) →* GL (Fin n) ℂ :=
    { toFun := dg, map_one' := dg_one, map_mul' := dg_mul }
  have hperm : ∀ σ : Equiv.Perm (Fin n), χ (dg (d ∘ σ)) = χ (dg d) := by
    intro σ
    have h := congrArg χ (pm_mul_dg σ d)
    rw [map_mul, map_mul, mul_comm (χ (pm σ))] at h
    exact (mul_right_cancel₀ (char_ne_zero χ (pm σ)) h).symm
  obtain ⟨v, hv_def⟩ : ∃ v : Fin n → ℂˣ, v = ∏ σ : Equiv.Perm (Fin n), d ∘ σ := ⟨_, rfl⟩
  have hv : ∀ k l, v k = v l := by
    intro k l
    rw [hv_def, Finset.prod_apply, Finset.prod_apply]
    exact Fintype.prod_equiv (Equiv.mulRight (Equiv.swap k l)) _ _
      (fun σ => by simp [Equiv.Perm.mul_apply, Equiv.swap_apply_right])
  have hcent : ∀ g, dg v * g = g * dg v := by
    intro g
    ext1
    ext k l
    simp only [dg, Units.val_mul, diagonal_mul, mul_diagonal]
    rw [hv k l, mul_comm]
  have h1 : χ (dg v) = 1 := hz _ hcent
  have h2 : χ (dg v) = χ (dg d) ^ (Fintype.card (Equiv.Perm (Fin n))) := by
    have e : χ (dg v) = (χ.comp D) v := rfl
    rw [e, hv_def, map_prod]
    simp only [MonoidHom.comp_apply, D, MonoidHom.coe_mk, OneHom.coe_mk, hperm]
    rw [Finset.prod_const, Finset.card_univ]
  have hm : Fintype.card (Equiv.Perm (Fin n)) ≠ 0 := Fintype.card_ne_zero
  rw [h1] at h2
  exact (pow_eq_one_iff_of_nonneg (by simp) hm).1 h2.symm

theorem char_eq_one (χ : GL (Fin n) ℂ →* ℝ≥0)
    (hz : ∀ z : GL (Fin n) ℂ, (∀ g, z * g = g * z) → χ z = 1) (g : GL (Fin n) ℂ) : χ g = 1 := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : GL (Fin n) ℂ, (u : Matrix (Fin n) (Fin n) ℂ) = M → χ u = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) ?_ ?_ ?_ ?_ g rfl
  · exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  · intro D hD u hu
    rw [det_diagonal] at hD
    have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = dg (fun i => Units.mk0 (D i) (hD' i)) := by
      ext1
      simp [hu, dg]
    rw [hu']
    exact char_dg χ hz _
  · intro t u hu
    have hu' : u = tv t.hij t.c := by
      ext1
      simp [hu, tv, Matrix.TransvectionStruct.toMatrix]
    rw [hu']
    exact char_tv χ t.hij t.c
  · intro A B hA hB hPA hPB u hu
    obtain ⟨a, rfl⟩ : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)
    obtain ⟨b, rfl⟩ : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.2 hB)
    have hu' : u = a * b := by
      ext1
      simp [hu]
    rw [hu', map_mul, hPA a rfl, hPB b rfl, one_mul]

theorem unimod : PositivityTheory.RgBcC.Unimod := by
  intro n _ _ μ _
  haveI : T2Space (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (T2Space (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (PositivityTheory.RgTw.G n) :=
    (Units.isClosedEmbedding_embedProduct :
      Topology.IsClosedEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).locallyCompactSpace
  haveI : SecondCountableTopology (PositivityTheory.RgTw.G n) :=
    (Units.isEmbedding_embedProduct :
      Topology.IsEmbedding (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ))).secondCountableTopology
  have hmap : ∀ g : PositivityTheory.RgTw.G n,
      Measure.map (· * g) μ = Measure.modularCharacter g • μ := by
    intro g
    have e1 := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ g
    rw [← e2] at e1
    exact e1
  have hχ : ∀ g : PositivityTheory.RgTw.G n, Measure.modularCharacter g = 1 := by
    refine char_eq_one Measure.modularCharacter ?_
    intro z hz
    have hc : Measure.map (· * z) μ = μ := by
      have h : (fun x => x * z) = (fun x => z * x) := funext fun x => (hz x).symm
      rw [h, map_mul_left_eq_self]
    have e2 := Measure.modularCharacterFun_eq_haarScalarFactor μ z
    simp only [hc, Measure.haarScalarFactor_self] at e2
    exact e2
  have hR : μ.IsMulRightInvariant := ⟨fun g => by rw [hmap, hχ g, one_smul]⟩
  exact ⟨hR, GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ⟩

end GlobalTheory.CompanionTheory.GLUnimod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedNoetherian
section
set_option autoImplicit false

noncomputable section

open DirectSum

namespace GlobalTheory.CompanionTheory.GE.GNoeth

variable {R : Type} [CommRing R] {M : ℕ → Type} [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)]

def shiftOp (T : ∀ e, M e →ₗ[R] M (e + 1)) : Module.End R (⨁ e, M e) :=
  DirectSum.toModule R ℕ _ (fun e => DirectSum.lof R ℕ M (e + 1) ∘ₗ T e)

theorem shiftOp_lof (T : ∀ e, M e →ₗ[R] M (e + 1)) (e : ℕ) (x : M e) :
    shiftOp T (DirectSum.lof R ℕ M e x) = DirectSum.lof R ℕ M (e + 1) (T e x) := by
  simp only [shiftOp, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem shiftOp_succ (T : ∀ e, M e →ₗ[R] M (e + 1)) (y : ⨁ e, M e) (e : ℕ) :
    shiftOp T y (e + 1) = T e (y e) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of R, shiftOp_lof, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    by_cases h : i = e
    · subst h; simp [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (by omega), map_zero]
  | add a b ha hb => simp only [map_add (f := _), DirectSum.add_apply, ha, hb]

theorem shiftOp_zero (T : ∀ e, M e →ₗ[R] M (e + 1)) (y : ⨁ e, M e) :
    shiftOp T y 0 = 0 := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of R, shiftOp_lof, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  | add a b ha hb => simp only [map_add (f := _), DirectSum.add_apply, ha, hb, add_zero]

theorem eventually_zero (f : ⨁ e, M e) : ∃ n : ℕ, ∀ e, n ≤ e → f e = 0 := by
  induction f using DirectSum.induction_on with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | of i x =>
    refine ⟨i + 1, fun e he => DirectSum.of_eq_of_ne _ _ _ (by omega)⟩
  | add a b ha hb =>
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    exact ⟨max n m, fun e he => by
      rw [DirectSum.add_apply, hn e (le_of_max_le_left he), hm e (le_of_max_le_right he), add_zero]⟩

theorem lof_mem {L : ∀ e, Submodule R (M e)} (i : ℕ) {x : M i} (hx : x ∈ L i) (j : ℕ) :
    DirectSum.lof R ℕ M i x j ∈ L j := by
  rw [DirectSum.lof_eq_of]
  by_cases h : i = j
  · subst h; simpa [DirectSum.of_eq_same] using hx
  · rw [DirectSum.of_eq_of_ne _ _ _ (by omega)]; exact zero_mem _

theorem gradedNoeth : GradedNoeth := by
  classical
  intro R _ _ k M _ _ _ T hT d hgen L hL
  have hEc : ∀ i j, shiftOp (T i) * shiftOp (T j) = shiftOp (T j) * shiftOp (T i) := by
    intro i j
    apply DirectSum.linearMap_ext
    intro e
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Module.End.mul_apply, shiftOp_lof]
    rw [hT i j e x]
  let Sset : Finset (Module.End R (⨁ e, M e)) := Finset.univ.image (fun i => shiftOp (T i))
  have hSset : ∀ a, a ∈ (Sset : Set (Module.End R (⨁ e, M e))) → ∃ i, shiftOp (T i) = a := by
    intro a ha
    simpa [Sset] using ha
  have hcomm : ∀ a ∈ (Sset : Set (Module.End R (⨁ e, M e))),
      ∀ b ∈ (Sset : Set (Module.End R (⨁ e, M e))), a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := hSset a ha
    obtain ⟨j, rfl⟩ := hSset b hb
    exact hEc i j
  let S := Algebra.adjoin R (Sset : Set (Module.End R (⨁ e, M e)))
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin R (by
    intro a ha b hb _
    exact hcomm a ha b hb)
  letI : CommRing S := { (inferInstance : Ring S) with mul_comm := mul_comm' }
  haveI : Algebra.FiniteType R S :=
    (Subalgebra.fg_iff_finiteType S).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have hEmem : ∀ i, shiftOp (T i) ∈ S := fun i => Algebra.subset_adjoin (by simp [Sset])
  have hfin : ∀ e, ∃ g : Finset (M e), Submodule.span R (g : Set (M e)) = ⊤ := fun e =>
    Module.Finite.fg_top (R := R) (M := M e)
  choose gens hgens using hfin
  let G0 : Set (⨁ e, M e) :=
    ⋃ e ∈ Finset.range (d + 1), DirectSum.lof R ℕ M e '' (gens e : Set (M e))
  have hG0 : G0.Finite :=
    (Finset.finite_toSet _).biUnion fun e _ => (Finset.finite_toSet _).image _
  let P : Submodule S (⨁ e, M e) := Submodule.span S G0
  have hbase : ∀ e, e ≤ d → ∀ m : M e, DirectSum.lof R ℕ M e m ∈ P := by
    intro e he m
    have hm : m ∈ Submodule.span R (gens e : Set (M e)) := by rw [hgens e]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Set.mem_biUnion (Finset.mem_range.2 (by omega)) ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact P.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem P c hx
  have hall : ∀ e (m : M e), DirectSum.lof R ℕ M e m ∈ P := by
    intro e
    induction e with
    | zero => exact hbase 0 (Nat.zero_le _)
    | succ e ih =>
      by_cases he : e + 1 ≤ d
      · exact hbase _ he
      · intro m
        have hm : m ∈ ⨆ i, LinearMap.range (T i e) := by rw [hgen e (by omega)]; trivial
        refine Submodule.iSup_induction _ (motive := fun m => DirectSum.lof R ℕ M (e + 1) m ∈ P)
          hm ?_ ?_ ?_
        · intro i x hx
          obtain ⟨y, rfl⟩ := hx
          have h1 : DirectSum.lof R ℕ M (e + 1) (T i e y) =
              (⟨shiftOp (T i), hEmem i⟩ : S) • DirectSum.lof R ℕ M e y :=
            (shiftOp_lof (T i) e y).symm
          rw [h1]
          exact P.smul_mem _ (ih y)
        · simp
        · intro x y hx hy
          rw [map_add (f := _)]
          exact P.add_mem hx hy
  have hP : ∀ y : ⨁ e, M e, y ∈ P := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => exact P.zero_mem
    | of i x => rw [← DirectSum.lof_eq_of R]; exact hall i x
    | add a b ha hb => exact P.add_mem ha hb
  have htop : P = ⊤ := eq_top_iff.2 fun y _ => hP y
  haveI : Module.Finite S (⨁ e, M e) := ⟨Submodule.fg_def.2 ⟨G0, hG0, htop⟩⟩
  have hstab : ∀ x ∈ S, ∀ y : ⨁ e, M e, (∀ e, y e ∈ L e) → ∀ e, x y e ∈ L e := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hSset x hx
      intro y hy e
      cases e with
      | zero => rw [shiftOp_zero]; exact zero_mem _
      | succ e => rw [shiftOp_succ]; exact hL i e (Submodule.mem_map_of_mem (hy e))
    | algebraMap r =>
      intro y hy e
      rw [Module.algebraMap_end_apply, DirectSum.smul_apply]
      exact (L e).smul_mem r (hy e)
    | add x x' _ _ hx hx' =>
      intro y hy e
      rw [LinearMap.add_apply, DirectSum.add_apply]
      exact (L e).add_mem (hx y hy e) (hx' y hy e)
    | mul x x' _ _ hx hx' =>
      intro y hy e
      rw [Module.End.mul_apply]
      exact hx _ (hx' y hy) e
  let N : Submodule S (⨁ e, M e) :=
    { carrier := {y | ∀ e, y e ∈ L e}
      add_mem' := fun {a b} ha hb e => by
        rw [DirectSum.add_apply]; exact (L e).add_mem (ha e) (hb e)
      zero_mem' := fun e => by rw [DirectSum.zero_apply]; exact zero_mem _
      smul_mem' := fun s y hy => hstab s.1 s.2 y hy }
  have hQ : ∀ e, ∀ x ∈ S, ∃ c : R, ∀ y : ⨁ e, M e, (∀ e', y e' ∈ L e') →
      x y (e + 1) - c • y (e + 1) ∈ ⨆ i, (L e).map (T i e) := by
    intro e x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hSset x hx
      refine ⟨0, fun y hy => ?_⟩
      rw [zero_smul, sub_zero, shiftOp_succ]
      exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (hy e))
    | algebraMap r =>
      refine ⟨r, fun y hy => ?_⟩
      rw [Module.algebraMap_end_apply, DirectSum.smul_apply, sub_self]
      exact zero_mem _
    | add x x' _ _ hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hx'
      refine ⟨c + c', fun y hy => ?_⟩
      have h2 := Submodule.add_mem _ (hc y hy) (hc' y hy)
      convert h2 using 1
      rw [LinearMap.add_apply, DirectSum.add_apply, add_smul]
      abel
    | mul x x' _ hx'S hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hx'
      refine ⟨c * c', fun y hy => ?_⟩
      have h2 := Submodule.add_mem _ (hc _ (hstab x' hx'S y hy)) (Submodule.smul_mem _ c (hc' y hy))
      convert h2 using 1
      rw [Module.End.mul_apply, smul_sub, mul_smul]
      abel
  obtain ⟨F, hF⟩ := IsNoetherian.noetherian N
  choose nf hnf using (eventually_zero : ∀ f : ⨁ e, M e, ∃ n : ℕ, ∀ e, n ≤ e → f e = 0)
  refine ⟨F.sup nf, fun e he => le_antisymm (iSup_le fun i => hL i e) ?_⟩
  intro x hx
  let Ne : Submodule S (⨁ e, M e) :=
    { carrier := {y | y ∈ N ∧ y (e + 1) ∈ ⨆ i, (L e).map (T i e)}
      add_mem' := fun {a b} ha hb => ⟨N.add_mem ha.1 hb.1, by
        rw [DirectSum.add_apply]; exact Submodule.add_mem _ ha.2 hb.2⟩
      zero_mem' := ⟨N.zero_mem, by rw [DirectSum.zero_apply]; exact zero_mem _⟩
      smul_mem' := fun s y hy => by
        obtain ⟨c, hc⟩ := hQ e s.1 s.2
        refine ⟨N.smul_mem s hy.1, ?_⟩
        have h3 := Submodule.add_mem _ (hc y hy.1) (Submodule.smul_mem _ c hy.2)
        rw [sub_add_cancel] at h3
        exact h3 }
  have hNle : N ≤ Ne := by
    rw [← hF, Submodule.span_le]
    intro f hf
    refine ⟨by rw [← hF]; exact Submodule.subset_span hf, ?_⟩
    have h4 : nf f ≤ F.sup nf := Finset.le_sup hf
    rw [hnf f (e + 1) (by omega)]
    exact zero_mem _
  have hxN : DirectSum.lof R ℕ M (e + 1) x ∈ N := fun j => lof_mem (e + 1) hx j
  have h5 := (hNle hxN).2
  rwa [DirectSum.lof_eq_of, DirectSum.of_eq_same] at h5

end GlobalTheory.CompanionTheory.GE.GNoeth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquiv
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.JacquetEquiv

theorem nonempty_jacquetRep_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  intro F _ _ _ _ n γ V V' _ _ _ _ π π' φ
  let e : V ≃ₗ[ℂ] V' := φ.toLinearEquiv
  have he : ∀ g, (e : V →ₗ[ℂ] V') ∘ₗ π g = π' g ∘ₗ (e : V →ₗ[ℂ] V') := by
    intro g
    rw [Representation.Equiv.toLinearEquiv_toLinearMap]
    exact φ.toIntertwiningMap.isIntertwining' g
  have he' := LinearEquiv.isIntertwining_symm_isIntertwining he
  let f : Representation.IntertwiningMap (MonoidHom.comp π (unipotentRadical F n γ).subtype) (MonoidHom.comp π' (unipotentRadical F n γ).subtype) :=
    ⟨(e : V →ₗ[ℂ] V'), fun x => he x⟩
  let g : Representation.IntertwiningMap (MonoidHom.comp π' (unipotentRadical F n γ).subtype) (MonoidHom.comp π (unipotentRadical F n γ).subtype) :=
    ⟨(e.symm : V' →ₗ[ℂ] V), fun x => he' x⟩
  let M := Representation.Coinvariants.map _ _ f
  let M' := Representation.Coinvariants.map _ _ g
  have hMM' : M ∘ₗ M' = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.apply_symm_apply v
  have hM'M : M' ∘ₗ M = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.symm_apply_apply v
  let E := LinearEquiv.ofLinearMap (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) M M' hMM' hM'M
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro m
  apply Representation.Coinvariants.hom_ext
  ext u
  have hc : f ((π (m : GL (Fin n) F)) u) = (π' (m : GL (Fin n) F)) (f u) := LinearMap.congr_fun (he m) u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.coe_ofLinearMap, jacquetRep,
    GroundTheory.Automorphic.Parabolic.twist_apply, map_smul, GroundTheory.Automorphic.Parabolic.jacquetAction,
    MonoidHom.coe_mk, OneHom.coe_mk, GroundTheory.Automorphic.coinvariantsTranslate_mk, M,
    Representation.Coinvariants.map_mk]
  rw [hc]

end GlobalTheory.CompanionTheory.JacquetEquiv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentIdentityMorphismCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_identity_morphism_compat : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) (U : Cov q)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {⊤}) (hQ' : Q' = St ⊤ {⊤}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  first | exact @GlobalTheory.CompanionTheory.BcCov.bc_cover | exact GlobalTheory.CompanionTheory.BcCov.bc_cover | (intros; apply GlobalTheory.CompanionTheory.BcCov.bc_cover <;> assumption)
end

