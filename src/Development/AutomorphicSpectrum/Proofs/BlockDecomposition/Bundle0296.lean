module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0290
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescends
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.SumDesc

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {I : Type 1} [DecidableEq I]

def sumPM (P : I → PM.{1} K ι) : PM.{1} K ι where
  M S := ⨁ i, (P i).M S
  res h := DirectSum.lmap fun i => (P i).res h
  res_id S h x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ _ = _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_id]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  res_comp h h' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_comp]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (P : I → PM.{1} K ι)

def pr (i : I) (m : ℕ) : (sumPM P).cech.X m →ₗ[K] (P i).cech.X m :=
  LinearMap.pi fun t => (DirectSum.component K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

def inc (i : I) (m : ℕ) : (P i).cech.X m →ₗ[K] (sumPM P).cech.X m :=
  LinearMap.pi fun t => (DirectSum.lof K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

theorem component_res {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (sumPM P).M S) :
    DirectSum.component K I (fun j => (P j).M T) i ((sumPM P).res h x) =
      (P i).res h (DirectSum.component K I (fun j => (P j).M S) i x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    change DirectSum.component K I _ i (DirectSum.lmap _ _) = _
    rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
    by_cases e : j = i
    · subst e
      simp
    · simp [DirectSum.component.of, e]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem res_lof {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (P i).M S) :
    (sumPM P).res h (DirectSum.lof K I (fun j => (P j).M S) i x) =
      DirectSum.lof K I (fun j => (P j).M T) i ((P i).res h x) := DirectSum.lmap_lof _ _ _

theorem pr_d (i : I) (m : ℕ) (z : (sumPM P).cech.X m) :
    pr P i (m + 1) ((sumPM P).cech.d m z) = (P i).cech.d m (pr P i m z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1

theorem inc_d (i : I) (m : ℕ) (y : (P i).cech.X m) :
    inc P i (m + 1) ((P i).cech.d m y) = (sumPM P).cech.d m (inc P i m y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (res_lof P _ i _).symm

theorem cochain_ext {m : ℕ} {z : (sumPM P).cech.X m} (h : ∀ i, pr P i m z = 0) : z = 0 := by
  funext t
  refine DFinsupp.ext fun i => ?_
  exact congrFun (h i) t

theorem pr_aug (i : I) (x : (sumPM P).M ∅) :
    pr P i 0 ((sumPM P).aug x) = (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) := by
  funext t
  exact component_res P _ i _

theorem aug_lof (i : I) (x : (P i).M ∅) :
    (sumPM P).aug (DirectSum.lof K I (fun j => (P j).M ∅) i x) = inc P i 0 ((P i).aug x) := by
  funext t
  exact res_lof P _ i _

theorem pr_inc_self (i : I) (m : ℕ) (y : (P i).cech.X m) : pr P i m (inc P i m y) = y := by
  funext t
  exact DirectSum.component.lof_self (M := fun j => (P j).M (ent t)) K i (y t)

theorem pr_inc_ne {i j : I} (e : j ≠ i) (m : ℕ) (y : (P j).cech.X m) : pr P i m (inc P j m y) = 0 := by
  funext t
  change DirectSum.component K I (fun j => (P j).M (ent t)) i (DirectSum.lof K I (fun j => (P j).M (ent t)) j (y t)) = 0
  rw [DirectSum.component.of, dite_eq_right e]

open Classical in
theorem decomp [Fintype ι] {m : ℕ} (z : (sumPM P).cech.X m) :
    ∃ F : Finset I, z = ∑ i ∈ F, inc P i m (pr P i m z) := by
  refine ⟨Finset.univ.biUnion fun t => DFinsupp.support (z t), sub_eq_zero.1 (cochain_ext P fun i => ?_)⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  by_cases hi : i ∈ Finset.univ.biUnion fun t => DFinsupp.support (z t)
  · rw [Finset.sum_eq_single_of_mem i hi (fun j _ e => pr_inc_ne P e _ _), pr_inc_self, sub_self]
  · have hz : pr P i m z = 0 := by
      funext t
      by_contra hne
      exact hi (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, DFinsupp.mem_support_iff.2 hne⟩)
    rw [hz, Finset.sum_eq_zero (fun j hj => pr_inc_ne P (ne_of_mem_of_not_mem hj hi) _ _), sub_zero]

theorem sum_ex [Fintype ι] (h : ∀ i, (P i).Ex) : (sumPM P).Ex := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · refine cochain_ext P fun i => ?_
    change pr P i 1 ((sumPM P).cech.d 0 ((sumPM P).aug x)) = 0
    rw [pr_d, pr_aug]
    exact (h i).1 _
  · rw [one_smul]
    refine DFinsupp.ext fun i => ?_
    have h0 : (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) = 0 := by
      rw [← pr_aug, hx, map_zero]
    have h1 := (h i).2.1 _ h0
    rw [one_smul] at h1
    exact h1
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d 0 (pr P i 0 y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i 1) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.1 _ (hc i)
    refine ⟨∑ i ∈ F, DirectSum.lof K I (fun j => (P j).M ∅) i (c i), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [one_smul, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [aug_lof, hc', one_smul]
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d (m + 1) (pr P i (m + 1) y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i (m + 2)) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.2 m _ (hc i)
    refine ⟨∑ i ∈ F, inc P i m (c i), ?_⟩
    rw [one_smul]
    change (sumPM P).cech.d m _ = y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [← inc_d]
    have h2 := hc' i
    rw [one_smul] at h2
    exact congrArg (inc P i (m + 1)) h2

theorem sum_desc {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I]
    (A : I → Sy.{1} K ι) (h : ∀ i, (A i).Desc) : (sumSy A).Desc :=
  fun n => sum_ex (fun i => (A i).term n) fun i => h i n

end GlobalTheory.CompanionTheory.KunGlue.SumDesc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetBlockMatrix
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoCell

open GroundTheory.Automorphic.Parabolic

theorem eq_iff_of_lt_iff {C A B : Type} [LinearOrder A] [LinearOrder B] (f : C → A) (g : C → B)
    (h : ∀ x y, f x < f y ↔ g x < g y) (x y : C) : f x = f y ↔ g x = g y := by
  constructor
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this

theorem card_cell_of_card_corner {n : ℕ} {β γ : Fin n → ℕ} {w w' : Equiv.Perm (Fin n)}
    (h : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card) (a b : ℕ) :
    (Finset.univ.filter fun j => γ j = b ∧ β (w j) = a).card =
      (Finset.univ.filter fun j => γ j = b ∧ β (w' j) = a).card := by
  classical
  have h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card := by
    intro a b
    cases b with
    | zero => simpa using h a 0
    | succ b =>
      have key : ∀ u : Equiv.Perm (Fin n),
          (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card =
            (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card +
              (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card := by
        intro u
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          omega
        · rw [Finset.disjoint_filter]
          intro j _ h1 h2
          omega
      have := h a (b + 1)
      rw [key w, key w', h a b] at this
      omega
  have key : ∀ u : Equiv.Perm (Fin n),
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card =
        (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card +
          (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card := by
    intro u
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      omega
  have := h1 a b
  rw [key w, key w', h1 (a + 1) b] at this
  omega

theorem permGL_mem_doubleCoset_iff_card : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  intro k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ e' γ hγ w w'
  classical
  have hβe := eq_iff_of_lt_iff β (blk e) hβ
  have hγe := eq_iff_of_lt_iff γ (blk e') hγ
  have reidx : ∀ (u : Equiv.Perm (Fin N)) (i : α) (j : β'),
      (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (u.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j).card := by
    intro u i j
    apply Finset.card_equiv u.symm
    intro x
    simp
  constructor
  · intro hmem i j
    have hc : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
        (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card := by
      intro a b
      rw [← cellRank_permGL (F := k), ← cellRank_permGL (F := k)]
      exact (cellRank_of_mem_doubleCoset hmem a b).symm
    rw [reidx, reidx]
    by_cases hi : ∃ x0, blk e x0 = i
    · by_cases hj : ∃ y0, blk e' y0 = j
      · obtain ⟨x0, rfl⟩ := hi
        obtain ⟨y0, rfl⟩ := hj
        have conv : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = blk e x0 ∧ blk e' y = blk e' y0) =
              Finset.univ.filter fun y => γ y = γ y0 ∧ β (u y) = β x0 := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβe, hγe]
          tauto
        rw [conv, conv]
        exact card_cell_of_card_corner hc _ _
      · have hz : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => hj ⟨y, h.2⟩
        rw [hz, hz]
    · have hz : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hi ⟨u y, h.1⟩
      rw [hz, hz]
  · intro h
    have hcard : ∀ c : α × β', Fintype.card {y : Fin N // (blk e (w y), blk e' y) = c} =
        Fintype.card {y : Fin N // (blk e (w' y), blk e' y) = c} := by
      intro c
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have conv : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => (blk e (u y), blk e' y) = c) =
            Finset.univ.filter fun y => blk e (u y) = c.1 ∧ blk e' y = c.2 := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      rw [conv, conv, ← reidx, ← reidx]
      exact h c.1 c.2
    let v : Fin N ≃ Fin N := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)
    have hv : ∀ j, (blk e (w' (v j)), blk e' (v j)) = (blk e (w j), blk e' j) := fun j =>
      Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j
    have hvβ : ∀ j, β (w' (v j)) = β (w j) := fun j => (hβe _ _).2 (Prod.ext_iff.1 (hv j)).1
    have hvγ : ∀ j, γ (v j) = γ j := fun j => (hγe _ _).2 (Prod.ext_iff.1 (hv j)).2
    let u : Equiv.Perm (Fin N) := w' * v * w⁻¹
    have hu : ∀ x, β (u x) = β x := by
      intro x
      simp only [u, Equiv.Perm.mul_apply]
      rw [hvβ]
      simp
    have hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin N)) x) = γ x := by
      intro x
      have := hvγ ((v⁻¹ : Equiv.Perm (Fin N)) x)
      have h' : v ((v⁻¹ : Equiv.Perm (Fin N)) x) = x := Equiv.apply_symm_apply v x
      rw [h'] at this
      exact this.symm
    refine DoubleCoset.mem_doubleCoset.2 ⟨permGL k u, permGL_mem_blockUpper hu, permGL k v⁻¹,
      permGL_mem_blockUpper hv', ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [u]
    group

end GlobalTheory.CompanionTheory.GeoCell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCoboundaryOfPairsCocycle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem cube_res_injective_of_eq {ι : Type} {A : Type} [CommRing A] (C : Cube.{0} ι A)
    {s t : Finset ι} (e : s = t) (h : s ⊆ t) : Function.Injective (Cube.res C h) := by
  subst e
  intro x y hxy
  rwa [GlobalTheory.Cube.res_self, GlobalTheory.Cube.res_self] at hxy

theorem cube_pairs_diag {ι : Type} [LinearOrder ι] {A : Type} [CommRing A] (C : Cube.{0} ι A)
    (c : ∀ i j : ι, C.obj {i, j})
    (hc : ∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) +
      Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k))
    (i : ι) : c i i = 0 := by
  have hx := hc i i i
  rw [add_eq_left] at hx
  apply GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_res_injective_of_eq C (s := {i, i}) (t := {i, i, i}) (by ext; simp)
    (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_triple_ij i i i)
  rw [map_zero]
  exact hx

theorem exists_coboundary_of_pairs_cocycle : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (C : Cube.{0} ι A), Function.Exact (Cube.d C 1) (Cube.d C 2) → ∀ c : ∀ i j : ι, C.obj {i, j}, (∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) + Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, C.obj {i}, ∀ i j, c i j = Cube.res C (sub_pair_left i j) (b i) - Cube.res C (sub_pair_right i j) (b j) := by
  intro ι _ A _ C hex c hc
  have hne : ∀ s : Finset ι, s.card = 2 → s.Nonempty := fun s hs => Finset.card_pos.1 (by omega)
  have hmm : ∀ (s : Finset ι) (hs : s.card = 2), ({s.min' (hne s hs), s.max' (hne s hs)} : Finset ι) ⊆ s :=
    fun s hs => Finset.insert_subset (Finset.min'_mem _ _)
      (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _))
  have htr : ∀ {a b a' b' : ι} (ha : a = a') (hb : b = b') (h : ({a, b} : Finset ι) ⊆ {a', b'}),
      GlobalTheory.Cube.res C h (c a b) = c a' b' := by
    intro a b a' b' ha hb h
    subst ha hb
    exact GlobalTheory.Cube.res_self C h _
  let y : GlobalTheory.Cube.Term C 2 := fun s =>
    -GlobalTheory.Cube.res C (hmm s.1 s.2) (c (s.1.min' (hne s.1 s.2)) (s.1.max' (hne s.1 s.2)))
  have hy : ∀ {i j : ι} (hij : i < j) (hs : ({i, j} : Finset ι).card = 2), y ⟨{i, j}, hs⟩ = -c i j := by
    intro i j hij hs
    have hmin : ({i, j} : Finset ι).min' (hne _ hs) = i :=
      le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [hij.le]))
    have hmax : ({i, j} : Finset ι).max' (hne _ hs) = j :=
      le_antisymm (Finset.max'_le _ _ _ (by simp [hij.le])) (Finset.le_max' _ _ (by simp))
    exact congrArg Neg.neg (htr hmin hmax _)
  have hy0 : GlobalTheory.Cube.d C 2 y = 0 := by
    funext ⟨t, ht⟩
    show _ = 0
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := GlobalTheory.AbLaw.CechOne.exists_triple (t := t) ht
    rw [GlobalTheory.AbLaw.CechOne.d_two_apply_triple C y hij hjk ht, hy hij, hy hjk, hy (hij.trans hjk)]
    simp only [map_neg]
    rw [← hc i j k]
    abel
  obtain ⟨x, hx⟩ := (hex y).1 hy0
  have hlt : ∀ i j, i < j → c i j =
      GlobalTheory.Cube.res C (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_pair_left i j) (x ⟨{i}, Finset.card_singleton i⟩) -
        GlobalTheory.Cube.res C (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_pair_right i j) (x ⟨{j}, Finset.card_singleton j⟩) := by
    intro i j hij
    have h1 := GlobalTheory.Cube.d_one_apply_pair C x hij
    rw [hx, hy hij] at h1
    rw [← neg_sub, ← h1, neg_neg]
  refine ⟨fun i => x ⟨{i}, Finset.card_singleton i⟩, fun i j => ?_⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hlt i j hij
  · rw [GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_pairs_diag C c hc i, sub_self]
  · apply GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_res_injective_of_eq C (s := {i, j}) (t := {i, j, i})
      (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_triple_ij i j i)
    have h := hc i j i
    rw [GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_pairs_diag C c hc i, map_zero] at h
    rw [eq_neg_of_add_eq_zero_left h, hlt j i hji]
    simp only [map_sub, neg_sub, GlobalTheory.Cube.res_res]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHomLocPiecesCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_homLoc_pieces_compatible : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module (MvPolynomial ι A) M] [IsScalarTower A (MvPolynomial ι A) M] (ℳ : ℤ → Submodule A M) [PolyGradedSMul ι ℳ] [DirectSum.Decomposition ℳ] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S') (ev : ∀ I : Finset ι, I.Nonempty → M →ₗ[MvPolynomial ι A] P I), (∀ I hI, IsGradedMap ℳ (𝒢 I) (ev I hI)) → (∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) m, res I J h (ev I hI m) = ev J hJ m) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ I (hI : I.Nonempty) (m : M), ev I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0) → (∀ I (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : M), ev I hI m = xProd A I ^ l • f) → ∀ t : ℤ, ∃ φ : ∀ I : Finset ι, I.Nonempty → (homLoc ℳ I t →ₗ[A] 𝒢 I t), (∀ I hI, Function.Bijective (φ I hI)) ∧ ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : homLoc ℳ I t), (φ J hJ (homLocRes ℳ h t z) : P J) = res I J h (φ I hI z : P I) := by
  intro ι _ A _ M _ _ _ _ ℳ _ _ P _ _ _ _ 𝒢 _ _ res ev hgr hres hX hker hcok t
  have key : ∀ (I : Finset ι) (hI : I.Nonempty), ∃ φ : homLoc ℳ I t →ₗ[A] 𝒢 I t,
      Function.Bijective φ ∧ ∀ (z : homLoc ℳ I t) (k : ℕ) (m : M),
        awayFrac M (xProd A I) k m = z → xProd A I ^ k • (φ z : P I) = ev I hI m := by
    intro I hI
    exact exists_homLoc_bijective_of (hgr I hI) I
      (xProd_smul_bijective_of I fun i hi => hX i I hi)
      (fun _ y _ hy => hker I hI y hy) (fun _ a _ => hcok I hI a) t
  choose φ hφbij hφ using key
  refine ⟨φ, hφbij, ?_⟩
  intro I J hI hJ h z
  have hb : Function.Bijective fun x : P J => xProd A J • x :=
    xProd_smul_bijective_of J fun i hi => hX i J hi
  have hinj : ∀ (n : ℕ) (x y : P J), xProd A J ^ n • x = xProd A J ^ n • y → x = y := by
    intro n
    induction n with
    | zero => intro x y hxy; simpa using hxy
    | succ n ih =>
      intro x y hxy
      apply ih
      apply hb.1
      show xProd A J • (xProd A J ^ n • x) = xProd A J • (xProd A J ^ n • y)
      rw [← mul_smul, ← mul_smul, ← pow_succ']
      exact hxy
  obtain ⟨k, m, hkm⟩ := exists_awayFrac (z : LocalizedModule.Away (xProd A I) M)
  have hc : xProd A J = (∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) * xProd A I :=
    (Finset.prod_sdiff h).symm
  have hz : (homLocRes ℳ h t z : LocalizedModule.Away (xProd A J) M) =
      awayFrac M (xProd A J) k ((∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) ^ k • m) := by
    rw [coe_homLocRes, ← hkm]
    exact locRes_awayFrac MvPolynomial.X h (Finset.prod_sdiff h).symm k m
  have h1 := hφ I hI z k m hkm
  have h2 := hφ J hJ (homLocRes ℳ h t z) k _ hz.symm
  apply hinj k
  rw [h2, map_smul, ← hres I J hI hJ h m, ← h1, map_smul, ← mul_smul, ← mul_pow, hc]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuReductionCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_mu_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j), B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) := by
  first | exact @GlobalTheory.CompanionTheory.CrysMid.mu_redHc | exact GlobalTheory.CompanionTheory.CrysMid.mu_redHc | (intros; apply GlobalTheory.CompanionTheory.CrysMid.mu_redHc <;> assumption)
end

