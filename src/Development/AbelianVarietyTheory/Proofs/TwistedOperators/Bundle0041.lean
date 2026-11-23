module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmodulePiTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootExSource

theorem det_eq_one_of_unip {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (b : ι → ℕ)
    (M : Matrix ι ι k) (h : ∀ r s, b s ≤ b r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hT : M.BlockTriangular b := fun r s hrs => by
    rw [h r s hrs.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hrs
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext r s
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, h _ _ (by rw [r.2, s.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, det_one]

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}

theorem mul_apply_of_inN {m : Type} {g : GL (n' ⊕ Fin c) k} (hg : InN p g)
    (x : Matrix m (n' ⊕ Fin c) k) (r : m) (s : n' ⊕ Fin c) :
    (x * g.val) r s = x r s + ∑ s', if lev p s' < lev p s then x r s' * g.val s' s else 0 := by
  have : x r s = (x * (1 : Matrix (n' ⊕ Fin c) (n' ⊕ Fin c) k)) r s := by rw [Matrix.mul_one]
  rw [this, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne, mul_zero, zero_add]
    rintro rfl
    exact lt_irrefl _ h
  · rw [hg s' s (not_lt.1 h), add_zero]

theorem affPt_nonfree (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, h]

theorem affPt_mul_nonfree {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : (affPt p x₀ e * g.val) r s = basePt c x₀ r s := by
  rw [mul_apply_of_inN hg, affPt_nonfree _ _ _ _ h, Finset.sum_eq_zero, add_zero]
  intro s' _
  split_ifs with h'
  · have : ¬ Free p (r, s') ∧ basePt c x₀ r s' = 0 := by
      rcases r with r | r <;> rcases s with s | s <;> rcases s' with s' | s' <;>
        simp [Free, lev, basePt] at h h' ⊢ <;> omega
    rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
  · rfl

theorem simpleSum_succ (g : GL (n' ⊕ Fin (c + 1)) k) :
    simpleSum g = ∑ l : Fin c, g.val (Sum.inr l.castSucc) (Sum.inr l.succ) := by
  unfold simpleSum
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (s := Finset.univ) (f := fun j : Fin (c + 1) =>
    if j.val = (Fin.last c).val + 1 then g.val (Sum.inr (Fin.last c)) (Sum.inr j) else 0), add_zero]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l.succ]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext (by simpa using h))
    · simp
  · intro j _
    rw [if_neg]
    have := j.2
    simp only [Fin.val_last]
    omega

theorem ch_affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (affPt p x₀ e * g.val) = ch (affPt p x₀ e) + simpleSum g := by
  rw [simpleSum_succ, ch, ch, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_apply_of_inN hg, Finset.sum_eq_single (Sum.inr l.castSucc)]
  · rw [if_pos (by simp [lev]), affPt_nonfree _ _ _ (Sum.inr l.castSucc) (by simp [Free])]
    simp [basePt]
  · intro s' _ hs
    split_ifs with h'
    · have : ¬ Free p ((Sum.inr l : n ⊕ Fin c), s') ∧ basePt c x₀ (Sum.inr l) s' = 0 := by
        rcases s' with s' | s' <;> simp [Free, lev, basePt, Fin.ext_iff] at hs h' ⊢ <;> omega
      rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
    · rfl
  · simp

def linPart (n : Type) [DecidableEq n] (p : ℕ) (g : GL (n' ⊕ Fin (c + 1)) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if b.1.1 = a.1.1 then g.val b.1.2 a.1.2 else 0

open Classical in
theorem det_linPart {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) : (linPart n p g).det = 1 := by
  rw [← det_transpose]
  refine det_eq_one_of_unip (fun a => lev p a.1.2) _ fun a b hab => ?_
  rcases a with ⟨⟨r, s⟩, ha⟩
  rcases b with ⟨⟨r', s'⟩, hb⟩
  simp only [linPart, transpose_apply, of_apply]
  rw [hg _ _ hab]
  by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [Matrix.one_apply, h1, h2]

open Classical in
theorem affPt_mul {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x₀ e * g.val = affPt p x₀ ((linPart n p g).mulVec e +
      fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases h : Free p (r, s)
  · have key : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
        ∑ s', (if h : Free p (r, s') then e ⟨(r, s'), h⟩ else 0) * g.val s' s := by
      have h1 : ((linPart n p g).mulVec e) ⟨(r, s), h⟩ =
          ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), (if b.1 = r then g.val b.2 s else 0) *
            (if h : Free p b then e ⟨b, h⟩ else 0) := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free p b)]
        rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ Free p b} => _)
          (fun b _ => by rw [dite_eq_right b.2, mul_zero]), add_zero]
        simp only [Matrix.mulVec, dotProduct, linPart, of_apply]
        refine Finset.sum_congr rfl fun b _ => by rw [dite_eq_left b.2]
      rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single r]
      · simp [mul_comm]
      · intro r' _ hr
        simp [hr]
      · simp
    unfold affPt
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.add_apply, of_apply, dite_eq_left h, Pi.add_apply, key]
    simp only [Matrix.mul_apply, Matrix.sub_apply, of_apply]
    ring
  · rw [affPt_mul_nonfree hg _ _ _ _ h, affPt_nonfree _ _ _ _ h]

private theorem secondCountable_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact secondCountable_of_proper

theorem opE_om_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n' (c + 1) p, opE ψ ν p (om μ g 1 Φ) = (ψ (simpleSum g) : ℂ) • opE ψ ν p Φ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hgN
  classical
  have := secondCountable_local k
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n' (c + 1) p
  have hg : InN p g := (h1 g).1 hgN
  have hdet := h3 g hgN
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : om μ g 1 Φ = fun x => Φ (x * g.val) := by
    funext x
    simp [om, hdet, hn1]
  funext x₀
  rw [hom, Pi.smul_apply, smul_eq_mul]
  unfold opE
  set v : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => (basePt c x₀ * g.val - basePt c x₀) a.1.1 a.1.2 with hv
  set F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ :=
    fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) with hF
  let G : GL {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart n p g) (by rw [det_linPart hg]; exact one_ne_zero)
  have hGval : G.val = linPart n p g := rfl
  have hGdet : Matrix.GeneralLinearGroup.det G = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hGval, det_linPart hg]; rfl
  have hcov := (GlobalTheory.SplitWeil.linear_change_of_variables k {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} n ν).1 G
    (fun e => F (e + v))
  rw [hGdet, hn1, inv_one, one_smul, hGval] at hcov
  have hint : ∀ e, Φ (affPt p x₀ e * g.val) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (simpleSum g) : ℂ) * F ((linPart n p g).mulVec e + v) := by
    intro e
    simp only [hF]
    rw [hv, ← affPt_mul hg, ch_affPt_mul hg, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  simp only [hint]
  rw [integral_const_mul, hcov]
  congr 1
  exact integral_add_right_eq_self F v

end GlobalTheory.RootExSource
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabiliserFiniteCosetsMod
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem stabiliser_finite_cosets_mod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (M : Submodule 𝒪[k] (ι → k)) (S : Finset (ι → k)) (hM : M.FG) (hS : IsReps ϖ M S) :
    ∃ T : Finset (GL ι k), (∀ t ∈ T, act t M = M) ∧ ∀ t : GL ι k, act t M = M →
      ∃ t₀ ∈ T, ∃ j : GL ι k, act j M = M ∧ MapsInto (j.val - 1) M (ϖ • M) ∧ t = t₀ * j := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hmem : ∀ t : GL ι k, act t M = M → ∀ x ∈ M, t.val *ᵥ x ∈ M := fun t ht x hx => by
    have h : t.val *ᵥ x ∈ act t M := mem_act.2 ⟨x, hx, rfl⟩
    rwa [ht] at h
  have hsM : ∀ x : s, x.1 ∈ M := fun x => hs ▸ Submodule.subset_span x.2
  have hex : ∀ (t : {t : GL ι k // act t M = M}) (x : s), ∃ r : S, t.1.val *ᵥ x.1 - r.1 ∈ ϖ • M := by
    intro t x
    obtain ⟨r, hr, -⟩ := hS.2 _ (hmem t.1 t.2 x.1 (hsM x))
    exact ⟨⟨r, hr.1⟩, hr.2⟩
  choose f hf using hex
  have hsec : ∀ y : Set.range f, ∃ t, f t = y.1 := fun y => y.2
  choose g hg using hsec
  have : Fintype (Set.range f) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun y => (g y).1, ?_, fun t ht => ?_⟩
  · intro t ht
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
    exact (g y).2
  · set t₀ := g ⟨f ⟨t, ht⟩, ⟨_, rfl⟩⟩ with ht₀
    have hft : f t₀ = f ⟨t, ht⟩ := hg _
    have hinv : act (t₀.1)⁻¹ M = M := by
      have h := act_mul (t₀.1)⁻¹ t₀.1 M
      rw [inv_mul_cancel, act_one, t₀.2] at h
      exact h.symm
    refine ⟨t₀.1, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (t₀.1)⁻¹ * t, ?_, ?_, ?_⟩
    · rw [act_mul, ht, hinv]
    · intro v hv
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        have h1 := hf ⟨t, ht⟩ ⟨x, hx⟩
        have h2 := hf t₀ ⟨x, hx⟩
        rw [hft] at h2
        have h3 := sub_mem h1 h2
        rw [sub_sub_sub_cancel_right] at h3
        obtain ⟨w, hw, hw'⟩ := mem_smul_iff.1 h3
        refine mem_smul_iff.2 ⟨_, hmem _ hinv w hw, ?_⟩
        rw [← Matrix.mulVec_smul, hw', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Units.inv_mul, Units.val_mul]
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ a hx
    · rw [mul_inv_cancel_left]

end GlobalTheory.RootEx.UnfoldShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem tensor_eq_top_or_le_ker_map : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀]
    {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i),
    Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) →
    Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) →
    (∀ i, ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel i ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → (∀ g ∈ Op i, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) →
    (∀ i, Rel i ≤ LinearMap.ker (p i)) → (∀ i, ∀ g ∈ Op i, ∀ x ∈ LinearMap.ker (p i), g x ∈ LinearMap.ker (p i)) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) →
      (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) →
      N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  intro ι _ _ M₀ P₀ _ _ _ _ M P _ _ _ _ Op₀ Op Rel₀ Rel p₀ p hr₀ hr hL₀ hloc₀ hRel₀ hK₀ hL hloc hRel hK
    N hN₀ hNi hS₀ hSi
  classical
  have hS : Stab (tensOps Op₀ (piOps Op)) N := by
    rintro f (⟨g, hg, rfl⟩ | ⟨h, ⟨i, g, hg, rfl⟩, rfl⟩) t ht
    · exact hS₀ g hg t ht
    · exact hSi i g hg t ht
  by_cases h0 : LinearMap.ker p₀ = ⊤
  · right
    intro t _
    have : p₀ = 0 := LinearMap.ker_eq_top.mp h0
    rw [LinearMap.mem_ker, this, TensorProduct.map_zero_left, LinearMap.zero_apply]
  by_cases hi : ∃ i, LinearMap.ker (p i) = ⊤
  · right
    obtain ⟨i, hi⟩ := hi
    have hpi : p i = 0 := LinearMap.ker_eq_top.mp hi
    have hmap : PiTensorProduct.map p = 0 := by
      ext y
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.zero_apply]
      exact MultilinearMap.map_coord_zero _ i (by simp [hpi])
    intro t _
    rw [LinearMap.mem_ker, hmap, TensorProduct.map_zero_right, LinearMap.zero_apply]
  push_neg at hi
  by_cases hN : N = ⊤
  · exact Or.inl hN
  have hSimple₀ : SimpleOver Op₀ (LinearMap.ker p₀) := fun U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc₀ U (hRel₀.trans hKU) hU hUt) hKU)
  have hSimple : ∀ i, SimpleOver (Op i) (LinearMap.ker (p i)) := fun i U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc i U ((hRel i).trans hKU) hU hUt) hKU)
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.exists_finset_generating_operator_stable_bounded Op₀ Rel₀ hL₀
  choose F hF using fun i => GlobalTheory.T.exists_finset_generating_operator_stable_bounded (Op i) (Rel i) (hL i)
  let G : Finset (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :=
    (F₀ ×ˢ Fintype.piFinset F).image (fun q => q.1 ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ q.2)
  have hgen : ∀ U, N ≤ U → Stab (tensOps Op₀ (piOps Op)) U → (↑G : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) ⊆ (U : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) → U = ⊤ := by
    intro U hNU hU hGU
    refine _root_.GlobalTheory.TensHead.eq_top_of_pure_generators Op₀ Op Rel₀ Rel F₀ F hF₀ hF U (fun x hx y => hNU (hN₀ x hx y))
      (fun i x hx x₀ y => hNU (hNi i x hx x₀ y)) hU ?_
    intro x₀ hx₀ y hy
    apply hGU
    simp only [G, Finset.coe_image]
    exact ⟨(x₀, y), by simp [hx₀, Fintype.mem_piFinset, hy], rfl⟩
  obtain ⟨N', hNN', hS', hN'top, hmax⟩ := GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating _ N G hgen N le_rfl hS hN
  have h0' := _root_.GlobalTheory.TensHead.tens_maxStab_contains_left_ker Op₀ (piOps Op) Rel₀ (LinearMap.ker p₀) hL₀ hloc₀ h0 hK₀ N'
    (fun x hx y => hNN' (hN₀ x hx y)) hS' hmax
  have hi' : ∀ i, ∀ x ∈ LinearMap.ker (p i), ∀ (x₀ : M₀) (y : ∀ j, M j),
      x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := fun i =>
    _root_.GlobalTheory.TensHead.position_mem_of_maximal_stable Op₀ Op i (Rel i) (LinearMap.ker (p i)) (hL i) (hloc i) (hi i) (hK i) N'
      (fun x hx x₀ y => hNN' (hNi i x hx x₀ y)) hS' hmax
  have hKT : tensKer (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) ≤ N' := by
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · exact h0' x hxy y
    · refine Submodule.span_induction (p := fun y _ => x ⊗ₜ[ℂ] y ∈ N') ?_ ?_ ?_ ?_ hxy
      · rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
        have := hi' i (z i) hzi x z
        rwa [Function.update_eq_self] at this
      · simp
      · intro a b _ _ ha hb
        rw [TensorProduct.tmul_add]
        exact N'.add_mem ha hb
      · intro c a _ ha
        rw [TensorProduct.tmul_smul]
        exact N'.smul_mem c ha
  have hPi := _root_.GlobalTheory.PiSimple.simpleOver_piKer Op (fun i => LinearMap.ker (p i)) hr hK hSimple
  have hT := _root_.GlobalTheory.TensHead.simpleOver_tensKer Op₀ (piOps Op) (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) hr₀ hK₀
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan Op _ hK) hSimple₀ hPi
  rcases hT N' hS' hKT with h | h
  · right
    rw [h] at hNN'
    refine hNN'.trans ?_
    have hle : piKer (fun i => LinearMap.ker (p i)) ≤ LinearMap.ker (PiTensorProduct.map p) := by
      rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, PiTensorProduct.map_tprod]
      exact MultilinearMap.map_coord_zero _ i (LinearMap.mem_ker.mp hzi)
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp hxy]
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp (hle hxy)]
  · exact absurd h hN'top

end GlobalTheory.TensHead
end

