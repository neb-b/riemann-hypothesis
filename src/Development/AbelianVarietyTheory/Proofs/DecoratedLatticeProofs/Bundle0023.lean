module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNEmbXInvMulMemKOne
section
open ValuativeRel Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SymChain.SymData
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem exists_N_embX_inv_mul_mem_KOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : GlobalTheory.SymChain.SymData k s κ), ∀ x ∈ S.P.J, ∃ (n : GL (Fin κ ⊕ Fin (s + 1)) k) (γ : GL (Fin κ) k),
        n ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) ∧ n ∈ S.P.J ∧ GlobalTheory.RootEx.embX (s + 1) γ ∈ S.P.J ∧
        (n * GlobalTheory.RootEx.embX (s + 1) γ)⁻¹ * x ∈ GlobalTheory.SplitWeil.KOne k (Fin κ ⊕ Fin (s + 1)) := by
  intro k _ _ _ _ s κ S x hx
  have mem_J_iff_pattern (g : GL (Fin κ ⊕ Fin (s + 1)) k) :
      g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
    rw [S.sym.1 g]
    constructor
    · rintro ⟨u, hu, γ, hγ, g₀, hg₀, hgb⟩
      refine ⟨⟨g₀, hg₀⟩, fun a b hab => ?_⟩
      rw [← hg₀, SymPattern.entry_lt_iff, hgb]
      exact SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
    · rintro ⟨⟨g₀, hg₀⟩, hpat⟩
      obtain ⟨u, hu, γ, hγ, he⟩ := SymPattern.exists_of_pat S.ρ
        (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀) (fun a b hab => by
          rw [← SymPattern.entry_lt_iff, hg₀]; exact hpat a b hab)
      exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, g₀, hg₀, he⟩
  obtain ⟨hxK, hpat⟩ := (mem_J_iff_pattern x).1 hx
  set M : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) k :=
    fun a b => if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b with hMdef
  have hMax : MaxM (M - x.val) := by
    intro a b
    show valuation k ((if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b) - x.val a b) < 1
    split_ifs with h
    · simp
    · rw [Valuation.map_sub_swap]; exact hpat a b h
  obtain ⟨u, hu, hMu⟩ := exists_mul_KOne hxK hMax
  have hMK : x * u ∈ KO k _ := mul_mem hxK (KOne_le_KO hu)
  have hpatM : ∀ a b, ¬ FreeTop S.ρ a b → (x * u).val a b = (1 : Matrix _ _ k) a b := by
    intro a b h; rw [hMu]; simp [hMdef, h]
  obtain ⟨n, hn, γ, hγ, e⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ (x * u) hpatM

  have hγv : ∀ i j, γ.val i j = (x * u).val (Sum.inl i) (Sum.inl j) := by
    intro i j
    rw [e, Units.val_mul, Radical.embX_val, GlobalTheory.SymPattern.mul_fromBlocks_inl]
    have e1 : ∀ t, n.val (Sum.inl i) (Sum.inl t) = (1 : Matrix (Fin κ) (Fin κ) k) i t := by
      intro t
      rw [hn _ _ (by simp [lev])]
      simp [Matrix.one_apply]
    simp only [e1]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  have hγint : ∀ i j, γ.val i j ∈ 𝒪[k] := fun i j => by
    rw [hγv]; exact intM_of_mem_KO hMK _ _

  have hγK : γ ∈ KO k (Fin κ) := by
    let A₀ : Matrix (Fin κ) (Fin κ) 𝒪[k] := fun i j => ⟨γ.val i j, hγint i j⟩
    have hmap : (algebraMap 𝒪[k] k).mapMatrix A₀ = γ.val := by ext i j; rfl
    have hdet1 : γ.val.det = 1 := Radical.Uni.det (b := Fin.val) hγ
    have hdet : A₀.det = 1 := by
      apply Subtype.ext
      have := RingHom.map_det (algebraMap 𝒪[k] k) A₀
      rw [hmap, hdet1] at this
      simpa using this
    refine ⟨Matrix.nonsingInvUnit A₀ (by rw [hdet]; exact isUnit_one), ?_⟩
    ext i j
    rfl
  have hembK : embX (s + 1) γ ∈ KO k _ := by
    refine mem_KO.2 ⟨?_, ?_⟩
    · rw [Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO hγK, intM_zero, intM_zero, intM_one⟩
    · rw [← map_inv, Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO (inv_mem hγK), intM_zero, intM_zero, intM_one⟩
  have hnK : n ∈ KO k _ := by
    have : n = (x * u) * (embX (s + 1) γ)⁻¹ := by rw [e]; group
    rw [this]; exact mul_mem hMK (inv_mem hembK)
  refine ⟨n, γ, (Radical.mem_N_iff n).2 hn, ?_, ?_, ?_⟩
  · refine (mem_J_iff_pattern n).2 ⟨hnK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ n hn 1 (fun r s _ => rfl) a b hab
    rw [map_one, mul_one] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · refine (mem_J_iff_pattern _).2 ⟨hembK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ 1 (fun r s _ => rfl) γ hγ a b hab
    rw [one_mul] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · rw [← e, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem hu

end GlobalTheory.SymChain.SymData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRootExchangeParabolicMulPrincipalCongruenc
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ResidueLift

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def blockIx (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p) (fun i => 2 * (i.val + 1) + 1)

theorem of_blockIx_lt {a b : n ⊕ Fin c} (h : blockIx p b < blockIx p a) :
    lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) ∧ a ≠ b := by
  rcases a with a | a <;> rcases b with b | b <;> simp only [blockIx, Sum.elim_inl, Sum.elim_inr] at h
  · omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, by simp⟩; simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega
  · refine ⟨?_, by simp, fun e => ?_⟩
    · simp only [lev, Sum.elim_inr]; omega
    · cases e; omega

theorem mem_R_of_pattern (r : GL (n ⊕ Fin c) k)
    (hr : ∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
      r.val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b) :
    r ∈ R k n c p := by
  have hbt : r.val.BlockTriangular (blockIx p) := fun a b h => by
    obtain ⟨h1, h2, h3⟩ := of_blockIx_lt h
    rw [hr a b h1 h2, one_apply_ne h3]
  have hbt' : (r⁻¹).val.BlockTriangular (blockIx p) := by
    rw [Matrix.coe_units_inv]; exact blockTriangular_inv_of_blockTriangular hbt
  have hz : ∀ (x : n) (j : Fin c), j.val + 1 ≤ p → r.val (.inl x) (.inr j) = 0 := fun x j hj => by
    rw [hr _ _ (by simpa [lev] using hj) (by simp)]; simp
  have hz' : ∀ (x : n) (j : Fin c), p ≤ j.val + 1 → (r⁻¹).val (.inr j) (.inl x) = 0 := fun x j hj =>
    hbt' (by simp only [blockIx, Sum.elim_inl, Sum.elim_inr]; omega)
  have e1 : r.val.toBlocks₁₁ * (r⁻¹).val.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.toBlocks₁₁ (congrArg Units.val (mul_inv_cancel r))
    rw [Units.val_mul, mul_toBlocks₁₁, Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁] at this
    rw [← this, left_eq_add]
    ext x x'
    simp only [Matrix.mul_apply, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_total (j.val + 1) p with hj | hj
    · rw [hz x j hj, zero_mul]
    · rw [hz' x' j hj, mul_zero]
  let γ : GL n k := ⟨r.val.toBlocks₁₁, (r⁻¹).val.toBlocks₁₁, e1, mul_eq_one_comm.1 e1⟩
  have e2 : (γ⁻¹).val * r.val.toBlocks₁₁ = 1 := Units.inv_mul γ
  have hm : InN p ((embX c γ)⁻¹ * r) := by
    intro a b hab
    rw [← map_inv, Units.val_mul, show (embX c γ⁻¹).val = fromBlocks (γ⁻¹).val 0 0 1 from rfl]
    rcases a with x | i
    · rcases b with x' | j
      · have := congrFun (congrFun e2 x) x'
        simpa [Matrix.mul_apply, Fintype.sum_sum_type, toBlocks₁₁, Matrix.one_apply] using this
      · have hj : j.val + 1 ≤ p := by simpa [lev] using hab
        simp [Matrix.mul_apply, Fintype.sum_sum_type, hz _ _ hj]
    · rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, zero_add]
      change ((1 : Matrix (Fin c) (Fin c) k) *ᵥ (fun j => r.val (.inr j) b)) i = _
      rw [Matrix.one_mulVec]
      exact hr (.inr i) b hab (by simp)
  have : r = embX c γ * ((embX c γ)⁻¹ * r) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨γ, rfl⟩) (Subgroup.mem_sup_right (Subgroup.subset_closure hm))

end GlobalTheory.SymChain.ResidueLift

namespace GlobalTheory.SymChain.ResidueLift

theorem exists_R_mul_KOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (h : GL (n ⊕ Fin c) k), (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KO k (n ⊕ Fin c) → (∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) → valuation k (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b - (1 : Matrix _ _ k) a b) < 1) → ∃ r ∈ R k n c p, ∃ u : GL (n ⊕ Fin c) k, (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * u * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KOne k (n ⊕ Fin c) ∧ h = r * u := by
  intro k _ _ _ _ ϖ n _ _ c p h hg hpat
  classical
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of fun a b =>
    if lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) then (1 : Matrix _ _ k) a b
    else ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b
  have hM : MaxM (M - ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val) := fun a b => by
    simp only [M, Matrix.sub_apply, Matrix.of_apply]
    split_ifs with hc
    · rw [← neg_sub, Valuation.map_neg]; exact hpat a b hc.1 hc.2
    · simp
  obtain ⟨u', hu', eu'⟩ := exists_mul_KOne hg hM
  refine ⟨(typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas *
      (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas) * u') *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_,
    (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_, ?_⟩
  · refine mem_R_of_pattern _ fun a b h1 h2 => ?_
    rw [Units.val_mul, Units.val_mul, eu', Model.typeFrame_val, Model.typeFrame_inv, mul_diagonal, diagonal_mul]
    simp only [M, Matrix.of_apply, if_pos (And.intro h1 h2)]
    by_cases hab : a = b
    · subst hab; simp [mul_inv_cancel₀ (Model.wt_ne_zero ϖ a)]
    · simp [one_apply_ne hab]
  · have e : (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ *
        (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹) * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas = u'⁻¹ := by group
    rw [e]; exact inv_mem hu'
  · group

end GlobalTheory.SymChain.ResidueLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnIndicatorPureAtSymmetricPosition
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat.PureColPf

section Plain
variable {k : Type} [Field k] {n n' ι ι' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem typeFrame_val' (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← fromBlocks_diagonal]; simp

theorem typeFrame_inv_val' (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_val', diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem coords_entry (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (u : n ⊕ Fin c) (v : n' ⊕ Fin c') :
    (((typeFrame ϖ o).bas⁻¹).val * x * (typeFrame ϖ o').bas.val) u v =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) u * x u v *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) v := by
  rw [typeFrame_inv_val', typeFrame_val', mul_diagonal, diagonal_mul]

theorem affPt_col (p : ℕ) (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : n) (q : Fin (c + 1)) (hq : q.val + 1 = p) : affPt p x₀ e (.inl a) (.inr q) = 0 := by
  have : ¬ Free p ((.inl a, .inr q) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) := by
    simp only [Free]; omega
  simp [affPt, basePt, this]

end Plain

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_one_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x
  simp [om, nabs]

end Loc

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem le_of_mul_pow_lt {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : ℕ) {y : k}
    (h : valuation k (y * (ϖ : k) ^ (r + 1)) < 1) : valuation k y ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k) := by
  have h1 := (hϖ _).1 h
  have h0 : ((ϖ : k) ^ (r + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have ey : y = (y * (ϖ : k) ^ (r + 1)) * ((ϖ : k) ^ (r + 1))⁻¹ := by field_simp
  have ec : (((ϖ ^ r)⁻¹ : kˣ) : k) = (ϖ : k) * ((ϖ : k) ^ (r + 1))⁻¹ := by
    simp [pow_succ]
  calc valuation k y = valuation k (y * (ϖ : k) ^ (r + 1)) * valuation k (((ϖ : k) ^ (r + 1))⁻¹) := by
        rw [← map_mul, ← ey]
    _ ≤ valuation k (ϖ : k) * valuation k (((ϖ : k) ^ (r + 1))⁻¹) := mul_le_mul_left h1 _
    _ = _ := by rw [← map_mul, ec]

theorem mul_pow_lt_of_le {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : ℕ) {y : k}
    (h : valuation k y ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k)) : valuation k (y * (ϖ : k) ^ (r + 1)) < 1 := by
  have h0 : ((ϖ : k) ^ (r + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have e : (((ϖ ^ r)⁻¹ : kˣ) : k) * (ϖ : k) ^ (r + 1) = ϖ := by
    simp [pow_succ]
  have h1 : valuation k (ϖ : k) < 1 := (hϖ _).2 le_rfl
  calc valuation k (y * (ϖ : k) ^ (r + 1)) = valuation k y * valuation k ((ϖ : k) ^ (r + 1)) := map_mul _ _ _
    _ ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k) * valuation k ((ϖ : k) ^ (r + 1)) := mul_le_mul_left h _
    _ = valuation k (ϖ : k) := by rw [← map_mul, e]
    _ < 1 := h1

end Main

section Chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem Phi_add_colAt (j c : ℕ) (H : j + 1 + c = s) (r : ℕ) (y : XIx (Fin κ) t (j + 1) → k)
    (hy : y ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹)
    (z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) :
    (S.T t).Phi j (c + 1) (by omega) (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y) =
      (S.T t).Phi j (c + 1) (by omega) z := by
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  rw [hΦ, hΦ]
  have e : ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o')
      (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y)).submatrix (ixSucc _ t j) id =
      ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') z).submatrix (ixSucc _ t j) id +
      ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') (colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y)).submatrix
        (ixSucc _ t j) id := by
    simp only [LatFrame.coords, Matrix.mul_add, Matrix.add_mul]
    rfl
  rw [e]
  refine TypeDatum.Phi_add _ (S.tame _) _ fun u v => ?_
  change valuation k ((((typeFrame S.ϖ o).bas⁻¹).val * colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y *
    (typeFrame S.ϖ o').bas.val) (o (ixSucc _ t j u)) (o' v)) < 1
  rw [coords_entry]
  generalize o (ixSucc _ t j u) = U
  generalize o' v = V
  rcases U with a | l <;> rcases V with b | q
  · simp [colAt]
  · by_cases hq : q.val = r
    · have := mul_pow_lt_of_le S.unif r (hy a)
      simpa [colAt, hq] using this
    · simp [colAt, hq]
  · simp [colAt]
  · simp [colAt]

end Chain

section Chain2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem mem_box_of_Phi_ne_zero (hpat : S.Pattern t) (j c : ℕ) (H : j + 1 + c = s) (r : ℕ) (hr : c + 1 = 2 * r)
    (z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hz : ∀ a, z (.inl a) (.inr ⟨r, by omega⟩) = 0) (y : XIx (Fin κ) t (j + 1) → k)
    (h : (S.T t).Phi j (c + 1) (by omega) (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y) ≠ 0) :
    y ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹ := by
  have hρ : r ≤ S.ρ := by have := S.odd; omega
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  rw [hΦ] at h
  obtain ⟨⟨g, hg, e⟩, hmax⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 h
  have hpg := ((hpat j g).1 hg).2
  set x := z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y with hx
  let q₀ : Fin (c + 1 + 1) := ⟨r, by omega⟩
  let b : Ix (Fin κ ⊕ Fin (s + 1)) t j := .inl (.inr ⟨r, by omega⟩)
  have hb : o' b = .inr q₀ := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (by omega) q₀
  intro a
  apply le_of_mul_pow_lt S.unif r
  have key : (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (o.symm (.inl a)) b = y a * (S.ϖ : k) ^ (r + 1) := by
    change (((typeFrame S.ϖ o).bas⁻¹).val * x * (typeFrame S.ϖ o').bas.val) (o (o.symm (.inl a))) (o' b) = _
    rw [Equiv.apply_symm_apply, hb, coords_entry]
    simp [hx, hz, q₀, colAt]
  rw [← key]
  obtain ⟨w, hw⟩ : ∃ w, ixSucc _ t j w = o.symm (.inl a) := ⟨_, Equiv.apply_symm_apply _ _⟩
  have hw' : o (ixSucc _ t j w) = .inl a := by rw [hw, Equiv.apply_symm_apply]
  rw [← hw]
  rcases w with i | u
  · have hgi : g.val i b = (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (ixSucc _ t j (.inl i)) b := by
      rw [e]; rfl
    have hnf : ¬ FreeIx S.ρ i b ∧ i ≠ b := by
      rcases i with (e' | l) | ⟨q, u⟩
      · refine ⟨?_, by simp [b]⟩
        simp only [FreeIx, FreeTop, b, Fin.mk_lt_mk, not_lt]
        exact hρ
      · have hl : c + 1 ≤ l.val := by
          by_contra hl
          push_neg at hl
          have h1 : o (.inl (.inr l)) = .inr ⟨l.val, hl⟩ :=
            standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) (c + 1) (by omega) (⟨l.val, hl⟩ : Fin (c + 1))
          have h2 : o (ixSucc _ t j (.inl (.inl (.inr l)))) = o (.inl (.inr l)) := rfl
          rw [h2, h1] at hw'
          exact Sum.inr_ne_inl hw'
        refine ⟨?_, ?_⟩
        · simp only [FreeIx, FreeTop, b, Fin.lt_def, not_lt]
          omega
        · intro he
          simp only [b, Sum.inl.injEq, Sum.inr.injEq] at he
          have := congrArg Fin.val he
          simp at this
          omega
      · exact ⟨by simp [FreeIx, b], by simp [b]⟩
    have := hpg i b hnf.1
    rw [Matrix.one_apply_ne hnf.2, sub_zero, hgi] at this
    exact this
  · exact hmax u b

end Chain2

theorem _root_.GlobalTheory.LocFlat.pureCol_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureCol S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hpat hex
  haveI := hν.1
  intro j c H r hr
  obtain ⟨C, hC, hCe⟩ := hex j (c + 1) (by omega) (r + 1) (by omega) (by omega) (by have := S.odd; omega)
  have hreg := (Chain.ofType_regular S.P S.μ S.tame (fun j c h => typeFrame S.ϖ (stdOrd (Fin κ) t j c h))
    (LatFrame.refl k _)).2.2 (j + 1) (c + 1) (by omega)
  have hvol := volNat_Cgrp_pos ν (J := ((S.T t).lev (j + 1) (c + 1) (by omega)).J) hreg.1 hreg.2.1
    ((S.T t).bas (j + 1) (c + 1) (by omega)) 1
  set V := volNat ν ((S.T t).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1)
    with hV
  refine ⟨C * V, mul_pos hC hvol, fun x => ?_⟩
  have hent : ∀ x₀, (S.T t).entry S.ψ ν j c H 1 1 x₀ =
      ((V⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 ((S.T t).Phi j (c + 1) (by omega)) x₀ := by
    intro x₀
    simp only [Chain.entry, xi, flat, om_one_one, hV]
  by_cases hy : (fun a => x a (Sum.inr ())) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹
  · rw [if_pos hy, mul_one, hent]
    have e : flCol S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x =
        opE S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x.toCols₁ := by
      unfold flCol
      congr 1
      funext z
      exact Phi_add_colAt S t j c H r _ hy z
    rw [e, hCe, Pi.smul_apply, smul_eq_mul]
    have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
    push_cast
    field_simp
  · rw [if_neg hy, mul_zero]
    unfold flCol opE
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun e => ?_)
    have h0 : (S.T t).Phi j (c + 1) (by omega) (affPt (r + 1) x.toCols₁ e +
        colAt (XIx (Fin κ) t j) (c + 1) (r + 1) fun a => x a (Sum.inr ())) = 0 := by
      by_contra hne
      exact hy (mem_box_of_Phi_ne_zero S t hpat j c H r hr _
        (fun a => affPt_col _ _ _ _ _ rfl) _ hne)
    simp only [h0, zero_mul, Pi.zero_apply]

end GlobalTheory.LocFlat.PureColPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslate
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat.ColTranslate
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat

theorem colE_neg_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (y : n → k) :
    ((colE c p (-y))⁻¹ : GL (n ⊕ Fin c) k).val = (colE c p y).val := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [colE, upU, -Matrix.coe_units_inv, Units.inv_mk, neg_ite]

theorem affPt_add_colAt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (y : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    affPt (q.val + 1) x₀ e + colAt n' c (q.val + 1) y = mat x₀ (ext0 (Free (q.val + 1)) e + gCol q y) := by
  classical
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [affPt_eq, mat, ext0, colAt, gCol, Free]
  · by_cases h : s = q.castSucc
    · subst h; simp [affPt_eq, mat, ext0, colAt, gCol, Free]
    · have h' : ¬ s.val = q.val := fun hh => h (Fin.ext (by simpa using hh))
      simp [affPt_eq, mat, ext0, colAt, gCol, h, h']
  · simp [affPt_eq, mat, ext0, colAt, gCol]
  · simp [affPt_eq, mat, ext0, colAt, gCol]

theorem ch_add_colAt {k : Type} [Field k] {n n' : Type} {c : ℕ} (p : ℕ) (y : n → k)
    (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]

end GlobalTheory.LocFlat.ColTranslate

namespace GlobalTheory.LocFlat
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat.ColTranslate

theorem flCol_eq_opE_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc Φ hΦ x
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp; omega⟩
  have hcont : Continuous Φ := hΦ.1.continuous
  have h1 := opE_colE hψ ν 1 q q (χ := fun _ => (1 : ℂ)) continuous_const hcont x.toCols₁
    (-fun r => x r (Sum.inr ()))
  simp only [om_colE, colE_neg_inv, one_mul, neg_neg] at h1
  refine Eq.trans ?_ h1.symm
  rw [flCol]
  unfold opE
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only
  rw [← affPt_add_colAt, big, ch_add_colAt, one_mul]

end GlobalTheory.LocFlat
end

