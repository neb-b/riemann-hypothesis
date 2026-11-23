module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableWeightedHeckeThetaKernelHalfSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeThetaKernelPoissonSummation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfRootInUnipotentRadical
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.MackeyRadical

theorem exists_elem {F : Type} [Field F] {r : ℕ} {i j : Fin r} (h : i ≠ j) (t : F) :
    ∃ g : GL (Fin r) F, ∀ k l, (g : Matrix (Fin r) (Fin r) F) k l =
      (1 : Matrix (Fin r) (Fin r) F) k l + if i = k ∧ j = l then t else 0 := by
  refine ⟨⟨Matrix.transvection i j t, Matrix.transvection i j (-t), ?_, ?_⟩, fun k l => ?_⟩
  · rw [Matrix.transvection_mul_transvection_same _ _ h, add_neg_cancel, Matrix.transvection_zero]
  · rw [Matrix.transvection_mul_transvection_same _ _ h, neg_add_cancel, Matrix.transvection_zero]
  · simp [Matrix.transvection, Matrix.single]

theorem eig_eq_bot_of_radical : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ψ ≠ 1 → ∀ a c : Fin r, cutEdge j a c → b (w a) < b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  intro F _ ψ r V _ _ b σ hσ j w x hx hψ a c hac hb
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext _ _ fun t => by simpa using h t)
  have hne : w a ≠ w c := fun h => by rw [h] at hb; exact lt_irrefl _ hb
  have hlt : a.val < c.val := by have := hac.1; omega
  obtain ⟨g, hg⟩ := exists_elem hne t
  have hgb : g ∈ blockTri (κ := F) b := by
    refine mem_blockTri.2 fun k l hkl => ?_
    have hkl' : k ≠ l := fun h => by rw [h] at hkl; exact lt_irrefl _ hkl
    rw [hg, Matrix.one_apply_ne hkl', if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hb hkl
  have h1 : σ ⟨g, hgb⟩ = 1 := by
    refine hσ.infl _ fun k l hkl => ?_
    show (g : Matrix (Fin r) (Fin r) F) k l = _
    rw [hg, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hb.ne hkl
  have hc : ∀ k l, ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l =
      (1 : Matrix (Fin r) (Fin r) F) k l + if a = k ∧ c = l then t else 0 := by
    intro k l
    rw [hx, hg]
    simp [Matrix.one_apply]
  have hu : x⁻¹ * g * x ∈ unip F r := by
    refine ⟨mem_blockTri.2 fun k l hkl => ?_, fun k => ?_⟩
    · have hkl' : k ≠ l := fun h => by rw [h] at hkl; exact lt_irrefl _ hkl
      rw [hc, Matrix.one_apply_ne hkl', if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hlt hkl
    · rw [hc, Matrix.one_apply_eq, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hlt
  have hs : edgeSum (cutEdge j) (x⁻¹ * g * x) = t := by
    unfold edgeSum
    have key : ∀ k l : Fin r, (if cutEdge j k l then ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l else 0) =
        if l = c then (if k = a then t else 0) else 0 := by
      intro k l
      by_cases h : cutEdge j k l
      · have hkl : k ≠ l := fun e => by have := h.1; rw [e] at this; omega
        rw [if_pos h, hc, Matrix.one_apply_ne hkl, zero_add]
        by_cases h1 : l = c <;> by_cases h2 : k = a <;> simp [h1, h2, @eq_comm _ a k, @eq_comm _ c l]
      · rw [if_neg h]
        by_cases h1 : l = c <;> by_cases h2 : k = a <;> simp [h1, h2]
        subst h1 h2
        exact absurd hac h
    simp only [key]
    simp
  refine eq_bot_iff.2 fun v hv => ?_
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker] at hv
  have := hv ⟨g, hgb⟩ hu
  simp only [h1, hs, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
  have h2 : (1 - ψ t) • v = 0 := by rw [sub_smul, one_smul]; exact this
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm ht
  · exact h

end GlobalTheory.FinGL.MackeyRadical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenSortingPermEqLeviWhittaker
section
noncomputable section

namespace GlobalTheory.FinGL.SortWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable {F : Type} [Field F] {r : ℕ}

def bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i k => if b i = b k then M i k else 0

theorem bd_apply (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) (i k : Fin r) :
    bd b M i k = if b i = b k then M i k else 0 := rfl

theorem bd_one (b : Fin r → ℕ) : bd b (1 : Matrix (Fin r) (Fin r) F) = 1 := by
  ext i k
  rw [bd_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply_ne]
    rintro rfl
    exact h rfl

theorem bd_bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : bd b (bd b M) = bd b M := by
  ext i k
  simp only [bd_apply]
  split_ifs <;> rfl

theorem bd_mul (b : Fin r → ℕ) {M N : Matrix (Fin r) (Fin r) F} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) :
    bd b (M * N) = bd b M * bd b N := by
  ext i k
  simp only [bd_apply, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (b l) (b i) with h1 | h1 | h1
    · rw [hM h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hN (show b k < b l by omega)]; simp
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases h1 : b i = b l
    · rw [if_neg (show ¬ b l = b k by omega), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem bd_tri (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : (bd b M).BlockTriangular b := by
  intro i k h
  rw [bd_apply, if_neg (by omega)]

def levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) : blockTri (κ := F) b :=
  ⟨⟨bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), bd b (((p⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F),
    by rw [← bd_mul b p.2 (p⁻¹).2, ← Units.val_mul]; simp [bd_one],
    by rw [← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]; simp [bd_one]⟩, bd_tri b _⟩

theorem levi_apply (b : Fin r → ℕ) (p : blockTri (κ := F) b) (i k : Fin r) :
    ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := rfl

theorem sigma_levi {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (p : blockTri (κ := F) b) :
    σ (levi b p) = σ p := by
  have h : σ (p⁻¹ * levi b p) = 1 := by
    refine hσ.infl _ fun i k hik => ?_
    have h1 : bd b ((((p⁻¹ * levi b p : blockTri (κ := F) b)) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [Subgroup.coe_mul, Units.val_mul, bd_mul b (p⁻¹).2 (levi b p).2]
      have : bd b ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
          bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := bd_bd b _
      rw [this, ← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]
      simp [bd_one]
    have h2 := congrFun (congrFun h1 i) k
    rwa [bd_apply, if_pos hik] at h2
  have : levi b p = p * (p⁻¹ * levi b p) := by group
  rw [this, map_mul, h, mul_one]

theorem edgeSum_levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) :
    edgeSum (blkEdge b) (levi b p : GL (Fin r) F) = edgeSum (blkEdge b) (p : GL (Fin r) F) := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [levi_apply, if_pos h.2]
  · rfl

section Perm

variable {b : Fin r → ℕ} {j : ℕ} {w : Equiv.Perm (Fin r)}

theorem lt_iff (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) {a c : Fin r} (h : b (w a) = b (w c)) :
    a < c ↔ w a < w c := by
  refine ⟨fun hac => h1 a c hac h, fun hw => ?_⟩
  rcases lt_trichotomy a c with h' | h' | h'
  · exact h'
  · subst h'; exact absurd hw (lt_irrefl _)
  · exact absurd (h1 c a h' h.symm) (not_lt.2 hw.le)

theorem edge_iff (hb : Monotone b) (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c)
    (h2 : ∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a))
    (h4 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) {a c : Fin r} (h : b (w a) = b (w c)) :
    blkEdge b (w a) (w c) ↔ cutEdge j a c := by
  constructor
  · rintro ⟨e1, -⟩
    have hac : a < c := (lt_iff h1 h).2 (by rw [Fin.lt_def]; omega)
    have hac' : a.val < c.val := hac
    have hc : c.val = a.val + 1 := by
      by_contra hne
      let e : Fin r := ⟨a.val + 1, by have := c.2; omega⟩
      have hae : a < e := by rw [Fin.lt_def]; simp [e]
      have hec : e < c := by rw [Fin.lt_def]; simp only [e]; omega
      have hbe := h2 a e c hae.le hec.le h
      have k1 : (w a).val < (w e).val := h1 a e hae hbe.symm
      have k2 : (w e).val < (w c).val := h1 e c hec (hbe.trans h)
      omega
    refine ⟨hc, fun hj => h4 a c (by omega) (by omega) h⟩
  · rintro ⟨e1, -⟩
    refine ⟨?_, h⟩
    have hac : a < c := by rw [Fin.lt_def]; omega
    have hw : (w a).val < (w c).val := h1 a c hac h
    by_contra hne
    let i : Fin r := ⟨(w a).val + 1, by have := (w c).2; omega⟩
    have hai : w a < i := by rw [Fin.lt_def]; simp [i]
    have hic : i < w c := by rw [Fin.lt_def]; simp only [i]; omega
    obtain ⟨e, he⟩ := w.surjective i
    have k1 : b (w a) ≤ b i := hb hai.le
    have k2 : b i ≤ b (w c) := hb hic.le
    rw [← he] at hai hic k1 k2
    have l1 : a.val < e.val := (lt_iff h1 (by omega)).2 hai
    have l2 : e.val < c.val := (lt_iff h1 (by omega)).2 hic
    omega

end Perm

theorem eig_conj_eq_leviWh : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → (∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) → (∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a)) → (∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a)) → (∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = eig σ {p | (p : GL (Fin r) F) ∈ unip F r} (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  intro F _ ψ r V _ _ b σ hσ j w x hx h1 h2 h3 h4
  have hsum : ∀ p : blockTri (κ := F) b, edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x) =
      edgeSum (blkEdge b) (p : GL (Fin r) F) := by
    intro p
    unfold edgeSum
    rw [← Equiv.sum_comp w (fun i => ∑ k, if blkEdge b i k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp w (fun k => if blkEdge b (w a) k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (w a) k else 0)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hx]
    by_cases h : b (w a) = b (w c)
    · simp only [edge_iff hσ.mono h1 h2 h4 h]
    · rw [if_neg (show ¬ blkEdge b (w a) (w c) from fun h' => h h'.2)]
      split_ifs with hc
      · exact p.2 (lt_of_le_of_ne (h3 a c hc) (Ne.symm h))
      · rfl
  ext v
  rw [mem_eig, mem_eig]
  constructor
  · intro H p hp
    have hp' : (p : GL (Fin r) F) ∈ unip F r := hp
    have hm : x⁻¹ * (levi b p : GL (Fin r) F) * x ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun a c hac => ?_, fun a => ?_⟩
      · rw [hx, levi_apply]
        split_ifs with h
        · exact unip_lower hp' (h1 c a hac h.symm)
        · rfl
      · rw [hx, levi_apply, if_pos rfl, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, hsum, edgeSum_levi] at this
    exact this
  · intro H p hp
    have hp' : x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r := hp
    have hm : (levi b p : GL (Fin r) F) ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun i k hik => ?_, fun i => ?_⟩
      · obtain ⟨a, rfl⟩ := w.surjective i
        obtain ⟨c, rfl⟩ := w.surjective k
        rw [levi_apply]
        split_ifs with h
        · rw [← hx]
          exact unip_lower hp' ((lt_iff h1 h.symm).2 hik)
        · rfl
      · obtain ⟨a, rfl⟩ := w.surjective i
        rw [levi_apply, if_pos rfl, ← hx, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, edgeSum_levi] at this
    rw [hsum]
    exact this

end GlobalTheory.FinGL.SortWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStrips
section
noncomputable section
open NumberField MeasureTheory

namespace GlobalTheory.HeckeStrip

theorem completed_pSeries_entire_bounded : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  intro K _ _ _ I _ φ hφ n hn M F hM hper hinv
  haveI : Nonempty I := ⟨hn.choose⟩
  obtain ⟨p, hpm, hp0, hpsum, R, hpR⟩ := _root_.GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates K I φ hφ
  obtain ⟨⟨C, hC⟩, hsumm, hge⟩ := _root_.GlobalTheory.HeckeLat.periodic_bound_summable_norm K I φ hφ M F hM hper
  obtain ⟨a, κ, hasumm, ⟨δ, hδ, hδa⟩, hfe⟩ := _root_.GlobalTheory.HeckePoisson.theta_poisson K I φ hφ n M F hM hper
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hpsum y) 1 (fun u _ => hp0 _)
    have h0 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by
      funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h0] using h
  have hpB : ∀ y, |p y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [hp0 y], hp1 y⟩
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hℓ : Measurable (fun y : I → ℝ => ∑ i, y i) := by fun_prop
  have hS0 : ∀ᵐ y ∂(volume.restrict S), 0 ≤ ∑ i, y i := ae_restrict_of_forall_mem hSm fun y hy => hy
  obtain ⟨D1m, D1i⟩ := _root_.GlobalTheory.HeckeTheta.Decay.integrable_weight_theta I (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n p 1 R hn hsumm
    ⟨1, one_pos, fun α _ h => hge α h⟩ hpm hpB hpR
  obtain ⟨D2m, D2i⟩ := _root_.GlobalTheory.HeckeTheta.Decay.integrable_weight_theta I (fun v : I → ℂ => v) a n (fun y => p (-y)) 1 R hn hasumm ⟨δ, hδ, hδa⟩
    (hpm.comp measurable_neg) (fun y => hpB _) (fun y hy i j => by
      have := hpR (-y) hy j i
      simp only [Pi.neg_apply] at this
      linarith)
  have A1 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D1m.restrict hS0 D1i
  have A2 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D2m.restrict hS0 D2i
  have hint : ∀ (g : (I → ℝ) → ℂ) (t : ℂ), AEStronglyMeasurable g volume →
      (∀ σ : ℝ, Integrable (fun y => ‖g y‖ * Real.exp (σ * ∑ i, y i)) (volume.restrict S)) →
      Integrable (fun y => g y * Complex.exp (t * ((∑ i, y i : ℝ) : ℂ))) (volume.restrict S) := by
    intro g t hg hgi
    refine (hgi t.re).mono' (hg.restrict.mul (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  set f1 : ℂ → ℂ := fun s => ∫ y in S, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf1
  set f2 : ℂ → ℂ := fun s => ∫ y in S, (p (-y) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf2
  have hd1 : Differentiable ℂ f1 := A1.1
  have hd2 : Differentiable ℂ f2 := A2.1
  have hb1 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f1 := A1.2
  have hb2 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f2 := A2.2
  refine ⟨fun s => 2 ^ Fintype.card I * (f1 s + κ * f2 (1 - s)), ?_, ?_, ?_⟩
  · exact (hd1.add ((hd2.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul κ)).const_mul _
  · intro a' b' hab
    obtain ⟨C1, hC1⟩ := hb1 a' b' hab
    obtain ⟨C2, hC2⟩ := hb2 (1 - b') (1 - a') (by linarith)
    refine ⟨‖(2 : ℂ) ^ Fintype.card I‖ * (C1 + ‖κ‖ * C2), fun s h1 h2 => ?_⟩
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add (hC1 s h1 h2) ?_)
    rw [norm_mul]
    gcongr
    exact hC2 (1 - s) (by simp; linarith) (by simp; linarith)
  · intro s hs
    rw [_root_.GlobalTheory.HeckeMellin.archFactor_mul_pSeries_eq_integral K I φ hφ n hn F C hC hinv p hpm hp0 hpsum s hs,
      GlobalTheory.T.mellin_integral_split_functional_equation I p _ _ κ s hfe (hint _ s D1m D1i) (hint _ (1 - s) D2m D2i)]

end GlobalTheory.HeckeStrip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (u v : Fin n → Glob1 F), ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by
  first | exact @GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero | exact GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero | (intros; apply GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module

variable {F : Type} [Field F] {r : ℕ}

def colSet (F : Type) [Field F] (b : Fin r → ℕ) (k : ℕ) : Set (blockTri (κ := F) b) :=
  {p | (p : GL (Fin r) F) ∈ unip F r ∧ ∀ i j : Fin r, j.val < k →
    ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j}

def colChar (ψ : AddChar F ℂ) (b : Fin r → ℕ) (k : Fin r) (l : Fin r → F) (p : blockTri (κ := F) b) : ℂ :=
  ψ (∑ i, l i * ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k +
    edgeSum (fun i j => blkEdge b i j ∧ k < j) (p : GL (Fin r) F))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem eig_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ χ' : G → ℂ) (h : ∀ g ∈ S, χ g = χ' g) : eig τ S χ = eig τ S χ' := by
  ext v
  simp only [mem_eig]
  exact forall₂_congr fun g hg => by rw [h g hg]

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbRegCountOfRanks
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

def untwist {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ Γ W) (χ : Γ →* ℂˣ) :
    Representation ℂ Γ W where
  toFun g := (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ' g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, mul_inv_rev, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply,
      LinearMap.map_smul, smul_smul]
    ring_nf

theorem untwist_apply {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ Γ W)
    (χ : Γ →* ℂˣ) (g : Γ) (w : W) : untwist ρ' χ g w = (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ' g w := rfl

theorem embReg_count_of_ranks : ∀ (K Γ R W : Type) [Field K] [Algebra K ℂ] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (Hb H : Subgroup Γ) [Fintype Hb] [DecidableEq Hb] [Fintype H] [DecidableEq H] (u0 u : R), (Matrix.of fun h g : Hb => act ((h : Γ) * g) u0).det ∈ nonZeroDivisors R → (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V V1 V2 : Submodule K R) [FiniteDimensional K V] [FiniteDimensional K V2] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : Hb, ∀ x ∈ Vm, x * act h u0 ∈ V) → (∀ h : H, ∀ x ∈ V, x * act h u ∈ V1) → (∀ h : H, ∀ x ∈ V1, act h x ∈ V1) → (∀ h : H, ∀ x ∈ V1, x * act h u ∈ V2) → ∀ c : ℝ, 0 ≤ c → (finrank K V2 : ℝ) ≤ c * finrank K Vm → ∀ [AddCommGroup W] [Module K W] [Module ℂ W] [IsScalarTower K ℂ W] (f : V →ₗ[K] W), IsBaseChange ℂ f → ∀ (ρ' : Representation ℂ Γ W) (χ : Γ →* ℂˣ), (∀ g v, ρ' g (f v) = ((χ g : ℂˣ) : ℂ) • f (ρ g v)) → ∀ lam : Hb →* ℂˣ, ∃ n : ℕ, EmbReg ρ' H n ∧ (n : ℝ) * Nat.card H ≤ c * Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by
  intro K Γ R W _ _ _ _ _ _ act Hb H _ _ _ _ u0 u hu0 hu Vm V V1 V2 _ _ ρ hρ hVm hV hV1 hV2 c hc hcr _ _ _ _ f hf ρ' χ hρ' lam
  obtain ⟨n, hn, hnle⟩ := GlobalTheory.T.embedsInRegularRepresentationCopies_of_groupDeterminant K Γ R act H u hu V V1 V2 ρ hρ hV hV1 hV2
  have hf'' : ∀ g v, untwist ρ' χ g (f v) = f (ρ g v) := by
    intro g v
    rw [untwist_apply, hρ', smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hn'' : EmbReg (untwist ρ' χ) H n :=
    embReg_of_isBaseChange K ℂ Γ V W f hf ρ (untwist ρ' χ) hf'' H n hn
  have hn' : EmbReg ρ' H n := by
    refine _root_.GlobalTheory.BadCount.embReg_twist ℂ Γ W (untwist ρ' χ) ρ' χ ?_ H n hn''
    intro g v
    rw [untwist_apply, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let lam' : Hb →* ℂˣ := lam * (χ.comp Hb.subtype)⁻¹
  have heig : eig ρ' Hb lam = eig (untwist ρ' χ) Hb lam' := by
    ext v
    rw [mem_eig, mem_eig]
    refine forall_congr' fun h => ?_
    rw [untwist_apply]
    simp only [lam', MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Units.val_mul]
    constructor
    · intro e; rw [e, smul_smul, mul_comm]
    · intro e
      have := congrArg (fun w => ((χ (h : Γ) : ℂˣ) : ℂ) • w) e
      simp only [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] at this
      rw [this]; congr 1
      rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hlow := _root_.GlobalTheory.BadCount.finrank_le_card_mul_finrank_eig_baseChange K ℂ Γ R W act Hb u0 hu0 Vm V ρ hρ hVm f hf (untwist ρ' χ) hf'' lam'
  rw [← heig] at hlow
  refine ⟨n, hn', ?_⟩
  have h1 : ((n * Nat.card H : ℕ) : ℝ) ≤ finrank K V2 := by exact_mod_cast hnle
  have h2 : (finrank K Vm : ℝ) ≤ Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by exact_mod_cast hlow
  push_cast at h1
  calc (n : ℝ) * Nat.card H ≤ finrank K V2 := h1
    _ ≤ c * finrank K Vm := hcr
    _ ≤ c * (Nat.card Hb * finrank ℂ (eig ρ' Hb lam)) := mul_le_mul_of_nonneg_left h2 hc
    _ = c * Nat.card Hb * finrank ℂ (eig ρ' Hb lam) := by ring

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_coefficientRing_invariance : GlobalTheory.EtC.A8 := by
  first
  | exact @GlobalTheory.EtC.a8
  | exact GlobalTheory.EtC.a8
  | (intros; apply GlobalTheory.EtC.a8 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecompositionStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition : ∀ (O : Type) [CommRing O] (N : GlobalTheory.Ex.NumD O) (S : Subring O) (m : ℕ) (h : N.Gt) (y : N.X), h ^ m = N.io y → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.θ x x' x'' : O) ∈ S ∧ (((N.θ x x' x'')⁻¹ : Oˣ) : O) ∈ S) → (∀ x ∈ Subgroup.closure (Set.range N.c ∪ {h.b}), (N.σ x : O) ∈ S ∧ (((N.σ x)⁻¹ : Oˣ) : O) ∈ S) → ∀ a b : N.X, ∃ w : Oˣ, (w : O) ∈ S ∧ N.ψ (m • a + b) * h.s (m • a + b) = w * N.ψ a ^ (m ^ 2) * N.τ a (m • b + y) * (N.ψ b * h.s b) := by
  first | exact @GlobalTheory.theta_term_smul_add | exact GlobalTheory.theta_term_smul_add | (intros; apply GlobalTheory.theta_term_smul_add <;> assumption)
end

