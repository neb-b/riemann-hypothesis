module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocFlat.CFac
open scoped Topology

noncomputable section
namespace GlobalTheory.LocFlat.LastColumn

def colJoin (n n' k : Type) [TopologicalSpace k] : Matrix n n' k × (n → k) ≃ₜ Matrix n (n' ⊕ Unit) k where
  toFun p := fromCols p.1 (Matrix.of fun r _ => p.2 r)
  invFun M := (M.toCols₁, fun r => M r (Sum.inr ()))
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · funext r; simp
  right_inv M := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  continuous_toFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using (by fun_prop : Continuous fun a : Matrix n n' k × (n → k) => a.2 r)
  continuous_invFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_pi fun r => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · exact continuous_id.matrix_elem r (Sum.inr ())

def colSplit (n n' k : Type) [TopologicalSpace k] :
    Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, Matrix.of fun r _ => x r (Sum.inr ()))
  invFun p := fromCols p.1 p.2
  left_inv x := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · ext r u; cases u; simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_matrix fun r u => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · simpa using continuous_id.matrix_elem r (Sum.inr ())
  continuous_invFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using continuous_snd.matrix_elem r u

def rowSplit (n n' Z k : Type) [TopologicalSpace k] :
    Matrix n n' k × Matrix (Z ⊕ Unit) n k ≃ₜ (Matrix n n' k × (n → k)) × Matrix Z n k where
  toFun q := ((q.1, q.2 (Sum.inr ())), q.2.toRows₁)
  invFun p := (p.1.1, fromRows p.2 (Matrix.of fun _ => p.1.2))
  left_inv q := by
    obtain ⟨x, M⟩ := q
    refine Prod.ext rfl ?_
    ext (i | u) j
    · simp [toRows₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨⟨x, y⟩, A⟩ := p
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · funext j; simp
    · ext i j; simp [toRows₁]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk continuous_fst (continuous_pi fun j => ?_))
      (continuous_matrix fun i j => ?_)
    · exact continuous_snd.matrix_elem (Sum.inr ()) j
    · simpa [toRows₁] using continuous_snd.matrix_elem (Sum.inl i) j
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_fst) (continuous_matrix fun i j => ?_)
    cases i with
    | inl i => simpa using continuous_snd.matrix_elem i j
    | inr u => simpa using (by fun_prop : Continuous fun a : (Matrix n n' k × (n → k)) × Matrix Z n k => a.1.2 j)

theorem isLocallyConstant_integral {Q Y : Type} [TopologicalSpace Q] [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) {H : Q × Y → ℂ} (hH : IsLocallyConstant H) {K : Set Y} (hK : IsCompact K)
    (hz : ∀ q, ∀ y ∉ K, H (q, y) = 0) : IsLocallyConstant fun q => ∫ y, H (q, y) ∂μ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun q₀ => ?_
  have h1 : ∀ᶠ q in 𝓝 q₀, ∀ y ∈ K, H (q, y) = H (q₀, y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hK fun y _ => ?_
    have h2 : IsLocallyConstant fun p : Q × Y => (H p, H (q₀, p.2)) :=
      hH.prodMk (hH.comp_continuous (by fun_prop))
    filter_upwards [h2.eventually_eq (q₀, y)] with p hp
    simp only [Prod.mk.injEq] at hp
    exact hp.1.trans hp.2.symm
  filter_upwards [h1] with q hq
  congr 1
  funext y
  by_cases hy : y ∈ K
  · exact hq y hy
  · rw [hz q y hy, hz q₀ y hy]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem hatCol_mem_SB (ψ : AddChar k Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] {n n' : Type} [Fintype n] [DecidableEq n]
    {Ψ : Matrix n (n' ⊕ Unit) k → ℂ} (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) :
    (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) ∈
      SB (Matrix n n' k × (n → k)) := by
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  set f : Matrix n n' k × (n → k) → ℂ := fun p => Ψ (colJoin n n' k p) with hfdef
  have hf : f ∈ SB (Matrix n n' k × (n → k)) :=
    ⟨hΨ.1.comp_continuous (colJoin n n' k).continuous, hΨ.2.comp_homeomorph _⟩
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ FourierPi.box n s, ∀ x y, f (x, y + t) = f (x, y) := by
    have h1 := PartialFourier.eventually_add_invariant hf
    have h2 : Filter.Tendsto (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) := by fun_prop
      exact this.tendsto 0
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (h2.eventually h1)
    exact ⟨s, fun t ht x y => by simpa using hs ht (x, y)⟩
  have hfun : (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) =
      fun p => ∫ y, f (p.1, y) * (ψ (y ⬝ᵥ (-p.2)) : ℂ) ∂(Measure.pi fun _ => ν) := by
    funext p
    simp only [GlobalTheory.StepData.hat]
    congr 1
    funext y
    rw [dotProduct_neg, dotProduct_comm, neg_one_mul]
    rfl
  rw [hfun]
  refine ⟨?_, ?_⟩
  · refine isLocallyConstant_integral _
      (H := fun q : (Matrix n n' k × (n → k)) × (n → k) => f (q.1.1, q.2) * (ψ (q.2 ⬝ᵥ (-q.1.2)) : ℂ))
      ?_ (hf.2.image continuous_snd) ?_
    · refine (hf.1.comp_continuous (by fun_prop)).mul ?_
      exact (hc.isLocallyConstant.comp_continuous
        (continuous_snd.dotProduct (continuous_snd.comp continuous_fst).neg)).comp (fun z : Circle => (z : ℂ))
    · intro q y hy
      have : f (q.1, y) = 0 := image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, rfl⟩
      simp [this]
  · refine HasCompactSupport.intro
      ((hf.2.image continuous_fst).prod (FourierPi.isCompact_box (n := n) (c * s⁻¹)).neg) fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : ∀ y, f (p.1, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hp ⟨_, h, rfl⟩
      simp [this]
    · rw [Set.mem_neg] at hp
      exact FourierPi.fourier_eq_zero_pi _ hc (f := fun y => f (p.1, y)) (fun t ht y => hs t ht p.1 y) hp

theorem lastColumn_datum_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z], (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)), ∃ Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k), ∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)), ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ())) := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _
  haveI := hν
  refine ⟨fun Ψ₁ Ψ₂ => ?_, fun Ξ₁ c => ?_⟩
  · let F : SB (Matrix n n' k × (n → k)) := ⟨_, hatCol_mem_SB ψk hψ hne ν Ψ₁.2⟩
    exact ⟨comapH (rowSplit n n' Z k) (prodSB F Ψ₂), fun q => mul_comm _ _⟩
  · exact ⟨comapH (colSplit n n' k) (prodSB Ξ₁ c), fun x => rfl⟩

end GlobalTheory.LocFlat.LastColumn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineRowTranslationHeisenbergSplitPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
open scoped GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineRowFrame

variable {D : D7}

theorem half_mul {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (v : Mx D m n) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu i]

theorem mul_half {e : AE D} {l m n : ℕ} (u : Mx D l m) {v : Mx D m n} (hv : IsHalf e v) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hv a j]

theorem adj_half {e : AE D} {m n : ℕ} {u : Mx D m n} (hu : IsHalf e u) : IsHalf (cA D e) (adj u) := fun i j => by
  change cA D e * cA D (u j i) = cA D (u j i)
  rw [← map_mul, hu j i]

theorem ofAdj_half {e : AE D} (S T : HSp D) {z : Mx D S.rank T.rank} (hz : IsHalf e z) :
    IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) := fun i j => by
  have h := mul_half (giA T) (half_mul (adj_half hz) (gA S)) i j
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.smul_apply, smul_eq_mul, mul_left_comm, h]

theorem xi_mul_hO (S T : HSp D) (x : WO S T) (z : Mx D S.rank T.rank) :
    incA D D.host.xi0 * hO S T x (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) = (z ⬝ x).trace := by
  conv_rhs => rw [← GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj S T z]
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc,
    Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem incA_mul_ι (a : D.host.E) (x : k) : incA D a * p.ι x = p.ι (p.pr a * x) := by
  conv_rhs => rw [← p.π_ι x, Place.pr, ← map_mul, p.ι_π, mul_left_comm, Witness.e_ι]

theorem pr_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) (r : Fin m) :
    p.pr ((M *ᵥ v) r) = ∑ a, p.pr (M r a) * p.pr (v a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem line_row : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ u₀ : n → k, ∃ x : WO S B'.L, p.up FS F₀' (fromRows 0 (Matrix.of fun _ => u₀)) = (B'.o.resT S).symm (0, x) ∧ IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) ∧ ∀ t : Matrix n (n' ⊕ Unit) k, ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (0, l.κ S x))) = ((ψk (-(u₀ ⬝ᵥ fun r => t r (Sum.inr ()))) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h₀ h₀' u₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  obtain ⟨w, hw⟩ : ∃ w, w = u₀ ᵥ* FS.γ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : WO S B'.L, ∀ a c, x a c = p.ι (s * p.xi * p.pr (B'.ζ a) * w c) :=
    ⟨Matrix.of fun a c => p.ι (s * p.xi * p.pr (B'.ζ a) * w c), fun _ _ => rfl⟩
  have hxh : IsHalf p.e x := fun a c => by rw [hx, Witness.e_ι]
  have hy : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  have hh : IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) := by
    rw [hy]
    exact half_mul (ofAdj_half B.L S (mul_half _ hxh)) _
  refine ⟨x, ?_, hh, fun t => ?_⟩
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    ext r c
    have e1 : (F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c = s * p.xi * p.pr (vecB B'.o B'.ζ r) * w c := by
      rw [Matrix.mul_assoc, fromRows_mul, Matrix.zero_mul, Matrix.mul_apply, Fintype.sum_sum_type, ← h₀'.2 r, hw]
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    change p.ι ((F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx]
    change _ = incA D (B'.o.iB r a) * _
    rw [incA_mul_ι]
    congr 1
    ring
  · rw [(GlobalTheory.LocSympl.halves_at_split D k p _ _ B.V₀ S F₀ FS ψ ψk hk).2.2.2.1 t _ hh]
    congr 2
    rw [B.o.hO_resS, AddEquiv.apply_symm_apply, hO_eq_trace B.A, adj_zero, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.trace_zero, zero_add]
    refine mul_left_cancel₀ hxi ?_
    have e2 : ∀ a c, p.π (((rat l.τ : Mx D B.L.rank B'.L.rank) ⬝ x) a c) = -(s * p.xi * w c) * p.pr (B.ζ a) := fun a c => by
      have h1 := pr_mulVec p l.τ B'.ζ a
      rw [l.map, Pi.neg_apply, Place.pr, map_neg, map_neg] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Place.pr, neg_mul, ← mul_neg, h1, Matrix.mul_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, hx, p.π_ι]
      change p.pr (l.τ a b) * _ = _
      ring
    have e3 : ∀ c a, p.π ((p.up F₀ FS t ⬝ B.o.jB) c a) = ∑ r, (FS.β * t * F₀.γ) c r * p.pr (B.o.iB r a) := fun c a => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (p.π_ι _)
    have e4 : ∀ c, ∑ r, (FS.β * t * F₀.γ) c r * F₀.β r (Sum.inr ()) = (FS.β * t) c (Sum.inr ()) := fun c => by
      rw [← Matrix.mul_apply, Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
    have e5 : ∑ c, w c * (FS.β * t) c (Sum.inr ()) = u₀ ⬝ᵥ fun r => t r (Sum.inr ()) := by
      change (w ᵥ* (FS.β * t)) (Sum.inr ()) = (u₀ ᵥ* t) (Sum.inr ())
      rw [hw, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, FS.γβ, Matrix.one_mul]
    change p.π (incA D D.host.xi0) * p.π (hO B.L S (p.up F₀ FS t ⬝ B.o.jB) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S _)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_mul, xi_mul_hO, Matrix.trace_mul_comm, ← e5, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, ← e4,
      Finset.sum_congr rfl fun a _ => (p.π.map_mul _ _).trans (congrArg₂ (· * ·) (e3 c a) (e2 a c))]
    generalize FS.β * t * F₀.γ = M
    simp only [h₀.2, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LineRowFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesMultiplication
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FlatBFLoc.ModelModul
variable {D : D7}

theorem symplectic_pairing_ext_zero_inc_zero {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (t : WO V W)
    (y : WO V₀ W₀) : symplO V W t (dV.ext0 W (dW.inc0 V₀ y)) = symplO V₀ W₀ (dW.p0 ⬝ t ⬝ dV.j0) y := by
  unfold symplO
  congr 2
  have h1 : dW.pY ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pY_j0, Matrix.zero_mul]
  have h2 : dW.pX ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pX_j0, Matrix.zero_mul]
  have h3 : dW.p0 ⬝ (dW.j0 ⬝ y) = y := by rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  rw [dV.hO_coordS, dW.hO_coordT]
  simp only [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc, HypDec.p0_jX, HypDec.p0_jY, HypDec.p0_j0,
    Matrix.mul_zero, Matrix.mul_one, h1, h2, h3]
  simp [pairS, pairT]

theorem isHalf_mul {a b c d : ℕ} {e : AE D} (A : Mx D a b) {y : Mx D b c} (C : Mx D c d) (hy : IsHalf e y) :
    IsHalf e (A ⬝ y ⬝ C) := by
  have h : e • y = y := Matrix.ext fun i j => hy i j
  intro i j
  have h2 : e • (A ⬝ y ⬝ C) = A ⬝ y ⬝ C := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]
  exact congrFun (congrFun h2 i) j

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem mul_iota (b : AE D) (a : k) : b * p.ι a = p.ι (p.π b * a) := by
  have h1 : p.e * p.ι a = p.ι a := by rw [← p.ι_π, p.π_ι]
  have h2 := p.ι_π (b * p.ι a)
  rw [map_mul, p.π_ι, mul_left_comm, h1] at h2
  exact h2.symm

theorem rat_mul_iota {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (A : Matrix (Fin b) (Fin c) k) :
    rat R ⬝ (A.map p.ι : Mx D b c) = ((R.map p.pr * A).map p.ι : Mx D a c) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, mul_iota, Place.pr]

theorem iota_mul_rat {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k) (R : Matrix (Fin b) (Fin c) D.host.E) :
    (A.map p.ι : Mx D a b) ⬝ rat R = ((A * R.map p.pr).map p.ι : Mx D a c) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, Place.pr]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, mul_iota, mul_comm]

theorem map_pr_mul {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (R' : Matrix (Fin b) (Fin c) D.host.E) :
    (R * R').map p.pr = R.map p.pr * R'.map p.pr :=
  Matrix.map_mul (f := p.π.comp (incA D))

theorem q_zero_projection_identities {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) :
    d.q0.map p.pr * d.i₀.map p.pr = 1 ∧ d.q0.map p.pr * d.e.map p.pr = 0 ∧ d.q0.map p.pr * d.e'.map p.pr = 0 := by
  have h1 : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
  have h2 : d.q0 * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jX)
  have h3 : d.q0 * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jY)
  have z : p.pr 0 = 0 := map_zero (p.π.comp (incA D))
  have o : p.pr 1 = 1 := map_one (p.π.comp (incA D))
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pr_mul, h1, Matrix.map_one _ z o]
  · rw [← map_pr_mul, h2, Matrix.map_zero _ z]
  · rw [← map_pr_mul, h3, Matrix.map_zero _ z]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem q_zero_jacobi_frame_projection {ρ : ℕ} (J : JacLev D ρ) (s hh : k) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (h : p.IsJacFrame J s hh G₀ FW) : J.d.q0.map p.pr * FW.β = fromCols G₀.β 0 := by
  obtain ⟨hc, h0, hX, hY⟩ := h
  obtain ⟨q1, q2, q3⟩ := q_zero_projection_identities p J.d
  have key : ∀ (E : Matrix (Fin J.W.rank) (Fin ρ) D.host.E), J.d.q0.map p.pr * E.map p.pr = 0 → ∀ (a : k) (i : Fin ρ)
      (j : Fin c), (∀ r, FW.β r (Sum.inr j) = a * p.pr (E r i)) → ∀ r, (J.d.q0.map p.pr * FW.β) r (Sum.inr j) = 0 := by
    intro E hE a i j hj r
    have := congrFun (congrFun hE r) i
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, hj]
    rw [← mul_zero a, ← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  ext r q
  rcases q with a | j
  · have : (J.d.q0.map p.pr * FW.β) r (Sum.inl a) = (J.d.q0.map p.pr * (J.d.i₀.map p.pr * G₀.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h0]
    rw [this, ← Matrix.mul_assoc, q1, Matrix.one_mul, fromCols_apply_inl]
  · rw [fromCols_apply_inr, Matrix.zero_apply]
    by_cases hj : j.val < ρ
    · exact key _ q2 _ ⟨j.val, hj⟩ j (hX ⟨j.val, hj⟩ j rfl) r
    · have := j.2
      exact key _ q3 _ ⟨2 * ρ - 1 - j.val, by omega⟩ j (hY ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only []; omega)) r

theorem bessel_normal_frame_core_frame_part {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (h : p.IsBesFrame B s FA FV) (j : Fin c)
    (hj : j.val = ρ) : B.d.i₀.map p.pr * F₀.β = FV.β.submatrix id (Sum.map id fun _ => j) := by
  obtain ⟨-, h0, -, hz, -⟩ := h
  ext r q
  rcases q with a | u
  · have : (B.d.i₀.map p.pr * F₀.β) r (Sum.inl a) = (B.d.i₀.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h₀.1]
    rw [this, ← Matrix.mul_assoc, ← map_pr_mul]
    exact (h0 r a).symm
  · cases u
    have h2 : p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) = ∑ m, p.pr (B.d.i₀ r m) * p.pr (vecB B.o B.ζ m) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]
    simp only [Matrix.submatrix_apply, Sum.map_inr, id, hz j hj r, h2, Matrix.mul_apply, Matrix.map_apply, h₀.2,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem core_up {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n)
    (FW : Frame k J.W.rank (n ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV)
    (hJ : p.IsJacFrame J s hh G₀ FW) (j : Fin (c + 1)) (hj : j.val = ρ) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    J.d.p0 ⬝ (p.up FV FW t : WO B.V J.W) ⬝ B.d.j0 = p.up F₀ G₀ (t.submatrix Sum.inl (Sum.map id fun _ => j)) := by
  have h1 := q_zero_jacobi_frame_projection p J s hh G₀ FW hJ
  have h2 := bessel_normal_frame_core_frame_part p B s FA F₀ FV h₀ hB j hj
  have h3 : t * FV.γ * B.d.i₀.map p.pr = t.submatrix id (Sum.map id fun _ => j) * F₀.γ := by
    rw [← Matrix.mul_one (t * FV.γ * B.d.i₀.map p.pr), ← F₀.βγ, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ F₀.β, h2]
    congr 1
    have : t * FV.γ * FV.β = t := by rw [Matrix.mul_assoc, FV.γβ, Matrix.mul_one]
    ext r q
    conv_rhs => rw [← this]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  unfold Place.up HypDec.p0 HypDec.j0
  rw [rat_mul_iota, iota_mul_rat]
  congr 1
  rw [Matrix.mul_assoc FW.β, ← Matrix.mul_assoc _ FW.β, h1, Matrix.mul_assoc, h3]
  refine (Matrix.mul_assoc _ _ _).symm.trans ?_
  congr 1
  ext r q
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem submatrix_affPt (ρ : ℕ) (j : Fin (c + 1)) (hj : j.val = ρ) (x : Matrix n (n' ⊕ Unit) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) :
    (affPt (ρ + 1) x.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) fun r => x r (Sum.inr ())).submatrix Sum.inl
      (Sum.map id fun _ => j) = x := by
  ext r q
  rcases q with a | u
  · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free]
  · cases u
    simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free, hj]

theorem continuous_hO_up {S T : HSp D} (FS : Frame k S.rank n') (FT : Frame k T.rank n) (y : WO S T) :
    Continuous fun t => p.π (hO S T (p.up FS FT t) y) := by
  have hx : ∀ i j, Continuous fun t => p.up FS FT t i j := fun i j =>
    p.cont_ι.comp (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
  refine p.cont_π.comp ?_
  exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => continuous_const.mul (hx _ _)

theorem model_modul : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (y : WO B.V₀ J.W₀), IsHalf (cA D p.e) y → ∀ (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = ψ (symplO B.V₀ J.W₀ (p.up F₀ G₀ t) y) * Ψ.1 t) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ y (L₀ Ψ) := by
  intro D _ hLaws _ k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW h₀ hB hJ Tm hTm L₀ hL₀ y hy
    Ψ Ψ' hΨ'
  have hψc : Continuous ψk := ((_root_.GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std).2.1 ψk hψk).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦSB, hΦ⟩ := ((_root_.GlobalTheory.LocFlat.flat_SB_onto k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have hy' : IsHalf (cA D p.e) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)) := isHalf_mul J.d.j0 B.d.p0 hy
  have hχ : IsLocallyConstant fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) := by
    have h := (GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψk hψc).comp_continuous
      (continuous_hO_up p FV FW (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))
    have h4 := (_root_.GlobalTheory.LocSympl.halves_at_split D k p _ _ B.V J.W FV FW ψ ψk hψk).2.2.2.1
    have h5 : (fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))) = _ :=
      funext fun t => h4 t _ hy'
    rw [h5]
    exact h
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨Φ, hΦSB⟩
  let Φ₂ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) * Φ t,
      hχ.mul hΦSB.1, hΦSB.2.mul_left⟩
  have h1 := hTm.modul _ hy' Φ₁ Φ₂ fun t => rfl
  have hMx : GlobalTheory.FinPl.MxAt (fun _ => True) y := fun i j =>
    ⟨congrFun (congrFun (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj p.split) hy) i) j,
      Ideal.mem_iInf.2 fun w => (w.2 trivial).elim⟩
  have h2 := ((hLaws ψ fun _ => True).1 ρ B J st).Heisenberg₂.core (Tm Φ₁) (hTm.theta Φ₁) y hMx
  have h3 := hL₀ Φ₁ Ψ hΦ.symm
  have h4 : Ψ'.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ₂.1 := by
    funext x
    rw [hΨ' x, ← hΦ]
    unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
    rw [← integral_const_mul]
    congr 1
    funext e
    have hj : ρ < c + 1 := by omega
    simp only [Φ₂]
    rw [symplectic_pairing_ext_zero_inc_zero, core_up p B J s _ FA F₀ FV G₀ FW h₀ hB hJ ⟨ρ, hj⟩ rfl, submatrix_affPt ρ ⟨ρ, hj⟩ rfl, mul_assoc]
  rw [← hL₀ Φ₂ Ψ' h4, h1, h2, h3]

end GlobalTheory.FlatBFLoc.ModelModul
end
end

