module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharDotProductTrivialOnTsupportNhds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLatticeComponentIntegralFrameCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal.LatChar

variable {D : D7}

theorem finPart_pair_zero (α : Af D.host.F) (x : D.host.E) :
    finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = α ⊗ₜ[D.host.F] x := rfl

theorem latV_int {S : HSp D} {L : Lat S} (hL : ∀ z ∈ L, z ∈ intVec D S.rank) {P : Pl D → Prop}
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) (i : Fin S.rank) : finPart D (y i) ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    change finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) ∈ intAE D
    rw [finPart_pair_zero, one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => rw [Pi.zero_apply, RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Pi.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [Pi.neg_apply, RingHom.map_neg]; exact neg_mem hx

theorem lat_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
    {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    β.IsLat L Λ → (∀ z, z ∈ L ↔ z ∈ intVec D _) → ∀ x : n → k, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  intro D k _ _ _ _ p S n _ _ β L Λ hΛ hL x
  rw [hΛ x]
  constructor
  · intro h r
    exact (p.int_iff _).2 (latV_int (fun z hz => (hL z).1 hz) h r)
  · intro h
    have h1 : (fun i => p.sec ((β.b *ᵥ x) i)) =
        ∑ r, fun i => p.sec ((β.b *ᵥ x) r) * incA D ((Pi.single r 1 : Fin S.rank → D.host.E) i) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, RingHom.map_one, mul_one]
      · intro r _ hr
        rw [Pi.single_eq_of_ne hr.symm, RingHom.map_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h1]
    refine sum_mem fun r _ => GlobalTheory.FinPl.FrameLat.int_mul_mem (GlobalTheory.FinPl.FrameLat.sec_mem_intAt p _ (h r)) ((hL _).2 fun i => ?_)
    by_cases hi : i = r
    · subst hi; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hi]; exact isIntegral_zero

end GlobalTheory.PhiOneVal.LatChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineColumnTranslationHeisenberg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrFrameCol

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule GlobalTheory.KappaHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul_rat (p : Place D k) {l m r : ℕ} (N : Matrix (Fin r) (Fin l) k) (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι : Mx D r l) * rat M = (N * M.map p.pr).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, rat, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, BoxModel.incA_mul_ι, mul_comm]

theorem qB_β (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F) :
    B.o.qB.map p.pr * F.β = fromCols 0 (Matrix.of fun r _ => s * p.pr (B.ζ r)) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map p.pr = M.map (BoxModel.prH p) :=
    fun _ => rfl
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · have : (B.o.qB.map p.pr * F.β) r (Sum.inl a) = (B.o.qB.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      simp only [Matrix.mul_apply (M := B.o.qB.map p.pr), h.1]
    rw [this, ← Matrix.mul_assoc, ← BoxModel.map_pr_mul, B.o.qB_iA, hm]
    simp
  · have h1 : B.o.qB *ᵥ vecB B.o B.ζ = B.ζ := by
      rw [vecB, Matrix.mulVec_mulVec, B.o.qB_iB, Matrix.one_mulVec]
    have h2 : p.pr (B.ζ r) = ∑ j, p.pr (B.o.qB r j) * p.pr (vecB B.o B.ζ j) := by
      conv_lhs => rw [← h1]
      change BoxModel.prH p (∑ j, B.o.qB r j * vecB B.o B.ζ j) = ∑ j, BoxModel.prH p _ * BoxModel.prH p _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul]
    rw [fromCols_apply_inr, Matrix.of_apply, h2, Finset.mul_sum, Matrix.mul_apply]
    simp only [h.2, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem line_γ_iA (p : Place D k) {n m : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F)
    (y : Matrix m Unit k) :
    fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr = 0 := by
  have h1 : fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β = 0 := by
    ext r a
    have : (fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β) r a
        = (fromCols (0 : Matrix m n k) y * F.γ * F.β) r (Sum.inl a) := by
      rw [Matrix.mul_assoc (_ * F.γ)]
      simp only [Matrix.mul_apply (M := fromCols (0 : Matrix m n k) y * F.γ), h.1]
    rw [this, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    simp
  rw [← Matrix.mul_one (_ * B.o.iA.map p.pr), ← FA.βγ, ← Matrix.mul_assoc, h1, Matrix.zero_mul]

theorem xi_mul_hO (L S : HSp D) (Y : WO L S) (z : Mx D L.rank S.rank) :
    incA D D.host.xi0 * hO L S Y (ofAdj L S z) = (z * Y).trace := by
  conv_rhs => rw [← starAdj_ofAdj L S z]
  rw [hO_eq_trace, starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem link_frames (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (s : k)
    {n' n'' : Type} [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) (h' : p.IsCoreFrame B' (s * p.xi) FA' F₀') :
    B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))
      = F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k) := by
  rw [qB_β p B' _ FA' F₀' h', ← Matrix.mul_assoc, ← BoxModel.map_pr_mul]
  have h1 : (B.o.iB * l.τ) *ᵥ B'.ζ = -vecB B.o B.ζ := by
    rw [← Matrix.mulVec_mulVec, l.map, Matrix.mulVec_neg, vecB]
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · have h2 : ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) = -p.pr (vecB B.o B.ζ r) := by
      have := congrArg (fun v => BoxModel.prH p (v r)) h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.neg_apply, map_neg] at this
      exact this
    have h3 : (F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k)) r (Sum.inr ())
        = F₀.β r (Sum.inr ()) * -p.xi := by
      simp [Matrix.mul_apply, Matrix.single_apply]
    rw [h3, h.2, Matrix.mul_apply]
    simp only [fromCols_apply_inr, Matrix.of_apply, Matrix.map_apply]
    calc _ = s * p.xi * ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h2]; ring

theorem frame_col : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ y₀ : n → k, ∃ x : WO S B'.L, p.up F₀ FS (fromCols 0 (Matrix.of fun r _ => y₀ r)) = (B.o.resS S).symm (0, l.κ S x) ∧ IsHalf (cA D p.e) ((B'.o.resT S).symm (0, x)) ∧ ∀ t : Matrix (n'' ⊕ Unit) n k, ψ (symplO S B'.V₀ (p.up FS F₀' t) ((B'.o.resT S).symm (0, x))) = ((ψk (-(t (Sum.inr ()) ⬝ᵥ y₀)) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s _ n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h h' y₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  have hτ : l.τ ≠ 0 := by
    intro h0
    have h1 := l.map
    rw [h0, Matrix.zero_mulVec, eq_comm, neg_eq_zero] at h1
    exact B.line.2 (by rw [h1, Matrix.mulVec_zero, dotProduct_zero])
  obtain ⟨τi, -, hi⟩ := LinkGram.exists_inv_of_rank_one B.line.1 B'.line.1 l.τ hτ
  set M : Matrix n (n' ⊕ Unit) k := fromCols 0 (Matrix.of fun r _ => y₀ r) with hM
  set Y : WO B.L S := p.up F₀ FS M * B.o.jB with hY
  have hYh : IsHalf p.e Y := isHalf_mul_right _ (GlobalTheory.LocSympl.up_half p F₀ FS M)
  have hκ : l.κ S (rat τi * starAdj B.L S Y) = Y := by
    rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hi, rat_one, Matrix.one_mul, LinkGram.ofAdj_starAdj]
  refine ⟨rat τi * starAdj B.L S Y, ?_, ?_, fun t => ?_⟩
  · rw [hκ, AddEquiv.eq_symm_apply, OrthDec.resS_apply]
    refine Prod.ext ?_ rfl
    change (FS.β * M * F₀.γ).map p.ι * rat B.o.iA = 0
    rw [ι_mul_rat, Matrix.mul_assoc FS.β, Matrix.mul_assoc FS.β, hM, line_γ_iA p B s FA F₀ h]
    simp
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (isHalf_mul_left _ (isHalf_smul _ (isHalf_mul_left _
      (isHalf_mul_right _ (isHalf_cA_adj hYh)))))
  · rw [GlobalTheory.LocSympl.psi_sympl_up p FS F₀' ψ ψk hk, OrthDec.hO_resT _ S, AddEquiv.apply_symm_apply,
      OrthDec.resT_apply]
    have hg := (LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
    have h0 : ∀ u : WO S B'.A, hO S B'.A u 0 = 0 := fun u => by
      rw [hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero]
    have h1 := GlobalTheory.LinkKappa.hO_ofAdj B.L B'.L S l.τ _ hg (rat τi * starAdj B.L S Y)
      (B'.o.pB * p.up FS F₀' t)
    rw [Int.cast_one, map_one, one_mul] at h1
    change hO B.L S (l.κ S _) _ = _ at h1
    rw [hκ] at h1
    have h2 := congrArg p.π (xi_mul_hO B.L S Y (rat l.τ * (B'.o.pB * p.up FS F₀' t)))
    rw [h1, map_mul] at h2
    have h3 : p.π (rat l.τ * (B'.o.pB * p.up FS F₀' t) * Y).trace = p.xi * -(t (Sum.inr ()) ⬝ᵥ y₀) := by
      have e1 : rat l.τ * (B'.o.pB * p.up FS F₀' t)
          = (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ))).map p.ι := by
        rw [← BoxModel.rat_mul_ι, ← BoxModel.rat_mul_ι]; rfl
      have e2 : Y = (FS.β * M * F₀.γ * B.o.iB.map p.pr).map p.ι := by
        rw [← ι_mul_rat]; rfl
      have e3 : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) k), (N.map p.ι).map p.π = N := fun N => by
        ext i j; exact p.π_ι _
      rw [AddMonoidHom.map_trace p.π, Matrix.map_mul, e1, e2, e3, e3, ← Matrix.mul_assoc _ _ (B.o.iB.map p.pr),
        Matrix.trace_mul_comm]
      have e4 : B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ)) * (FS.β * M * F₀.γ))
          = (B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))) * (t * (FS.γ * FS.β) * M) * F₀.γ := by
        simp only [Matrix.mul_assoc]
      rw [e4, link_frames p B B' l s FA F₀ FA' F₀' h h', FS.γβ, Matrix.mul_one, Matrix.trace_mul_comm,
        ← Matrix.mul_assoc F₀.γ, ← Matrix.mul_assoc F₀.γ F₀.β, F₀.γβ, Matrix.one_mul, Matrix.trace_single_mul]
      simp [hM, Matrix.mul_apply, dotProduct]
    rw [h3] at h2
    rw [h0, zero_add, mul_left_cancel₀ hxi h2]

end GlobalTheory.ContrFrameCol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineComponentsContraction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem contraction_all : ∀ D : D7, GlobalTheory.FinPl.Contraction D := by
  intro D k _ _ _ _ _ _ p ψ χ hχ
  obtain ⟨ε, hε, hloc⟩ := _root_.GlobalTheory.FinPl.LineAct.line_act D k p ψ χ hχ
  refine ⟨ε, hε, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ _ L₁ L₂ L₂' L₃ f₁ Ξ₁ Ξ₁' f₂ Ξ₂ Ξ₂' Ψ₁ Ψ₂
    a a' b b' ha ha' hb hb' h1 h1' h2 h2' φ hφ
  by_cases hA0 : a = 0 ∧ a' = 0
  · obtain ⟨rfl, rfl⟩ := hA0
    simp
  by_cases hB0 : b = 0 ∧ b' = 0
  · obtain ⟨rfl, rfl⟩ := hB0
    simp
  have hstd : IsStdChar D ψ (-1) := s₁.weil.std
  obtain ⟨sbC, sbC', sbR, sbR'⟩ := GlobalTheory.FinPl.tens_SB_iff k n n'
  obtain ⟨sbC2, sbC2', sbR2, sbR2'⟩ := GlobalTheory.FinPl.tens_SB_iff k n n''
  have hΨ₁ : Ψ₁ ∈ SB (Matrix n n' k) := by
    by_cases h0 : a = 0
    · exact sbC' Ψ₁ a' h1'.2.2.2.1 (fun h => hA0 ⟨h0, h⟩)
    · exact sbC' Ψ₁ a h1.2.2.2.1 h0
  have hΨ₂ : Ψ₂ ∈ SB (Matrix n'' n k) := by
    by_cases h0 : b = 0
    · exact sbR2' Ψ₂ b' h2'.2.2.2.1 (fun h => hB0 ⟨h0, h⟩)
    · exact sbR2' Ψ₂ b h2.2.2.2.1 h0
  obtain ⟨⟨T₁, hT₁⟩, -⟩ := h1.2.2.2.2
  obtain ⟨⟨T₂, hT₂⟩, -⟩ := h2.2.2.2.2
  let A : ((n → k) → ℂ) → (WO B.V₀ J.W₀ → ℂ) := fun a => T₁ (extFun α₀ β (tensCol Ψ₁ a))
  let Bb : ((n → k) → ℂ) → (WO J.W₀ B'.V₀ → ℂ) := fun b => T₂ (extFun β γ₀ (tensRow Ψ₂ b))
  have hA_eq : ∀ a₀ Ξ, Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) Ξ → Ξ = A a₀ := fun a₀ Ξ h => h.2.2.2.2.2 T₁ hT₁
  have hB_eq : ∀ b₀ Ξ, Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) Ξ → Ξ = Bb b₀ := fun b₀ Ξ h => h.2.2.2.2.2 T₂ hT₂
  have OB1 := _root_.GlobalTheory.FinPl.overBasic D k p n (n' ⊕ Fin 1) ψ hstd B.V₀ J.W₀ α₀ β L₁ L₂ h1.1 h1.2.1 f₁ h1.2.2.1
  have OB2 := _root_.GlobalTheory.FinPl.overBasic D k p (n'' ⊕ Fin 1) n ψ hstd J.W₀ B'.V₀ β γ₀ L₂' L₃ h2.1 h2.2.1 f₂ h2.2.2.1
  have hA_over : ∀ a₀ ∈ SB (n → k), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) (A a₀) := by
    intro a₀ ha₀
    obtain ⟨f, hf, -⟩ := OB1.1 _ (sbC Ψ₁ a₀ hΨ₁ ha₀)
    rwa [← hA_eq a₀ f hf]
  have hB_over : ∀ b₀ ∈ SB (n → k), Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) (Bb b₀) := by
    intro b₀ hb₀
    obtain ⟨f, hf, -⟩ := OB2.1 _ (sbR2 Ψ₂ b₀ hΨ₂ hb₀)
    rwa [← hB_eq b₀ f hf]
  have hA_th : ∀ a₀ ∈ SB (n → k), IsThetaFunO ψ B.V₀ J.W₀ (A a₀) := fun a₀ h => (OB1.2.1 _ _ (hA_over a₀ h)).1
  have hB_th : ∀ b₀ ∈ SB (n → k), IsThetaFunO ψ J.W₀ B'.V₀ (Bb b₀) := fun b₀ h => (OB2.2.1 _ _ (hB_over b₀ h)).1
  have hA_add : ∀ a₀ a₁, A (a₀ + a₁) = A a₀ + A a₁ := by
    intro a₀ a₁
    show T₁ _ = T₁ _ + T₁ _
    rw [← map_add (f := _)]; congr 1; funext x
    simp only [extFun, tensCol, Pi.add_apply]
    split_ifs <;> ring
  have hA_smul : ∀ (c : ℂ) a₀, A (c • a₀) = c • A a₀ := by
    intro c a₀
    show T₁ _ = c • T₁ _
    rw [← map_smul]; congr 1; funext x
    simp only [extFun, tensCol, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  have hB_add : ∀ b₀ b₁, Bb (b₀ + b₁) = Bb b₀ + Bb b₁ := by
    intro b₀ b₁
    show T₂ _ = T₂ _ + T₂ _
    rw [← map_add (f := _)]; congr 1; funext x
    simp only [extFun, tensRow, Pi.add_apply]
    split_ifs <;> ring
  have hB_smul : ∀ (c : ℂ) b₀, Bb (c • b₀) = c • Bb b₀ := by
    intro c b₀
    show T₂ _ = c • T₂ _
    rw [← map_smul]; congr 1; funext x
    simp only [extFun, tensRow, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  obtain ⟨add₁, smul₁, add₂, smul₂⟩ := GlobalTheory.DoubleStepLin.besselFourierJacobi_doubleUnfolding_bilinear D ψ σ B J B' s₁ s₂ l vL φ hφ
  obtain ⟨hχc, hχ1⟩ := GlobalTheory.FinPl.SplitChar.cont_ne_one D k p ψ χ hχ hstd
  let χε : AddChar k Circle := χ.compAddMonoidHom (AddMonoidHom.mulLeft ε)
  have hχε : ∀ x, χε x = χ (ε * x) := fun x => rfl
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [h]
  have hχεc : Continuous χε := hχc.comp (continuous_const.mul continuous_id)
  have hχε1 : χε ≠ 1 := by
    intro h
    apply hχ1
    ext x
    have := congrArg (fun f : AddChar k Circle => f (ε * x)) h
    simp only [hχε, AddChar.one_apply] at this
    rw [← mul_assoc, hε2, one_mul] at this
    simp [this]
  have key : ∀ h₁ : GA D B'.A, ∃ c : ℂ, ∀ a₀ b₀ : SB (n → k), hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁ =
      c * ∫ η, (∫ y, a₀.1 y * (χε (η ⬝ᵥ y) : ℂ) ∂μ) * b₀.1 η ∂μ := by
    intro h₁
    let Bf : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun a₀ b₀ => hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁)
      (fun m₁ m₂ n₀ => by
        simp only [Submodule.coe_add, hA_add]
        rw [add₁ _ _ _ (hA_th _ m₁.2) (hA_th _ m₂.2) (hB_th _ n₀.2)]; rfl)
      (fun c m n₀ => by
        simp only [Submodule.coe_smul, hA_smul]
        rw [smul₁]; rfl)
      (fun m n₁ n₂ => by
        simp only [Submodule.coe_add, hB_add]
        rw [add₂ _ _ _ (hA_th _ m.2) (hB_th _ n₁.2) (hB_th _ n₂.2)]; rfl)
      (fun c m n₀ => by
        simp only [Submodule.coe_smul, hB_smul]
        rw [smul₂]; rfl)
    obtain ⟨c, hc⟩ := GlobalTheory.HeisLine.heis_invariant_form k n χε hχεc hχε1 μ Bf
      (fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by
        obtain ⟨⟨w₀, hw₁, hw₂⟩, -⟩ := hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t
        have e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1) := by
          have hfun : a₁.1 = fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a₀.1 y := funext fun y => by rw [ha₁ y, hχε]
          rw [hfun]
          exact (hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm
        have e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1) := by
          have hfun : b₁.1 = fun η => b₀.1 (η - t) := funext hb₁
          rw [hfun]
          exact (hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm
        show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁
        rw [e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])
      (fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by
        obtain ⟨-, ⟨w₀, hw₁, hw₂⟩⟩ := hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t
        have e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1) := by
          have hfun : a₁.1 = fun y => a₀.1 (y - t) := funext ha₁
          rw [hfun]
          exact (hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm
        have e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1) := by
          have hfun : b₁.1 = fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b₀.1 η := funext fun η => by rw [hb₁ η, hχε]
          rw [hfun]
          exact (hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm
        show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁
        rw [e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])
    exact ⟨c, fun a₀ b₀ => hc a₀ b₀⟩
  have eΞ₁ := hA_eq a Ξ₁ h1
  have eΞ₁' := hA_eq a' Ξ₁' h1'
  have eΞ₂ := hB_eq b Ξ₂ h2
  have eΞ₂' := hB_eq b' Ξ₂' h2'
  funext h₁
  obtain ⟨c, hc⟩ := key h₁
  have k1 := hc ⟨a, ha⟩ ⟨b, hb⟩
  have k2 := hc ⟨a', ha'⟩ ⟨b', hb'⟩
  simp only [hχε] at k1 k2
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eΞ₁, eΞ₁', eΞ₂, eΞ₂', k1, k2]
  ring

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearLawHalfVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
  GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinearHalf

open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (NumberField.RingOfIntegers D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E)}
  {a : AE D} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D}

section Model

variable (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (ha : a * a = a)
  (hinf : infPart D a = 0) (hc : a * cA D a = 0) (hf : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
  (he : IsSplitIdem D e) (hae : a * e = e)
  (hfix : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀)

include hW hS hT ha hinf hc hf hTm he hae hfix

theorem base_enlarge {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e S g x) (hy : IsDetAt e T h y)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    om (g, h) f₀ = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt ((((latO S T ΛS ΛT fun _ => True) ⊓ half S T e).relIndex
      ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹) •
      Tm fun t => halfInd a (latO S T ΛS ΛT fun _ => True) (actO S T g⁻¹ h⁻¹ t) := by
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
  haveI := finite_enlarge inferInstance inferInstance he.1 hle
  obtain ⟨R, r1, r2, r3⟩ := exists_reps ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e)
    ((latO S T ΛS ΛT fun _ => True).comap (actAdd S T g⁻¹ h⁻¹) ⊓ half S T e)
  have hR : ∀ u ∈ R, actO S T g⁻¹ h⁻¹ u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf e u := fun u hu =>
    ⟨(r2 u hu).1, (isHalf_iff S T).2 (r2 u hu).2⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT (fun _ => True) → IsHalf e w →
      ∃! v, v ∈ R ∧ w - v ∈ latO S T ΛS ΛT (fun _ => True) := fun w hw hwe =>
    (existsUnique_congr fun v => and_congr_right fun hv =>
      ⟨fun h => h.1, fun h => ⟨h, (isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_sub hwe (hR v hv).2)⟩⟩).1
      (r3 w ⟨hw, (isHalf_iff S T).1 hwe⟩)
  rw [om_eq_sum_lattice hW hS hT he hf hfix hg hh hx hy hR hRu hle, r1,
    model_sum hTm fun u hu => isHalf_mono hae (hR u hu).2,
    sum_halfInd he.1 hc hae (GlobalTheory.SplitScalar.idem_smul_mem he.1) (suppAt_inv hg) (suppAt_inv hh) hR hRu hle]

theorem law_enlarge' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (hle : ∀ w ∈ latO S T ΛS ΛT fun _ => True, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ latO S T ΛS ΛT fun _ => True) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  have h1 := base_enlarge hW hS hT ha hinf hc hf hTm he hae hfix hg hh
    (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
  rw [← Complex.ofReal_inv, sqrt_index inferInstance inferInstance he (isDetAt_detAt e he.1 S g) (isDetAt_detAt e he.1 T h) hle] at h1
  exact om_model_of_base D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hf hTm g h _ h1

theorem law_place' {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) :
    Law om a (latO S T ΛS ΛT fun _ => True) Tm g h (fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h)) := by
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
  obtain ⟨N, hN, h1⟩ := exists_nsmul_actO (ΛS := ΛS) (ΛT := ΛT) inferInstance inferInstance g⁻¹ h⁻¹
  obtain ⟨z, z1, z2⟩ := exists_scalar he T hN
  have z4 : SuppAt e T z⁻¹ := suppAt_of (GlobalTheory.SplitScalar.off_smul_mt_inv z1)
  have l1 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix hg (suppAt_mul hh z4) fun w hw hwe => by
    rw [actO_scalar' z2 g h hwe]
    exact h1 w hw
  have l2 := law_enlarge' hW hS hT ha hinf hc hf hTm he hae hfix (suppAt_one e S) z4 fun w hw hwe => by
    rw [inv_one, inv_inv, actO_scalar z2 hwe]
    exact nsmul_mem hw N
  have l3 := l1.mul inferInstance inferInstance (l2.inv inferInstance inferInstance (fac_ne_zero _ _))
  have e1 : fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T (h * z⁻¹)) =
      fac S T χS χT (detAt e he.1 S g) (detAt e he.1 T h) * fac S T χS χT (detAt e he.1 S 1) (detAt e he.1 T z⁻¹) := by
    rw [← fac_mul, ← MonoidHom.map_mul, ← MonoidHom.map_mul, mul_one]
  exact l3.congr (by rw [inv_one, mul_one]) (mul_inv_cancel_right _ _)
    (by rw [e1, mul_inv_cancel_right₀ (fac_ne_zero _ _)])

end Model

theorem detAt_eq {V : HSp D} (he : e * e = e) {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    x = detAt e he V g :=
  Units.ext (hx.trans (isDetAt_detAt e he V g).symm)

theorem law_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Lat S)
    (ΛT : Lat T) (e : AE D) (f₀ : WO S T → ℂ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsSplitIdem D e → IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀) →
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
    ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y : (AE D)ˣ, IsDetAt e S g x → IsDetAt e T h y →
    ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ →
      om (g, h) (Tm Φ) = GlobalTheory.SplitLinear.fac S T χS χT x y • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ S T χS χT om ΛS ΛT e f₀ Tm hW hS hT he hf hfix hTm g h hg hh x y hx hy Φ hΦ
  have hinf : infPart D e = 0 := GlobalTheory.PlaceModelSum.IsOrthSum.infPart_eq
    ⟨Unit, {()}, fun _ => e, fun _ _ => he, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => e) ()).symm⟩
  rw [detAt_eq he.1 hx, detAt_eq he.1 hy]
  exact law_place' hW hS hT he.1 hinf he.2.1 hf hTm he he.1 hfix hg hh Φ hΦ

end GlobalTheory.SplitLinearHalf

end
end

