module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.ContrHeis

variable {D : D7}

theorem symplOH_kappa {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w w' : WO S B'.L) : symplOH B.L S (l.κ S w) (l.κ S w') = -symplOH S B'.L w w' := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  obtain ⟨-, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)
  rw [symplOH, symplOH, hsym, Int.cast_one, one_mul, mul_neg]

theorem kappa_add {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w w' : WO S B'.L) : l.κ S (w + w') = l.κ S w + l.κ S w' := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).1 w w'

theorem kappa_rat {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w : WO S B'.L) (hw : w ∈ ratMx D B'.L.rank S.rank) : l.κ S w ∈ ratMx D S.rank B.L.rank := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.2.1 w hw

theorem contr_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (Ξ₁ : WO B.V₀ S → ℂ) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ x : WO S B'.L, GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂) = GlobalTheory.Unf.contr l S vL Ξ₁ Ξ₂ := by
  intro D ψ _ ρ σ B B' l S vL Ξ₁ Ξ₂ h₁ h₂ x
  funext u v
  have hT : ∀ (a b : WO S B'.A) (c d : WO S B'.L), symplOH S B'.V₀ ((B'.o.resT S).symm (a, c)) ((B'.o.resT S).symm (b, d)) =
      symplOH S B'.A a b + symplOH S B'.L c d := by
    intro a b c d
    rw [B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hS : ∀ (a b : WO B.A S) (c d : WO B.L S), symplOH B.V₀ S ((B.o.resS S).symm (a, c)) ((B.o.resS S).symm (b, d)) =
      symplOH B.A S a b + symplOH B.L S c d := by
    intro a b c d
    rw [B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  set G : WO S B'.L → ℂ := fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) with hG
  have step : ∀ w, heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂ ((B'.o.resT S).symm (v, w)) *
      heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) = G (w + x) := by
    intro w
    simp only [heisO, hG]
    rw [hT, hS, symplOH_zero_right, symplOH_zero_right, zero_add, zero_add, symplOH_kappa, ← map_add (f := _), ← map_add (f := _),
      Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero, ← kappa_add]
    have e : ψ (symplOH S B'.L w x) * ψ (-symplOH S B'.L w x) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (Ξ₂ ((B'.o.resT S).symm (v, w + x)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S (w + x)))) * e
  have per : ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ a, G (γ + a) = G a := by
    intro γ hγ a
    have r2 : (B'.o.resT S).symm (0, γ) ∈ ratMx D B'.V₀.rank S.rank := by
      refine (B'.o.mem_ratL_resT S _).2 ?_
      rw [AddEquiv.apply_symm_apply]
      exact ⟨zero_mem _, hγ⟩
    have r1 : (B.o.resS S).symm (0, l.κ S γ) ∈ ratMx D S.rank B.V₀.rank := by
      refine (B.o.mem_ratL_resS S _).2 ?_
      rw [AddEquiv.apply_symm_apply]
      exact ⟨zero_mem _, kappa_rat l S γ hγ⟩
    obtain ⟨γ₂, hγ₂⟩ := r2
    obtain ⟨γ₁, hγ₁⟩ := r1
    have q2 := h₂.quasi γ₂ ((B'.o.resT S).symm (v, a))
    have q1 := h₁.quasi γ₁ ((B.o.resS S).symm (u, l.κ S a))
    have e2 : ratW B'.V₀ S γ₂ = (B'.o.resT S).symm (0, γ) := hγ₂
    have e1 : ratW S B.V₀ γ₁ = (B.o.resS S).symm (0, l.κ S γ) := hγ₁
    rw [e2, ← map_add (f := _), Prod.mk_add_mk, zero_add, hT, symplOH_zero_left, zero_add] at q2
    rw [e1, ← map_add (f := _), Prod.mk_add_mk, zero_add, hS, symplOH_zero_left, zero_add, symplOH_kappa, neg_neg] at q1
    simp only [hG]
    rw [kappa_add, q2, q1]
    have e : ψ (-symplOH S B'.L γ a) * ψ (symplOH S B'.L γ a) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    linear_combination (Ξ₂ ((B'.o.resT S).symm (v, a)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S a))) * e
  simp only [contr]
  rw [show (fun w => heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂ ((B'.o.resT S).symm (v, w)) *
      heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) = fun w => G (w + x)
    from funext step]
  exact covolOne_integral_add vL.covol G per x

end GlobalTheory.Unf.ContrHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionThetaFunctionIsLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology

namespace GlobalTheory.ContrModL

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem ι_mul_incA (x : k) (b : D.host.E) : p.ι x * incA D b = p.ι (x * p.pr b) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι x * p.ι (p.π (incA D b))
  rw [p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, Witness.e_ι]

theorem map_ι_mul_rat {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map p.pr).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, ι_mul_incA, map_sum]

theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem core_iA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map p.pr = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have hβ : B.o.iA.map p.pr * FA.β = F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) := by
    ext r a
    rw [← h.1 r a]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  calc F₀.γ * B.o.iA.map p.pr = F₀.γ * (B.o.iA.map p.pr * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = fromRows FA.γ 0 := by
        rw [hβ, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

theorem core_qA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) :
    FA.γ * B.o.qA.map p.pr * F₀.β = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
  have hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]
  have hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero]
  have hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r := by
    intro r
    rw [h.2 r, vecB, map_pr_eq]
    congr 1
    exact (RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)
  have hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0 := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  generalize (B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv
  generalize FA.γ * B.o.qA.map p.pr = X at hA hv ⊢
  ext i (a | u)
  · have := congrFun (congrFun hA i) a
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, fromCols_apply_inl, ← this]
    simp only [h.1]
  · rw [Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]
    simp only [hc, mul_left_comm _ s, ← Finset.mul_sum]
    have h2 := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
    rw [h2, mul_zero]

end SlopeTestRemainingChoices
end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem up_fromCols {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x (0 : Matrix n Unit k)) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have hX : FA.γ * B.o.qA.map p.pr = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) * F₀.γ := by
    rw [← core_qA p B FA F₀ h, Matrix.mul_assoc _ F₀.β, F₀.βγ, Matrix.mul_one]
  have hx : fromCols x (0 : Matrix n Unit k) = x * fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
    rw [Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Place.up, Place.up, OrthDec.pA, rat, map_ι_mul_rat, Matrix.mul_assoc (FS.β * x), hX, hx]
  simp only [Matrix.mul_assoc]

theorem up_jA {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀)
    (t : Matrix n (n' ⊕ Unit) k) : p.up F₀ FS t ⬝ B.o.jA = p.up FA FS t.toCols₁ := by
  rw [Place.up, Place.up, OrthDec.jA, rat, map_ι_mul_rat, Matrix.mul_assoc _ F₀.γ, core_iA p B FA F₀ h]
  conv_lhs => rw [← fromCols_toCols t]
  rw [Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, ← Matrix.mul_assoc]

end Up

section Pass
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ)

theorem symplOH_zero_r {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have : hO S T x 0 = 0 := by simp [hO]
  simp [symplOH, symplO, this]

theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO V S → ℂ) (a u : WO A S) (z : WO L S) :
    heisO ψ V S ((o.resS S).symm (a, 0)) f ((o.resS S).symm (u, z)) =
      ψ (symplOH A S u a) * f ((o.resS S).symm (u + a, z)) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ (T₁ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ S → ℂ)), p.IsModel ψ F₀ FS T₁ → ∀ (φ₀ : SB (n → k)) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ (v : WO S B'.A) (T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ)), (∀ Ξ₁ u, T Ξ₁ u = GlobalTheory.Unf.contr l S vL (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁)) Ξ₂ u v) → p.IsModel ψ FA FS T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n' _ _ _ _ FA F₀ FS hcore T₁ hT₁ φ₀ Ξ₂ hΞ₂ v T hT

  have pass : ∀ (a : WO B.A S) (Φ Φ' : SB (Matrix n n' k)),
      T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ') =
        heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ)) →
      T Φ' = heisO ψ B.A S a (T Φ) := by
    intro a Φ Φ' e
    funext u
    rw [hT Φ' u, e]
    change _ = ψ (symplOH B.A S u a) * T Φ (u + a)
    rw [hT Φ (u + a)]
    unfold GlobalTheory.Unf.contr
    rw [← integral_const_mul]
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    rw [heis_pass]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  ·
    haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
    haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
      ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ hΞ₂
    have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) :=
      hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))
    have hint : Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₂).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₂ _)
    have h := GlobalTheory.SuperposS.superpos_isTheta D ψ hψ B.V₀ B.A B.L S B.o (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ))
      (hT₁.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) (l.κ S) (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)))
      (GlobalTheory.ContractionLocal.continuous_kappa l S).measurable hint
    convert h using 1
    funext u
    rw [hT]
    rfl
  ·
    refine pass (p.up FA FS x) Φ Φ' ?_
    rw [← up_fromCols p B S FA F₀ FS hcore x]
    refine hT₁.trans _ _ _ fun t => ?_
    have h1 : (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x := by
      ext i j; simp [Matrix.toCols₁]
    have h2 : (fun r => (t + fromCols x (0 : Matrix n Unit k)) r (Sum.inr ())) = fun r => t r (Sum.inr ()) := by
      funext r; simp
    simp only [GlobalTheory.ContractionLocal.colTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₁.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [← mul_assoc, hy i c]
    · simp only [GlobalTheory.ContractionLocal.colTens_apply, e]
      rw [B.o.symplO_resS S (p.up F₀ FS t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resS_apply B.o S (p.up F₀ FS t)]
      simp only
      rw [up_jA p B S FA F₀ FS hcore t]
      have : symplO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by
        have h0 : hO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem oneBF_red_torus : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W (· = v) → ∀ t : GL (Fin ρ) (AE D), ∀ γ ∈ grpAt J.W₀ (· = v), ∀ κ, InK J.W LW (· = v) κ → 𝔉 (s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f) ≠ 0 → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have h1 : InK B.V LV (· = v) 1 := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y _
    simp
  have hfix : s.om (1, κ) f = f :=
    _root_.GlobalTheory.StabSetFix.stab_fix_vac D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hG.sdV hG.sdW (· = v)
      (fun w hw => hw ▸ ⟨hG.tame, hU.1, hU.2⟩) f hf 1 κ h1 hκ
  have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ f hf.1
  have hsplit : s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f =
      s.om (1, n * J.d.emb0 γ) (s.om (1, J.d.levi t) f) := by
    have : n * J.d.levi t * J.d.emb0 γ * κ = (n * J.d.emb0 γ) * J.d.levi t * κ := by
      rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
      simp only [mul_assoc]
    rw [this]
    have e : ((1 : GA D B.V), (n * J.d.emb0 γ) * J.d.levi t * κ) =
        ((1, n * J.d.emb0 γ) * (1, J.d.levi t)) * (1, κ) := by
      simp
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix]
  intro h0
  apply hne
  rw [hsplit, h𝔉.equiv _ hg n hnN hnG γ hγ, h0]
  have : opA ψ J.d B.o B.ζ s.om₀ n γ 0 = 0 := by
    funext w
    simp [opA, jacT, heisO]
  rw [this, smul_zero]

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomRelationOfPin
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.MiTop.BotTwo

variable {D : D7}

theorem per_smul_f {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem contAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact contAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact contAut_add hx hy
  | zero => simpa using contAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact contAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact contAut_smul (h x) c

theorem lev_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) {k : GA D V} (hk : k ∈ J)
    (g : GA D V) : G x (g * k) = χ k * G x g := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x g with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on generalizing g with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      simp only [Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]; ring
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]; ring
  | zero => simp
  | add T₁ T₂ _ _ h₁ h₂ => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, h₁, h₂]; ring
  | smul c T _ h => simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h]; ring

theorem shift_swap {G A B : Type} [Group G] [Group A] [Group B] (ι : G ≃* A × B) (g w : G) (y : A) (x : B)
    (hw : (ι w).1 = 1) : ι.symm (ι g * (y, x)) * w = g * (ι.symm (1, x) * w) * ι.symm (y, 1) := by
  apply ι.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  ext
  · simp [hw]
  · simp [mul_assoc]

theorem comb_integral {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (c α α' : ℂ) (F F' : Y → ℂ)
    (h : ∀ y, α * F y + α' * F' y = 0) : α * (c * ∫ y, F y ∂ν) + α' * (c * ∫ y, F' y ∂ν) = 0 := by
  have hI : ∫ y, α * F y ∂ν = ∫ y, -(α' * F' y) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => eq_neg_of_add_eq_zero_left (h y))
  rw [integral_neg, integral_const_mul, integral_const_mul] at hI
  linear_combination c * hI

end GlobalTheory.MiTop.BotTwo


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.LevLift

theorem exists_mem_U_finM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  intro B X I _ _ l Z u a Ch A hA i hi β z
  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
    (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) ((I.rec7 l Z).sp.X i) _ (rankN (I.rec7 l Z) i hi)
  obtain ⟨g, hg⟩ := e.toMulEquiv.surjective ⟨z.1, (((A.K i hi β).lev.U_eq z.1).1 z.2).1⟩
  have hfin : z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := by
    rw [← he g]
    have h2 : (e g : GL _ _) = z.1 := congrArg Subtype.val hg
    rw [h2]
  exact ⟨⟨g.1, (hA.U i hi β g.1).2 ⟨g.2, z, hfin⟩⟩, hfin⟩

end GlobalTheory.AdForm.LevLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReadingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ e, IsSplitIdem D e → ∀ (s : GA D S) (s' : GA D T), SuppAt e S s → SuppAt e T s' → ∀ x₀ y₀, IsDetAt e S s x₀ → IsDetAt e T s' y₀ → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T s s' u₀) → ∀ A₁ A₂ : AddSubgroup (VCx D.what₂.Tau a b), (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₁)) → (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂)) → (∀ z ∈ A₂, ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) A₂ → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₁ (alV D.host.d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₂ (alV D.host.d sc) → Formalism.L2.Th1.H.relIdx A₁ A₂ ≠ 0 → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₁ → xiN θ S T hS hT δ sc (om (s, s') f) ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₂ → xiN θ S T hS hT δ sc (om (s, s') f) ≠ 0 → xiN θ S T hS hT δ sc (om (s, s') f) = fun z => ((μ x₀ : ℂ))⁻¹ * (μ y₀ : ℂ) * Formalism.L2.Th1.H.inter (HV sc) (alV D.host.d sc) A₁ A₂ (xiN θ S T hS hT δ sc f) z := by
  first | exact @GlobalTheory.AdForm.SplitGen.moves_reading | exact GlobalTheory.AdForm.SplitGen.moves_reading | (intros; apply GlobalTheory.AdForm.SplitGen.moves_reading <;> assumption)
end

