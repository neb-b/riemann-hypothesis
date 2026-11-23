module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QVal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def places {r : ℕ} (Q : Fin r → QStep S) : GlobalTheory.FinPl.Pl D → Prop := fun v => ∃ i, (Q i).q.v = v

def integrand {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  GlobalTheory.PosOne.comb (conv (List.ofFn fun i => (Q i).e₀.mapDomain (Q i).gl₀)) fun a =>
    S.val c₁ c₂ (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
      φ f (g * a) (h₁ * x) (h₂ * y)

def value {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : ℂ :=
  (∏ i, (Q i).volJ) * ∑ γ : ∀ i, (Q i).A₁, ∑ β : ∀ i, (Q i).A₂, (∏ i, (Q i).w₁ (γ i) * (Q i).w₂ (β i)) *
    S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ (γ i))) (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ (γ i) (β i))) f₁ f₂ φ
      (trc (conv (List.ofFn fun i => ((Q i).e₂ (β i)).mapDomain (Q i).gl₂)) f) g h₁ h₂

def innerVal {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  (Q 0).volJ * ∑ γ : (Q 0).A₁, ∑ β : (Q 0).A₂, ((Q 0).w₁ γ * (Q 0).w₂ β) *
    integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ x y

def Hyps {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : Prop :=
  (∀ i, (Q i).Away c₁ ∧ (Q i).Away c₂) ∧ IsThetaFunO ψ _ _ f₁ ∧ IsThetaFunO ψ _ _ f₂ ∧ (∀ i, (Q i).Vac f₁ f₂) ∧
    IsContAut S.B.A φ ∧ IsContAut S.B'.V f ∧ (∀ i, (Q i).Typed f) ∧ g ∈ GlobalTheory.FinPl.grpOff S.B.V (places Q) ∧
    h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (places Q) ∧ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (places Q)

def Norm {r : ℕ} (Q : Fin r → QStep S) (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q)))
    (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q)))) (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))) : Prop :=
  μ₁.IsHaarMeasure ∧ ρ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ ρ₂.IsHaarMeasure ∧
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 ∧ ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 ∧
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 ∧ ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1

def LocNorm (Q₀ : QStep S) (m₁ : Measure (GL (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1)) Q₀.k)) (s₁ : Measure (RFJ Q₀.k Q₀.n₁ (Q₀.c + 1 + 1) (σ + 1)))
    (m₂ : Measure (GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)) (s₂ : Measure (R Q₀.k Q₀.n₂ (Q₀.c + 1) (σ + 1))) : Prop :=
  m₁.IsHaarMeasure ∧ m₁ (KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))) = 1 ∧ s₁.IsHaarMeasure ∧
    s₁ {x | x.1 ∈ KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))} = 1 ∧ m₂.IsHaarMeasure ∧ m₂ (KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))) = 1 ∧
    s₂.IsHaarMeasure ∧ s₂ {x | x.1 ∈ KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))} = 1

def levJ {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.J.W (places Q)) :=
  (⨆ i, (Q i).L₁.J.map (Q i).gl₁).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))

def levB {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) :=
  (⨆ i, (Q i).L₂.J.map (Q i).gl₂).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q))

end GlobalTheory.QVal

namespace GlobalTheory.QVal

def ValQr (D : D7) (r : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) →
  ∀ (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))))
    (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ →
  ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ →
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)

theorem valQ_of_valQr (D : D7) (h : ∀ r, ValQr D r) : ValQ D := by
  intro ψ hψ σ S r Q hinj P hP μ₁ ρ₁ μ₂ ρ₂ a1 a2 a3 a4 a5 a6 a7 a8 c₁ c₂ hc f₁ f₂ t1 t2 hv φ f hφ hf ht g hg h₁ hh₁ h₂ hh₂
  have e : P = places Q := funext fun v => propext (hP v)
  subst e
  exact h r ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ c₁ c₂ f₁ f₂ φ f g h₁ h₂
    ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩

end GlobalTheory.QVal

namespace GlobalTheory.QVal
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def pint {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V)
    (x : GlobalTheory.FinPl.grpAt S.J.W (places fun i => Q i.succ) × GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)
    (y : GlobalTheory.FinPl.grpAt S.B'.V (places fun i => Q i.succ) × GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) : ℂ :=
  integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)
end GlobalTheory.QVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilHomActionFixOfTrivialAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.OffFix

open scoped TensorProduct

variable {D : D7}

theorem idOff_mul_eq_zero {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x y : AE D}
    (hx : x ∈ idOff D (· = v)) (hy : algebraMap (AF D.host.F) (AE D) ε * y = y) : x * y = 0 := by
  classical
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hc' : ∀ w, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = if w = v then 1 else 0 := by
    intro w
    rw [hc w]
    by_cases h : w = v
    · subst h; rw [if_pos rfl, hv]; rfl
    · rw [if_neg h, hw w h, TensorProduct.zero_tmul]
  have hx0 := (SetCut.mem_idOff_iff_mul (· = v) _ h0 hc' x).1 hx
  rw [← hy, ← mul_assoc, mul_comm x, hx0, zero_mul]

theorem supp_of_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε)
    (hsum : p.e + cA D p.e = algebraMap (AF D.host.F) (AE D) ε) (S T : HSp D) (LS : Lat S) (LT : Lat T) (u : WO S T)
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨
      IsHalf p.e u ∨ IsHalf (cA D p.e) u) :
    ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = u i j := by
  rcases hu with hu | hu | hu
  · intro i j
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, -, hα0, a, -, s, -, t, -, rfl⟩ := hw
      have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
        obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D p.v _ α rfl
        rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
        exact ⟨h0, fun w hw => by rw [hc w, hα0 w hw, TensorProduct.zero_tmul]⟩
      rw [Matrix.of_apply]
      have hfac : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) =
          algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) *
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hfac]
      exact ((placeIdem_acts D p.v ε hε).1 _).1 (Ideal.mul_mem_right _ _ hmem)
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => simp only [Matrix.neg_apply, mul_neg, hx]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
    rw [← hu i j, ← mul_assoc, hce]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
      rw [← hsum, add_mul, p.split.2.1, zero_add, ← map_mul, p.split.1]
    rw [← hu i j, ← mul_assoc, hce]

theorem actO_eq_of_grpOff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T) (g : GA D S) (h : GA D T),
    g ∈ grpOff S (· = p.v) → h ∈ grpOff T (· = p.v) → ∀ u : WO S T,
    (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨ IsHalf p.e u ∨
      IsHalf (cA D p.e) u) → actO S T g h u = u := by
  intro D k _ _ _ _ p S T LS LT g h hg hh u hu
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hsupp := supp_of_mem p hε hsum S T LS LT u hu
  have hA : ∀ i j, (Formalism.L2.Theta.mt T h - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff T (idOff D (· = p.v)) h).1 hh
  have hB : ∀ i j, (Formalism.L2.Theta.mt S g⁻¹ - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff S (idOff D (· = p.v)) g⁻¹).1 (inv_mem hg)
  let U : Matrix (Fin T.rank) (Fin S.rank) (AE D) := u
  have hU : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * U i j = U i j := hsupp
  have h1 : HMul.hMul (Formalism.L2.Theta.mt T h - 1) U = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => idOff_mul_eq_zero hε (hA i l) (hU l j)
  have h2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹ - 1) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idOff_mul_eq_zero hε (hB l j) (hU i l)
  have e1 : HMul.hMul (Formalism.L2.Theta.mt T h) U = U := by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1
  have e2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹) = U := by rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2; exact h2
  show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) U) (Formalism.L2.Theta.mt S g⁻¹) = U
  rw [e1, e2]

end GlobalTheory.FinPl.OffFix

end
end

