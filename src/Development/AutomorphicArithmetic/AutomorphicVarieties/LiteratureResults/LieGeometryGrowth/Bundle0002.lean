module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
section
noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo.Pf

section Defs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

structure CInv (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  left : ∀ γ g, F (ratGL E a γ * g) = F g
  centre : ∀ t g, F (splitCentre E a t * g) = F g

structure SInv (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  centre : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g
  level : IsOpen {k | act (.fin k) φ = φ}

def Cs {M : Type} [Zero M] (F : GA E a → M) : Prop := ∃ R : ℝ, ∀ g, R < qht g → F g = 0

def QInt (μ : Measure (GA E a)) (F : GA E a → ℂ) : Prop :=
  Integrable (fun x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a) => F x.out) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def qint (μ : Measure (GA E a)) (F : GA E a → ℂ) : ℂ :=
  ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), F x.out ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)

def TwInv (χ : HChar E) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop := ∀ j, SInv (mulChi a χ (cmp j m))

def pt (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) : ℂ :=
  (‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) * (star (ev x g) ⬝ᵥ G *ᵥ ev y g)

theorem cmp_ev {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.inductionOn with
  | tmul φ v => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem ptIp_eq {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a)
    (α β : Co Ξ q) (g : GA E a) :
    ptIp χ G e α β g = ∑ I : Fin q → Fin n, pt χ G (α fun i => e (I i)) (β fun i => e (I i)) g := by
  simp only [ptIp, pt, Finset.mul_sum]

theorem CInv.sum {ι : Type} (s : Finset ι) {F : ι → GA E a → ℂ} (h : ∀ i, CInv (F i)) : CInv fun g => ∑ i ∈ s, F i g :=
  ⟨continuous_finsetSum _ fun i _ => (h i).cont, fun γ g => Finset.sum_congr rfl fun i _ => (h i).left γ g,
    fun t g => Finset.sum_congr rfl fun i _ => (h i).centre t g⟩

theorem cs_pt_left (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) {x : Sm E a ⊗[ℂ] (Fin d → ℂ)} (y : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (h : Cs (ev x)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

theorem cs_pt_right (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) {y : Sm E a ⊗[ℂ] (Fin d → ℂ)}
    (h : Cs (ev y)) : Cs (pt χ G x y) :=
  h.imp fun _ hR g hg => by simp [pt, hR g hg]

end Defs

def InvLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), SInv φ →
    CInv φ.1 ∧ ∀ X : Lie E a, SInv (lie E a X φ)

def BddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → QInt μ F ∧ GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ F

def CsBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), CInv F →
    (Cs F ∨ ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖F g.1‖ ≤ C) → ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C

def CsLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (X : Lie E a), Cs φ.1 → Cs (lie E a X φ).1

def ProdEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ ψ : Sm E a), ∃ θ : Sm E a,
    (∀ g, θ.1 g = starRingEnd ℂ (φ.1 g) * ψ.1 g) ∧
    ∀ (X : Lie E a) g, (lie E a X θ).1 g =
      starRingEnd ℂ ((lie E a X φ).1 g) * ψ.1 g + starRingEnd ℂ (φ.1 g) * (lie E a X ψ).1 g

def StokesFn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (θ : Sm E a) (X : Lie E a), SInv θ → Cs θ.1 → qint μ (lie E a X θ).1 = 0

def LevInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E), HasOne Ξ r → IsTw (a := a) r χ →
    ∀ (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ X, TwInv χ (α X)

def PtInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (χ : HChar E) (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ)
    (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)),
    (∀ g, pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g)) ∧
    ((TwInv χ x → TwInv χ y → CInv (pt χ G x y)) ∧
      ∀ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) → TwInv χ x → TwInv χ y → SInv θ)

def TwLie : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E),
    IsTw (a := a) r χ → ∀ (X : Lie E a) (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x →
      TwInv χ (smLie Ξ X x) ∧ TwInv χ (smAdj Ξ r X x)

def CsTens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (X : Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), Cs (ev x) → Cs (ev (smLie Ξ X x)) ∧ Cs (ev (smAdj Ξ r X x))

def PtDiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G → ∀ x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ),
    ∃ θ : Sm E a, (∀ g, θ.1 g = pt χ G x y g) ∧ ∀ (X : Herm E a) g,
      (lie E a (toL X.1) θ).1 g = pt χ G x (smLie Ξ (toL X.1) y) g - pt χ G (smAdj Ξ r (toL X.1) x) y g

def AdjInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsTw (a := a) r χ → IsAdm Ξ G →
    ∀ (X : Herm E a) (x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)), TwInv χ x → TwInv χ y → Cs (ev x) ∨ Cs (ev y) →
      QInt μ (pt χ G x (smLie Ξ (toL X.1) y)) ∧ QInt μ (pt χ G (smAdj Ξ r (toL X.1) x) y) ∧
        qint μ (pt χ G x (smLie Ξ (toL X.1) y)) = qint μ (pt χ G (smAdj Ξ r (toL X.1) x) y)

def PtD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ)
    (L : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (β : Co Ξ (q + 1)) (η : Co Ξ q) (g : GA E a),
    ptIp χ G e β (dCo L η) g = ((q : ℂ) + 1) * ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g ∧
      ptIp χ G e (del L e β) η g = ∑ J : Fin q → Fin n, ∑ j,
        pt χ G (L (toL (e j).1) (β (Matrix.vecCons (e j) fun i => e (J i)))) (η fun i => e (J i)) g

def ChiOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ g : KernelIndexFullLattice.G1 E a, ‖((chiDet a χ g.1 : ℂˣ) : ℂ)‖ = 1

def RapidBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E) (s : ℝ), χ.IsAbsPow s →
    ∀ (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a) (q : ℕ) (α β : Co Ξ q), Rapid α → Moderate β →
      ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ptIp χ G e α β g.1‖ ≤ C

def ZeroInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (F : GA E a → ℂ), CInv F → (∀ g, ∃ t : ℝ, 0 ≤ t ∧ F g = t) → QInt μ F → qint μ F = 0 → ∀ g, F g = 0

def PtPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), IsAdm Ξ G → ∀ (n : ℕ) (e : Fin n → Herm E a), IsFrame e → ∀ (q : ℕ) (α : Co Ξ q),
    (∀ g, ∃ t : ℝ, 0 ≤ t ∧ ptIp χ G e α α g = t) ∧ ((∀ g, ptIp χ G e α α g = 0) → α = 0)

theorem pairFacts_of_steps (h1 : BddInt) (h2 : CsBdd) (h3 : LevInv) (h4 : PtInv) (h5 : AdjInt) (h6 : PtD) (h7 : RapidBdd)
    (h8 : ZeroInt) (h9 : PtPos) : PairFacts := by
  intro E _ _ _ a ha μ _ U hU Ξ r χ G n e hD q
  have hv := h3 E a ha U hU Ξ r χ hD.one hD.tw
  have hc : ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → CInv (ptIp χ G e α β) := fun α β hα hβ => by
    rw [show ptIp χ G e α β = _ from funext (ptIp_eq χ G e α β)]
    exact CInv.sum _ fun I => (h4 E a χ _ G _ _).2.1 (hv q α hα _) (hv q β hβ _)
  refine ⟨fun α β hα hβ hr hm => ?_, fun α β hα hβ hs => ⟨?_, ?_⟩, fun α hα hi h0 => ?_, fun β η hβ hη hs => ?_⟩
  · obtain ⟨s, hs⟩ := hD.tw.1
    exact (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inr (h7 E a Ξ χ s hs G n e q α β hr hm)))).1
  · refine (h1 E a μ _ (hc α β hα hβ) (h2 E a _ (hc α β hα hβ) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · refine (h1 E a μ _ (hc β α hβ hα) (h2 E a _ (hc β α hβ hα) (.inl ?_))).1
    exact hs.imp fun R hR g hg => by simp [ptIp, hR _ g hg]
  · have hp := h9 E a Ξ χ G hD.adm n e hD.frame q α
    exact hp.2 (h8 E a μ _ (hc α α hα hα) hp.1 hi h0)
  · have hA := fun (J : Fin q → Fin n) (j : Fin n) => h5 E a μ Ξ r χ G hD.tw hD.adm (e j)
      (β (Matrix.vecCons (e j) fun i => e (J i))) (η fun i => e (J i)) (hv _ β hβ _) (hv _ η hη _)
      (hs.imp (fun h => h.imp fun R hR g hg => hR _ g hg) fun h => h.imp fun R hR g hg => hR _ g hg)
    simp only [pair, (h6 E a Ξ χ G n e q (smLie Ξ) β η _).1, (h6 E a Ξ χ G n e q (smAdj Ξ r) β η _).2]
    rw [integral_const_mul, integral_finsetSum _ fun J _ => integrable_finsetSum _ fun j _ => (hA J j).1,
      integral_finsetSum _ fun J _ => integrable_finsetSum _ fun j _ => (hA J j).2.1]
    congr 1
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [integral_finsetSum _ fun j _ => (hA J j).1, integral_finsetSum _ fun j _ => (hA J j).2.1]
    exact Finset.sum_congr rfl fun j _ => (hA J j).2.2

end UpperTheory.V.Lit.Geo.Pf
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullDefs
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open scoped ContDiff TensorProduct

namespace UpperTheory.V.Lit.Geo

section Abs

variable {V' V F : Type} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pb (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') : V' [⋀^Fin q]→L[ℝ] F :=
  (w (H p)).compContinuousLinearMap (fderiv ℝ H p)

theorem pb_apply (H : V' → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V') (v : Fin q → V') :
    pb H w p v = w (H p) fun i => fderiv ℝ H p (v i) := rfl

def flow (W : V → V) (t : ℝ) (p : V) : V := p + t • W p

def hk (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ((w (flow W t p)).curryLeft (W p)).compContinuousLinearMap (fderiv ℝ (flow W t) p)

theorem hk_apply (W : V → V) (t : ℝ) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) (v : Fin q → V) :
    hk W t w p v = w (flow W t p) (Matrix.vecCons (W p) fun i => fderiv ℝ (flow W t) p (v i)) := rfl

def hom (W : V → V) {q : ℕ} (w : V → V [⋀^Fin (q + 1)]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, hk W t w p

def IsField (Y : Set V) (W : V → V) : Prop :=
  ContDiffOn ℝ ∞ W Y ∧ ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, flow W t p ∈ Y

end Abs

section Om

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

structure IsFlow (W : S → V → V) : Prop where
  field : ∀ s, IsField G.Y (W s)
  equiv : ∀ γ s, ∀ p ∈ G.Y, W (G.σ γ s) (G.ρ γ p) = G.ρ γ (W s p)
  homog : ∀ s (t : ℝ), 0 < t → ∀ p ∈ G.Y, W s (t • p) = t • W s p

theorem isFlow_zero : IsFlow G 0 :=
  ⟨fun _ => ⟨contDiffOn_const, fun p hp t _ => by simpa [flow] using hp⟩, fun _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩


open Classical in
def toOm {q : ℕ} (z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) : G.Om q :=
  if h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y then
    ⟨fun s => G.Y.indicator (z s), fun s =>
      ⟨(h s).congr fun _ hp => Set.indicator_of_mem hp _, fun _ hp => Set.indicator_of_notMem hp _⟩⟩
  else 0

theorem toOm_apply {q : ℕ} {z : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)} (h : ∀ s, ContDiffOn ℝ ∞ (z s) G.Y) (s : S) {p : V}
    (hp : p ∈ G.Y) : (toOm G z).1 s p = z s p := by
  rw [toOm, dite_eq_left h]
  exact Set.indicator_of_mem hp _

def pbOm (W : S → V → V) {q : ℕ} (w : G.Om q) : G.Om q := toOm G fun s => pb (flow (W s) 1) (w.1 s)

def homOm (W : S → V → V) {q : ℕ} (w : G.Om (q + 1)) : G.Om q := toOm G fun s => hom (W s) (w.1 s)

structure Good {q : ℕ} (w : G.Om q) : Prop where
  inv : ∀ γ, G.act q γ w = w
  basic : ∀ s, RadBasic G.Y (w.1 s)
  dbasic : ∀ s, RadBasic G.Y ((G.dOm q w).1 s)

end Om

section Ad

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

structure IsFld (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (C : ℝ) : Prop where
  sm : ∀ i j w, ∃ φ : Sm E a, (∀ g, φ.1 g = (Y g).1 i j w) ∧ BddDer φ
  left : ∀ γ t g, Y (ratGL E a γ * splitCentre E a t * g) = Y g
  cpt : ∀ (k : Kinf E a) g, adHerm k (Y (g * infGL E a (Unitary.toUnits k))) = Y g
  lev : ∀ u ∈ U, ∀ g, Y (g * finGL E a u) = Y g
  root : ∀ g (t : ℝ), |t| ≤ 1 → ∃ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 ∧
    ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C

theorem IsStep.fld {U : Subgroup (GL (Fin a) (Af E))} {f : GA E a → ℝ} {Y : GA E a → Herm E a} {C c f₀ : ℝ}
    (h : IsStep U f Y C c f₀) : IsFld U Y C := ⟨h.Y_sm, h.Y_left, h.Y_cpt, h.Y_lev, h.root⟩

theorem IsFld.neg {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C) :
    IsFld U (-Y) C := by
  refine { sm := ?_, left := ?_, cpt := ?_, lev := ?_, root := ?_ }
  · intro i j w
    obtain ⟨φ, h1, h2⟩ := h.sm i j w
    refine ⟨-φ, fun g => congrArg Neg.neg (h1 g), fun X l => ?_⟩
    obtain ⟨B, hB⟩ := h2 X l
    exact ⟨B, fun g => by rw [map_neg]; exact (norm_neg _).trans_le (hB g)⟩
  · exact fun γ t g => congrArg Neg.neg (h.left γ t g)
  · intro k g
    have e := congrArg Subtype.val (h.cpt k g)
    refine Subtype.ext ?_
    change k.1 * (-(Y (g * infGL E a (Unitary.toUnits k))).1) * star k.1 = -(Y g).1
    rw [mul_neg, neg_mul, ← e]
    rfl
  · exact fun u hu g => congrArg Neg.neg (h.lev u hu g)
  · intro g t ht
    obtain ⟨x, h1, h2⟩ := h.root g (-t) (by rwa [abs_neg])
    exact ⟨x, by rw [h1, neg_smul]; exact congrArg (1 + ·) (smul_neg t (Y g).1).symm, h2⟩

def FCorr (U : Subgroup (GL (Fin a) (Af E))) (Y : GA E a → Herm E a) (W : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)),
    W (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) = sand g (hv (Y (infGL E a g * finGL E a x)))

def Bd {Ξ : AlgRep E a} {q : ℕ} (α : Co Ξ q) (g : GA E a) (M : ℝ) : Prop :=
  ∀ X : Fin q → Herm E a, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M * ∏ i, ‖hv (X i)‖

theorem Bd.mono {Ξ : AlgRep E a} {q : ℕ} {α : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (hM : M ≤ M') : Bd α g M' :=
  fun X => (h X).trans (mul_le_mul_of_nonneg_right hM (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem Bd.sub {Ξ : AlgRep E a} {q : ℕ} {α β : Co Ξ q} {g : GA E a} {M M' : ℝ} (h : Bd α g M) (h' : Bd β g M') :
    Bd (α - β) g (M + M') := fun X => by
  rw [sub_apply, map_sub, Pi.sub_apply, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (h X) (h' X))

end Ad

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_le (g : GA E a) (γ : GL (Fin a) E) :
    qht g ≤ height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) :=
  ciInf_le ⟨1, by rintro _ ⟨δ, rfl⟩; exact one_le_height _⟩ γ

private theorem one_le_qht (g : GA E a) : 1 ≤ qht g := le_ciInf fun _ => one_le_height _

private theorem retract_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem qht_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    qht (ratGL E a γ * splitCentre E a t * g) = qht g := by
  unfold qht
  rw [retract_left]
  refine Eq.trans ?_ ((Equiv.mulRight γ).iInf_comp
    (g := fun δ : GL (Fin a) E => height (K := E) (ratGL E a δ * (retractOne g : KernelIndexFullLattice.G1 E a).1)))
  refine congrArg _ (funext fun δ => ?_)
  rw [Equiv.coe_mulRight, map_mul, mul_assoc]

private theorem exists_split (g : GA E a) : ∃ t : ℝ, splitCentre E a t * g = (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

private theorem qht_mul {C : Set (GA E a)} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ g : GA E a, ∀ h ∈ C, qht (g * h) ≤ B * qht g := by
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact (K := E) (n := a)
    (hC.image (continuous_subtype_val.comp (continuous_retractOne (K := E) (n := a))))
  have hc : 0 < heightConst E a := one_pos.trans_le one_le_heightConst
  refine ⟨heightConst E a * M, fun g h hh => ?_⟩
  have hm := hM _ ⟨h, hh, rfl⟩
  have hM0 : 0 < M := (height_pos _).trans_le hm
  rw [← div_le_iff₀' (mul_pos hc hM0)]
  refine le_ciInf fun γ => ?_
  rw [div_le_iff₀' (mul_pos hc hM0)]
  refine (qht_le _ γ).trans ?_
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, mul_right_comm]
  exact (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left hm (mul_pos hc (height_pos _)).le)

private theorem qht_proper (R : ℝ) : ∃ C : Set (GA E a), IsCompact C ∧
    ∀ g : GA E a, qht g ≤ R → ∃ γ t, ratGL E a γ * splitCentre E a t * g ∈ C := by
  obtain ⟨c, N, hc, h⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height E a
  have hR : 0 < max 1 R + 1 := by positivity
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := a)
    (ε := (c * (max 1 R + 1) ^ N)⁻¹) (by positivity)
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (hg.trans_lt ((le_max_right 1 R).trans_lt (lt_add_one _)))
  obtain ⟨t, ht⟩ := exists_split g
  obtain ⟨_, ⟨δ, rfl⟩, x, hx, e⟩ := hC' (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
    (mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) (retractOne g).2) fun v hv => by
      rw [inv_le_iff_one_le_mul₀' (by positivity)]
      have h0 := h (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v hv
      have hp : 0 ≤ Reduction.height (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v := by
        by_contra hn
        have : 0 ≤ c * height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) ^ N := by
          have := height_pos (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
          positivity
        nlinarith [not_le.1 hn]
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (height_pos _).le hγ.le N) hc.le) hp)
  refine ⟨δ⁻¹ * γ, t, ?_⟩
  have e' : ratGL E a δ * x = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := e
  rw [mul_assoc, ht, map_mul, mul_assoc, ← e', map_inv, inv_mul_cancel_left]
  exact hx

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.qhtFacts :
    QhtFacts := by
  intro E _ _ _ a
  exact ⟨one_le_qht, qht_left, fun _ hC => qht_mul hC, qht_proper⟩
end

