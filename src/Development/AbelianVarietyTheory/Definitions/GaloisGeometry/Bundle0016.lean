module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.LocGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}


variable (k N) in
abbrev AdGL : Type := GL (Fin N) k ⧸ Subgroup.center (GL (Fin N) k)

def CoeffLp (p : ℝ) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : Measure (AdGL k N)), μ.IsHaarMeasure →
    ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} →
      ∃ F : AdGL k N → ℝ, (∀ g : GL (Fin N) k, F (QuotientGroup.mk g) = ‖l (π g v)‖) ∧ MemLp F (ENNReal.ofReal p) μ

def IsSqIntCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := CoeffLp 2 π

def IsTemperedCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := ∀ ε : ℝ, 0 < ε → CoeffLp (2 + ε) π

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
section
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DatLoc (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) : Prop :=
  ∀ x x' : Formalism.L2.Col.HomE D.host.E a b,
    (∀ P ∈ SS, ((cl : D.host.E)⁻¹ • (x - x')) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (aaOf D cc) N N')) → Ξ x = Ξ x'

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc]

def KapLawLt (Th : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc) : Prop :=
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ),
    (X.Pj j).IsLatTup L → (X.Pj (j + 1)).IsLatTup La'.2 →
    Th j (c, (X.Lv.lev j c).smul γ L) La' =
      MvPowerSeries.C ((kapG X Kc j c γ)⁻¹) * SA X Kc j (gamAt X j c γ) (Th j (c, L) La')

end Law

section Data

variable {p : ℕ} [Fact p.Prime] {D : D7} (X : Sys p) (E : CEmb X.G)
  (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D)
  {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)

def xiM (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
  movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')

def scal0 (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℂ :=
  muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j La))⁻¹ *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j La)) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ))

def pPow (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℂ_[p] :=
  (p : ℂ_[p]) ^ (∑ v : X.Pl, X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2))

def LamPos : Prop :=
  ∀ v s x, TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = twG X E v s (ρ v (if IsOddPos s then D.host.conj x else x))

def PairOK : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧
    DatLoc D cc SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') ∧
    Differentiable ℂ (kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La')) ∧
    TaylorLogMetric.CoefIn D (kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La')) TaylorLogMetric.Qbar ∧
    scal0 X fd χ muT j La La' ∈ TaylorLogMetric.Qbar ∧
    Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∈ TaylorLogMetric.Qbar ∧
    Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ≠ 0 ∧
    ∀ v : X.Pl, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det ∧
      Submodule.span (X.G.P.W v) ((fun x k => ρ v (x k)) '' (fd.kerN j La : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
        (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧
      Submodule.span (X.G.P.W v) ((fun x k => ρ v (x k)) '' (fd.kerN (j + 1) La' : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
        (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))

def MoveTie : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ),
    (X.Pj j).IsLatTup L → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∃ (e : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (cΞ : ℂ), e * star e = 1 ∧
      (∀ v, fd.frM j (c, (X.Lv.lev j c).smul γ L) v * (gamAt X j c γ v : Matrix _ _ _) = e.map (ρ v) * fd.frM j (c, L) v) ∧
      fd.kerN j (c, (X.Lv.lev j c).smul γ L) = SDLat.smulLat e (fd.kerN j (c, L)) ∧ cΞ ∈ TaylorLogMetric.Qbar ∧
      (∀ x, xiM X fd Ξ₀ j (c, (X.Lv.lev j c).smul γ L) La' x = cΞ * xiM X fd Ξ₀ j (c, L) La' (x ∘ₗ Matrix.toLin' e)) ∧
      pPow X j (c, (X.Lv.lev j c).smul γ L) La' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j (c, (X.Lv.lev j c).smul γ L) La' *
          (Base.chiFac χ _ _ (fd.kerN j (c, (X.Lv.lev j c).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * cΞ) =
        (kapG X ℂ_[p] j c γ)⁻¹ * (pPow X j (c, L) La' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j (c, L) La' *
          (Base.chiFac χ _ _ (fd.kerN j (c, L)) (fd.kerN (j + 1) La'))⁻¹))

def AwayTie (v : X.Pl) (j : ℕ) : Prop :=
  ∃ P : HeightOneSpectrum (𝓞 D.host.E), GL3Theta.SplitP D P ∧
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) ∧ P ∉ SS ∧ Formalism.L2.Col.conjPrime₂ P ∉ SS ∧
    ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal ∧
    (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ v x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) ∧
    (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ v x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) ∧
    ∃ u u' : X.G.Kf, X.vEqK u 0 ∧ X.vEqK u' 0 ∧
      ∀ (La Lb : X.Lt j) (La' Lb' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
        (X.Pj j).IsLatTup Lb.2 → (X.Pj (j + 1)).IsLatTup Lb'.2 → aw X v j La La' = aw X v j Lb Lb' →
        GL3Theta.EqOff D P (fd.kerN j La) (fd.kerN j Lb) ∧ GL3Theta.EqOff D P (fd.kerN (j + 1) La') (fd.kerN (j + 1) Lb') ∧
        fd.frM j La = fd.frM j Lb ∧ fd.frM (j + 1) La' = fd.frM (j + 1) Lb' ∧
        xiM X fd Ξ₀ j La La' = xiM X fd Ξ₀ j Lb Lb' ∧
        pPow X j La La' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j La La') * E.iK (u ^ len X v j Lb.2 * u' ^ len X v (j + 1) Lb'.2) =
          pPow X j Lb Lb' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j Lb Lb') * E.iK (u ^ len X v j La.2 * u' ^ len X v (j + 1) La'.2)

end Data

section DatLocApi

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))} {cl : ℕ}
  {N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}

theorem DatLoc.comp {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ) (f : ℂ → ℂ) :
    DatLoc D cc SS cl N N' fun x => f (Ξ x) :=
  fun x x' hx => congrArg f (h x x' hx)

theorem DatLoc.const_mul {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ) (k : ℂ) :
    DatLoc D cc SS cl N N' fun x => k * Ξ x :=
  h.comp fun y => k * y

theorem DatLoc.of_locP_eq {M : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ)
    (hM : ∀ P ∈ SS, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (aaOf D cc) M M') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (aaOf D cc) N N')) :
    DatLoc D cc SS cl M M' Ξ :=
  fun x x' hx => h x x' fun P hP => hM P hP ▸ hx P hP

theorem DatLoc.add_halfBO {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ)
    (x m : Formalism.L2.Col.HomE D.host.E a b) (hm : m ∈ halfBO SS (perO (aaOf D cc) N N') cl) : Ξ (x + m) = Ξ x := by
  refine h _ _ fun P hP => ?_
  rw [add_sub_cancel_left]
  have h1 := (Submodule.mem_iInf _).1 hm P
  have h2 : Formalism.L2.Ker.expS SS P = 1 := by
    unfold Formalism.L2.Ker.expS
    rw [if_pos hP]
  rw [h2, zpow_one] at h1
  exact h1

theorem DatLoc.invOn {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ) {ι : Type} [Fintype ι]
    (emb : ι → D.host.E →+* ℂ) (δ : ℂ) (hinj : Function.Injective (embH (a := a) (b := b) emb δ)) :
    InvOn (AC emb δ (aaOf D cc) SS N N' cl) (BC emb δ (aaOf D cc) SS N N' cl) (onV emb δ Ξ) := by
  have hon : ∀ x, onV emb δ Ξ (embH emb δ x) = Ξ x := by
    intro x
    have hx : ∃ y, embH emb δ y = embH emb δ x := ⟨x, rfl⟩
    unfold onV
    rw [dite_eq_left hx]
    exact congrArg Ξ (hinj hx.choose_spec)
  rintro _ ⟨x, -, rfl⟩ _ - ⟨m, hm, rfl⟩
  rw [← map_add (f := _), hon, hon]
  exact h.add_halfBO x m hm

end DatLocApi

section LawApi

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Kc : Type} [Field Kc] [Algebra (FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc]

theorem KapLawLt.congr {Th Th' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc} (h : KapLawLt X Kc Th)
    (he : ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      Th' j La La' = Th j La La') : KapLawLt X Kc Th' := by
  intro j hj c L La' γ hL hL'
  have hγ : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul γ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ L).2 hL
  rw [he j hj (c, (X.Lv.lev j c).smul γ L) La' hγ hL', he j hj (c, L) La' hL hL']
  exact h j hj c L La' γ hL hL'

theorem KapLawLt.stab {Th : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc} (h : KapLawLt X Kc Th) {j : ℕ} (hj : j < X.mm)
    (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ) (hL : (X.Pj j).IsLatTup L)
    (hL' : (X.Pj (j + 1)).IsLatTup La'.2) (hε : (X.Lv.lev j c).smul ε L = L) :
    MvPowerSeries.C ((kapG X Kc j c ε)⁻¹) * SA X Kc j (gamAt X j c ε) (Th j (c, L) La') = Th j (c, L) La' := by
  have := h j hj c L La' ε hL hL'
  rw [hε] at this
  exact this.symm

end LawApi

section DataApi

variable {p : ℕ} [Fact p.Prime] {D : D7} (X : Sys p) (E : CEmb X.G)
  (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D)
  {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)

theorem frecG_eq (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' =
      linSub (fun x y => c * subBG E pos fd j La La' x y)
        (pPow X j La La' • serP lam fun z =>
          (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹) *
            kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z) := by
  unfold FrecG pPow scal0 xiM
  congr 3
  funext z
  ring

theorem pPow_eq_prod (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    pPow X j La La' = ∏ v : X.Pl, (p : ℂ_[p]) ^ (X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2)) := by
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  unfold pPow
  induction (Finset.univ : Finset X.Pl) using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hp, ih]

theorem twG_eq_tw (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    twG X E v s = tw X ℂ_[p] v s := rfl

theorem LamPos.even (h : LamPos X E pos lam ρ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : ¬ IsOddPos s) (x : D.host.E) :
    TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = twG X E v s (ρ v x) := by
  rw [h v s x, if_neg hs]

theorem LamPos.odd (h : LamPos X E pos lam ρ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) (x : D.host.E) :
    TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = twG X E v s (ρ v (D.host.conj x)) := by
  rw [h v s x, if_pos hs]

end DataApi

end GlobalTheory.TwU

end
end

