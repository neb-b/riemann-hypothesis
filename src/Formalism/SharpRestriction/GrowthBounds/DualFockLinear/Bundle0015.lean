module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0014
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.BaseMatrixAlgebra
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model.TS (fockR)

def RestTSX : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (X : Fin n' → Fin (m + 1) → ℤ), IsDominant X →
    ∃ (Ψ : Module.Dual Kf ↥(Vsp Kf X) ≃ₗ[Kf] ↥(Vsp Kf X)) (c : Kf), c ≠ 0 ∧
      TSProp p n' (W := W) (O := O) ι σ w r X Ψ ∧
      ∀ y u : Vsp Kf X, Ψ.symm y u =
        c * fockR (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
          (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)

def OpFAt {n' : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] {m : ℕ} (TT : Finset (Fin n'))
    (d : Fin n' → ℕ) (rest : Fin n' → Fin (m + 1) → ℤ) (c0 : ℕ)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∀ (κ : Kf) (β s : Vsp Kf rest) (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)),
    ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
      (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
        OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧
      ∀ Y : Vsp Kf (flW (m := m) d),
        fockR ((Θ F' : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
            (Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          κ * fockR (((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
              (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
            ((Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
              (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))

def OpFStep (C : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq), IsUnit hm.det →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        OpFAt TT (dT TT lam0) (topW TT (restW TT lam0)) c0 Θ

def RestOpF : Prop := ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → OpFStep C

theorem tsOpAt_of {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hX : RestTSX)
    {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (rest lam : Fin n' → Fin (m + 1) → ℤ)
    (hlam : IsDominant lam) (c0 : ℕ)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hOp : OpFAt TT d rest c0 Θ) : TSOpAt p n' (W := W) ι σ w r TT d rest lam c0 Θ := by
  obtain ⟨Ψ0, a0, ha0, t0, f0⟩ := hX p n' W Qq O Kf ι σ j w hS m r lam hlam
  obtain ⟨Ψf, af, haf, tf, ff⟩ := hX p n' W Qq O Kf ι σ j w hS m r (flW d) (flW_dom d)
  refine ⟨Ψ0, Ψf, t0, tf, ?_⟩
  intro β F s u hu
  obtain ⟨F', h1, h2⟩ := hOp ((p : Kf) ^ Ar r rest * ((p : Kf) ^ kap1 p lam * a0) / af) β s F
  refine ⟨F', h1, ?_⟩
  intro T z hz
  have e1 : T (Θ F') = af * fockR ((Θ F' : Vsp Kf (flW (m := m) d)) :
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (Ψf T : Vsp Kf (flW (m := m) d)) := by
    rw [← ff (Ψf T) (Θ F'), LinearEquiv.symm_apply_apply]
  rw [e1, h2 (Ψf T), f0 z u, hu, hz]
  field_simp

theorem restTSOp_of (hX : RestTSX) (hOp : RestOpF) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestTSOp D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, hC1, h⟩ := hOp
  refine ⟨C₁, hC1, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  exact tsOpAt_of hSet.1 hX r TT (dT TT lam0) _ _ (topW_dom TT hdom) c0 Θ
    (h C hC p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H hm hhm Θ hΘ)

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfTwo
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det kp_lamAt_antitone)

section Tensor

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem tensor_onto (A B M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (hM : ∀ s, M s ≤ Submodule.span R {X | ∃ F ∈ A s, ∃ G ∈ B s, X = F * G}) :
    tensorLat R K M ≤ Submodule.span R {X | ∃ P ∈ tensorLat R K A, ∃ Q ∈ tensorLat R K B, X = P * Q} :=
  _root_.UpperTheory.Reformulated.B.product_first_partition.tensor_onto A B M hM

end Tensor

theorem ontoAll : OntoAll := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r d rest lam hlam hdr e he z hz
  have hw := w_ne_zero h
  have := h.frac_O
  have hfd : IsDominant (flW (m := m) d) := flW_dom _
  have hAr : Ar r lam = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam]; exact Ar_add r _ _
  obtain ⟨gs, hgs, _, h2, _⟩ := Formalism.L2.G.Model.edgeLat h m r e he
  have hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
      LeAt p ι σ w s.val e = colSpan O g := fun s =>
    ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩
  set cw : Kf := algebraMap O Kf w with hcw
  set Sp := Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e,
    ∃ β ∈ Re p ι σ w r rest e, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)} with hSp
  obtain ⟨z0, hz0, rfl⟩ := mem_scale.1 hz
  have hz0' : ((z0 : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O lam (fun s => LeAt p ι σ w s.val e) := hz0
  have hten := tensor_onto (R := O) (fun s => H0 O m (lamAt (flW (m := m) d) s) (LeAt p ι σ w s.val e))
    (fun s => H0 O m (lamAt rest s) (LeAt p ι σ w s.val e)) (fun s => H0 O m (lamAt lam s) (LeAt p ι σ w s.val e))
    (fun s => by
      rw [hlam, lamAt_add]
      exact le_of_eq (Formalism.L2.G.Model.cartanOnto_proved O Kf m _ _ _ (hΛ s) (kp_lamAt_antitone _ hfd s)
        (kp_lamAt_antitone _ hdr s))) hz0'
  have key : ∀ x ∈ Submodule.span O {X | ∃ P ∈ Hten O (flW (m := m) d) (fun s => LeAt p ι σ w s.val e),
      ∃ Q ∈ Hten O rest (fun s => LeAt p ι σ w s.val e), X = P * Q},
      ∃ hx : x ∈ Vsp Kf lam, cw ^ (-Ar r lam) • (⟨x, hx⟩ : Vsp Kf lam) ∈ Sp := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, hP, Q, hQ, rfl⟩ := hx
      have hPV := Hten_le_V hfd _ hΛ P hP
      have hQV := Hten_le_V hdr _ hΛ Q hQ
      refine ⟨V_mul Kf hlam hfd hdr hPV hQV, Submodule.subset_span
        ⟨cw ^ (-Ar r (flW (m := m) d)) • ⟨P, hPV⟩, mem_scale.2 ⟨⟨P, hPV⟩, hP, rfl⟩,
          cw ^ (-Ar r rest) • ⟨Q, hQV⟩, mem_scale.2 ⟨⟨Q, hQV⟩, hQ, rfl⟩, ?_⟩⟩
      simp only [Submodule.coe_smul]
      rw [smul_mul_smul_comm, ← zpow_add₀ hw, hAr]
      congr 2
      ring
    | zero => exact ⟨Submodule.zero_mem _, by
        have : (⟨0, Submodule.zero_mem _⟩ : Vsp Kf lam) = 0 := rfl
        rw [this, smul_zero]; exact Submodule.zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      refine ⟨Submodule.add_mem _ ha1 hb1, ?_⟩
      have : (⟨a + b, Submodule.add_mem _ ha1 hb1⟩ : Vsp Kf lam) = ⟨a, ha1⟩ + ⟨b, hb1⟩ := rfl
      rw [this, smul_add]
      exact Submodule.add_mem _ ha2 hb2
    | smul t a _ ha =>
      obtain ⟨ha1, ha2⟩ := ha
      have hta : t • a ∈ Vsp Kf lam := by
        rw [← algebraMap_smul Kf t a]
        exact Submodule.smul_mem _ _ ha1
      refine ⟨hta, ?_⟩
      have : (⟨t • a, hta⟩ : Vsp Kf lam) = t • ⟨a, ha1⟩ := rfl
      rw [this, smul_comm]
      exact Submodule.smul_mem _ _ ha2
  obtain ⟨hx, hmem⟩ := key _ hten
  exact hmem

theorem restCloudB_of_two (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hop : RestTSOp D CLa Ck Crk Cdeg) (hsz : RestSize) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_three D CLa Ck Crk Cdeg hop hsz ontoAll

end Formalism.MainNotions.TestSideCounting
end
end

