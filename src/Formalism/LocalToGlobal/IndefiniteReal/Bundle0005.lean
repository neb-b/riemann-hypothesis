module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.GlobalTheory.DivPassage

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelAmbTransfer
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.L2.GlobalTheoryTheory.DivPassage

theorem levelAmb_transfer
    {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {D0 D1 : ℕ}
    (A : LevelAmb K D0 D1) {G : Type} [Group G] [Fintype G] {T : A.S → Type}
    [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)]
    (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) (ρ : Representation K G (Fin A.Dg → K))
    (hτ : IsGood τ) (hM : M1 τ H₀ χ₀)
    (h0 : A.ep0.mulVecLin = epP H₀ χ₀ ρ) (h1 : A.ep1.mulVecLin = epP H χ ρ)
    (hs : ∀ s, (A.es s).mulVecLin = eS (τ s) ρ) (hn : ∀ s, A.nS s = nS (τ s) H χ)
    (hG : A.G = Fintype.card G) (hgood : eGood τ ρ = LinearMap.id)
    (hX : A.FramesG) (hL : Submodule.IsFullLattice K A.Rg) (hst : ∀ g : G, ∀ a ∈ A.Rg, ρ g a ∈ A.Rg)
    (hU : IsUnitaryRep (Pi.basisFun K (Fin A.Dg)) A.Xg ρ) :
    A.Ranks ∧ A.Deg0 ∧ A.Deg1 ∧ (A.latticeAtSharpLevel ≠ ⊥ → A.MaxT) := by
  have h15 := all_parts_transfer_holds
  have hlat : IsGLat ρ A.Rg := by
    have : Submodule.IsFullLattice K A.Rg := hL
    exact ⟨Submodule.IsLattice.fg K A.Rg, Submodule.IsFullLattice.span_eq_top, hst⟩
  have p := h15 K G A.S T τ H₀ χ₀ H χ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have q := h15 K G A.S T τ H₀ χ₀ H₀ χ₀ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have e0 : A.latticeAtBaseLevel = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h0]; rfl
  have e1 : A.latticeAtSharpLevel = cut A.Rg (epP H χ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h1]; rfl
  have es : ∀ s, A.Rs s = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s => by
    rw [← h0, ← hs, ← Matrix.mulVecLin_mul]; rfl
  unfold TransferLatticeConditions at p q
  dsimp only at p q
  simp only [← e0, ← e1, ← es, ← hn, ← hG] at p
  have hM' : ∀ s, nS (τ s) H₀ χ₀ = 1 := hM
  simp only [← e0, ← es, hM', one_mul] at q
  obtain ⟨⟨-, r1⟩, ⟨-, -, -, -, -, -, d0⟩, -, ⟨d1, -⟩, m⟩ := p
  have r0 := q.1.2
  have h85 : (8.5 : ℝ) = 17 / 2 := by norm_num
  rw [h85] at d1 m
  refine ⟨⟨r0, r1⟩, ?_, ?_, fun h => (m h).1⟩
  · unfold LevelAmb.Deg0
    rw [r0, Nat.cast_sum]
    exact sub_le_iff_le_add'.1 d0
  · unfold LevelAmb.Deg1
    rw [r1]
    have := (abs_le.1 d1).1
    exact sub_le_iff_le_add.2 (by
      have h2 := neg_le_sub_iff_le_add.1 this
      exact h2)

end Formalism.IndefR.LatticeTransfer
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
section
open Module
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.L2.Indef

theorem mem_range_adjoint_of_ker_stable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (Θ : E →ₗ[ℂ] F) (T T' : E →ₗ[ℂ] E) (hT' : T' = LinearMap.adjoint T)
    (hker : ∀ u, Θ u = 0 → Θ (T' u) = 0) {y : E} (hy : y ∈ LinearMap.range (LinearMap.adjoint Θ)) :
    T y ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (LinearMap.adjoint Θ)), Submodule.mem_orthogonal]
  intro v hv
  have hΘv : Θ v = 0 := by
    have h := (Submodule.mem_orthogonal _ _).1 hv (LinearMap.adjoint Θ (Θ v)) ⟨Θ v, rfl⟩
    rw [LinearMap.adjoint_inner_left] at h
    exact inner_self_eq_zero.1 h
  rw [← LinearMap.adjoint_inner_left, ← hT', LinearMap.adjoint_inner_right, hker v hΘv, inner_zero_left]

theorem semilin_comp_eq_constr {ι k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module ℂ W]
    {σ : k →+* ℂ} (b : Basis ι k V) (j : V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i))) (f : V →ₗ[k] V) (x : V) :
    j (f x) = (Basis.mk hli hsp).constr ℂ (fun i => j (f (b i))) (j x) := by
  have h := b.ext (f₁ := j.comp f)
    (f₂ := ((Basis.mk hli hsp).constr ℂ (fun i => j (f (b i)))).comp j) (fun i => by
      simp only [LinearMap.comp_apply]
      rw [show j (b i) = Basis.mk hli hsp i from (Basis.mk_apply hli hsp i).symm, Basis.constr_basis])
  exact LinearMap.congr_fun h x

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem jR_opR (hR : X.KFormR) (t : Bs.Tup) (i : A.OpR t) (x : A.FR t) :
    X.jR t (A.opR t i x) = X.opC t i (X.jR t x) := by
  unfold opC
  rw [dite_eq_left (hR t)]
  exact semilin_comp_eq_constr _ (X.jR t) (hR t).1 (hR t).2.ge (A.opR t i) x

theorem jL_opL (hL : X.KFormL) (j : Bs.J) (t : Bs.Tup) (i : A.OpL j t) (x : A.FL j t) :
    X.jL j t (A.opL j t i x) = X.opLC j t i (X.jL j t x) := by
  unfold opLC
  rw [dite_eq_left (hL j t)]
  exact semilin_comp_eq_constr _ (X.jL j t) (hL j t).1 (hL j t).2.ge (A.opL j t i) x

theorem cutStable : X.CutStable := by
  intro hR hL hkR hkL haR haL
  unfold DefSub.Stable
  refine ⟨fun t i => ?_, fun j t i => ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    show X.jR t (A.opR t i x) ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))
    rw [jR_opR X hR]
    obtain ⟨i', hi'⟩ := haR t i
    exact mem_range_adjoint_of_ker_stable (X.Θ t) (X.opC t i) (X.opC t i') hi'
      (fun u hu => hkR t i' u hu) (y := X.jR t x) hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    show X.jL j t (A.opL j t i x) ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t))
    rw [jL_opL X hL]
    obtain ⟨i', hi'⟩ := haL j t i
    exact mem_range_adjoint_of_ker_stable (X.θ' j t) (X.opLC j t i) (X.opLC j t i') hi'
      (fun u hu => hkL j t i' u hu) (y := X.jL j t x) hx

end CxData

end Formalism.IndefR.Cx
end
end

