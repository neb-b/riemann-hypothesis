module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpen
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HBBump

theorem exists_bump : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G),
    IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) →
    ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧
      ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  intro G Z _ _ _ _ _ H ρ B hBo hBc z hz
  classical

  have hwell : ∀ (h h' : H) (β β' : G), β ∈ B → β' ∈ B → (h : G) * β = (h' : G) * β' →
      ρ h z = ρ h' z := by
    intro h h' β β' hβ hβ' e
    have ha : ((h'⁻¹ * h : H) : G) ∈ B := by
      have : ((h'⁻¹ * h : H) : G) = β' * β⁻¹ := by
        push_cast
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
        group
      rw [this]
      exact B.mul_mem hβ' (B.inv_mem hβ)
    have h1 := hz _ ha
    have h2 : h = h' * (h'⁻¹ * h) := by group
    rw [h2, map_mul, Module.End.mul_apply, h1]
  let P : G → Prop := fun p => ∃ h : H, ∃ β ∈ B, p = (h : G) * β
  let f : G → Z := fun p => if hp : P p then ρ hp.choose z else 0
  have hval : ∀ (h : H) (β : G), β ∈ B → f ((h : G) * β) = ρ h z := by
    intro h β hβ
    have hp : P ((h : G) * β) := ⟨h, β, hβ, rfl⟩
    obtain ⟨β', hβ', e⟩ := hp.choose_spec
    simp only [f, dif_pos hp]
    exact hwell _ _ _ _ hβ' hβ e.symm
  have hzero : ∀ p, ¬ P p → f p = 0 := fun p hp => by simp only [f, dif_neg hp]
  have hleft : ∀ (h : H) (g : G), f ((h : G) * g) = ρ h (f g) := by
    intro h g
    by_cases hg : P g
    · obtain ⟨h', β, hβ, rfl⟩ := hg
      have : (h : G) * ((h' : G) * β) = ((h * h' : H) : G) * β := by push_cast; group
      rw [this, hval _ _ hβ, hval _ _ hβ, map_mul, Module.End.mul_apply]
    · have hn : ¬ P ((h : G) * g) := by
        rintro ⟨h', β, hβ, e⟩
        refine hg ⟨h⁻¹ * h', β, hβ, ?_⟩
        push_cast
        rw [mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hg, map_zero]
  have hright : ∀ (p : G), ∀ x ∈ B, f (p * x) = f p := by
    intro p x hx
    by_cases hp : P p
    · obtain ⟨h, β, hβ, rfl⟩ := hp
      rw [mul_assoc, hval _ _ (B.mul_mem hβ hx), hval _ _ hβ]
    · have hn : ¬ P (p * x) := by
        rintro ⟨h, β, hβ, e⟩
        refine hp ⟨h, β * x⁻¹, B.mul_mem hβ (B.inv_mem hx), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hzero _ hn, hzero _ hp]
  let F : indSpace H ρ := ⟨f, hleft⟩
  have hsm : F ∈ smoothPart (ind H ρ) := by
    let T : Subgroup G :=
      { carrier := {g | ind H ρ g F = F}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hBT : (B : Set G) ⊆ T := by
      intro x hx
      show ind H ρ x F = F
      apply Subtype.ext
      funext p
      exact hright p x hx
    exact T.isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset (hBo.mem_nhds B.one_mem) hBT)
  refine ⟨⟨⟨F, hsm⟩, ⟨(B : Set G), hBc, ?_⟩⟩, hval, hzero⟩
  intro g hg
  by_contra hc
  refine hg (hzero g ?_)
  rintro ⟨h, β, hβ, e⟩
  exact hc ⟨h, h.2, β, hβ, e⟩

end GlobalTheory.CompanionTheory.HBBump
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntertwinerOfEquiv
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSeq

section Alg

variable {k : Type} [Field k]

theorem mul_colMat_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (v : Fin n → k) :
    (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * colMat k n v =
      colMat k n ((blockMat k n (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec v) := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last =>
      have e : ∀ l : Fin n, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc l) = 0 := by
        intro l
        rw [hl]
        simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
      simp [colMat, Matrix.mul_apply, Fin.sum_univ_castSucc, e]
    | cast i =>
      simp [colMat, Matrix.mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct, blockMat]
  · simp [colMat, Matrix.mul_apply, hj]

theorem colMat_mul_of_mem {n : ℕ} (h : GL (Fin (n + 1)) k) (hh : h ∈ Mir k n) (w : Fin n → k) :
    colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = colMat k n w := by
  have hl := (mem_Mir_iff k h).1 hh
  ext i j
  have e : (colMat k n w * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) i j =
      colMat k n w i (Fin.last n) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
    · intro l _ hlne
      simp [colMat, hlne]
    · simp
  rw [e, hl]
  by_cases hj : j = Fin.last n
  · subst hj
    simp [colMat, eLast]
  · simp [colMat, eLast, hj]

theorem conj_mem_MirUin {n : ℕ} (h : Mir k n) (u : MirUin k n) : h * (u : Mir k n) * h⁻¹ ∈ MirUin k n := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hv' : ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  show (h : GL (Fin (n + 1)) k) * ((u : Mir k n) : GL (Fin (n + 1)) k) * (h : GL (Fin (n + 1)) k)⁻¹ ∈ MirU k n
  rw [hv']
  refine ⟨Multiplicative.ofAdd ((blockMat k n ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)).mulVec
    v.toAdd), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext1
  rw [Units.val_mul, Units.val_mul]
  show (1 + colMat k n _) * _ = _ * (1 + colMat k n v.toAdd)
  rw [add_mul, mul_add, one_mul, mul_one, colMat_mul_of_mem _ h.2, mul_colMat_of_mem _ h.2]
  simp

end Alg

section Seq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Beta

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle) {n : ℕ}
  (τ : Representation ℂ (Mir k (n + 1)) V)

end Beta

variable (hI : BetaInd k) (hS : BetaSmooth k) (hC : BetaCompact k)


end Seq

end GlobalTheory.CompanionTheory.BZMirSeq

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMirDer.NonZero

section Alg

variable {k : Type} [Field k]

theorem mir_zero_eq_one (g : Mir k 0) : g = 1 := by
  have h := (mem_Mir_iff k (g : GL (Fin 1) k)).1 g.2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
  have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
  subst hi
  subst hj
  have := congrFun h (Fin.last 0)
  simpa [eLast] using this

end Alg

theorem twKer_eq_bot_of_forall_eq_one {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (hN : ∀ n : N, n = 1) :
    twKer ρ N θ = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  rw [hN n]
  simp

theorem nontrivial_quot_of_not_mem {V : Type} [AddCommGroup V] [Module ℂ V] (p : Submodule ℂ V) (v : V)
    (hv : v ∉ p) : Nontrivial (V ⧸ p) :=
  nontrivial_of_ne (Submodule.Quotient.mk v) 0 (by rwa [Ne, Submodule.Quotient.mk_eq_zero])

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmb (n : ℕ) : Continuous (glEmb k n) := by
  apply Continuous.units_map
  show Continuous (glEmbMat k n)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases <;> simp [glEmbMat] <;>
      first | exact continuous_const | exact (continuous_apply _).comp (continuous_apply _) | fun_prop
  | cast i => induction j using Fin.lastCases <;> simp [glEmbMat] <;>
      first | exact continuous_const | exact (continuous_apply _).comp (continuous_apply _) | fun_prop

theorem continuous_levi_comp_subtype (m : ℕ) : Continuous ((levi k (m + 1)).comp (Mir k m).subtype) :=
  continuous_induced_rng.2 ((continuous_glEmb (m + 1)).comp continuous_subtype_val)

end Top

theorem exists_derivative_nontrivial (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ψ ≠ 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V),
      IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ τ _ hV
    refine ⟨0, le_rfl, ?_⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply nontrivial_quot_of_not_mem _ v
    rw [twKer_eq_bot_of_forall_eq_one τ _ _ (fun n => Subtype.ext (mir_zero_eq_one _))]
    exact hv
  | succ m ih =>
    intro V _ _ τ hτ hV
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    by_cases h1 : v ∈ twKer τ (MirUin k (m + 1)) 1
    · have hex : ∃ g : GL (Fin (m + 1)) k,
          τ (levi k (m + 1) g) v ∉ twKer τ (MirUin k (m + 1)) (mirChar k ψ m) := by
        by_contra hcon
        push_neg at hcon
        exact hv (_root_.GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer k ψ hψc hψ m V τ hτ v h1 hcon)
      obtain ⟨g, hg⟩ := hex
      haveI := nontrivial_quot_of_not_mem _ _ hg
      have hs : IsSmooth (phiMinus k ψ τ) :=
        GlobalTheory.T.twisted_action_smooth τ hτ _ _ _ (continuous_levi_comp_subtype m) (levi_stab ψ m)
      obtain ⟨n, hn, hnt⟩ := ih _ (phiMinus k ψ τ) hs inferInstance
      obtain ⟨e⟩ := _root_.GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv k ψ m n hn V τ
      exact ⟨n, hn.trans (Nat.le_succ m), e.injective.nontrivial⟩
    · refine ⟨m + 1, le_rfl, ?_⟩
      apply nontrivial_quot_of_not_mem _ v
      rwa [← _root_.GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ (m + 1) V τ]

end GlobalTheory.CompanionTheory.BZMirDer.NonZero

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.TranslAdele

theorem thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  ext i j
  change σ (σ (g.val i j)) = g.val i j
  exact hσ _

theorem exists_scalar_of_central {K : Type} [Field K] {n : ℕ} (z : GL (Fin n) K)
    (hz : ∀ h : GL (Fin n) K, z * h = h * z) : ∃ c : K, z.val = Matrix.scalar (Fin n) c := by
  have : z.val ∈ Set.range (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    have h := hz ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩
    have h' := congrArg Units.val h
    exact h'.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

theorem Phi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map f = GlobalTheory.Tw.Phi n S := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem translAd : TranslAd := by
  intro E _ _ _ n u hu g

  have hz : ∀ h : GL (Fin n) E, ((PhiU n E)⁻¹ * u) * h = h * ((PhiU n E)⁻¹ * u) := by
    intro h
    have hinv : thetaE E n (thetaE E n h) = h :=
      thetaR_thetaR (conjE E) (fun x => IsCMField.complexConj_apply_apply E x) n h
    have h1 := hu.1 (thetaE E n h)
    rw [hinv] at h1
    have h2 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
      have := thetaGL_eq n E (IsCMField.complexConj E).toRingEquiv.toRingHom (thetaE E n h)
      rw [show thetaR (IsCMField.complexConj E).toRingEquiv.toRingHom n (thetaE E n h) = h from hinv] at this
      exact this
    rw [h2] at h1
    have h3 : h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * u * h := by
      have h4 : PhiU n E * h * (PhiU n E)⁻¹ * u = u * h := by rw [h1]; group
      calc h * (PhiU n E)⁻¹ * u = (PhiU n E)⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹ * u) := by group
        _ = (PhiU n E)⁻¹ * u * h := by rw [h4]; group
    rw [← h3, mul_assoc h]
  obtain ⟨c, hc⟩ := exists_scalar_of_central _ hz

  set w : GA E n := ratGL E n ((PhiU n E)⁻¹ * u) with hw
  have hwc : ∀ t : GA E n, w * t = t * w := by
    intro t
    apply Units.ext
    have hval : w.val = Matrix.scalar (Fin n) (algebraMap E (Ad E) c) := by
      have : w.val = (((PhiU n E)⁻¹ * u : GL (Fin n) E).val).map (algebraMap E (Ad E)) := rfl
      rw [this, hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [Units.val_mul, Units.val_mul, hval]
    exact Matrix.scalar_commute _ (fun r' => Commute.all _ _) _
  have hP : ratGL E n (PhiU n E) = PhiU n (Ad E) := by
    apply Units.ext
    rw [phiU_val, ← Phi_map (algebraMap E (Ad E)) n, ← phiU_val]
    rfl
  have hr : ratGL E n u = PhiU n (Ad E) * w := by
    rw [hw, map_mul, map_inv, hP, mul_inv_cancel_left]
  rw [thetaGL_eq, hr]
  have h5 : w * thetaA E n g * w⁻¹ = thetaA E n g := by rw [hwc]; group
  calc PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹
      = PhiU n (Ad E) * (w * thetaA E n g * w⁻¹) * (PhiU n (Ad E))⁻¹ := by rw [h5]
    _ = PhiU n (Ad E) * w * thetaA E n g * (PhiU n (Ad E) * w)⁻¹ := by group

end GlobalTheory.CompanionTheory.TranslAdele

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWittComplementFrame
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_coords {K : Type} [Field K] {n : ℕ} (S : Submodule K (Fin n → K)) (P : Matrix (Fin n) (Fin n) K)
    (hP : ∀ v, P *ᵥ v ∈ S) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K),
      (∀ w, Z *ᵥ w ∈ S) ∧ Z * C = P ∧ Function.Injective Z.mulVec := by
  classical
  let b := Module.finBasis K S
  let Z : Matrix (Fin n) (Fin (Module.finrank K S)) K := Matrix.of fun i k => (b k : Fin n → K) i
  have hZ : ∀ w, Z *ᵥ w = ((∑ k, w k • b k : S) : Fin n → K) := by
    intro w
    ext i
    simp [Z, Matrix.mulVec, dotProduct, mul_comm, Submodule.coe_sum, Finset.sum_apply]
  let L : (Fin n → K) →ₗ[K] S := P.mulVecLin.codRestrict S hP
  let c : (Fin n → K) →ₗ[K] (Fin (Module.finrank K S) → K) := b.equivFun.toLinearMap ∘ₗ L
  refine ⟨_, Z, LinearMap.toMatrix' c, fun w => by rw [hZ]; exact Subtype.property _, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, hZ]
    have : (∑ k, c v k • b k : S) = L v := b.sum_equivFun (L v)
    rw [this]
    rfl
  · intro w w' h
    rw [hZ, hZ] at h
    have h' := Subtype.coe_injective h
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h'
    exact b.equivFun.symm.injective h'

theorem exists_witt_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW
  have hc : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => sigma_sigma hσ _
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := hA ▸ hW.xx
  have hBY : B * Y = 0 := hB ▸ hW.yy
  have hAY : A * Y = 1 := hA ▸ hW.xy
  have hBX : B * X = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hc, hcc, Formalism.UG.cT_one, ← Matrix.mul_assoc] at h
    rw [hB, h]
  obtain ⟨P, hPd⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAP : A * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hBP : B * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX, hBY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hPX : P * X = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBX, hAX,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  have hPY : P * Y = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBY, hAY,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  obtain ⟨m, Z, C, hS, hZC, hinj⟩ := exists_coords
    (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) P (fun v => by
      refine ⟨?_, ?_⟩
      · simp [Matrix.mulVec_mulVec, hAP]
      · simp [Matrix.mulVec_mulVec, hBP])
  have hAZ : A * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).1
  have hBZ : B * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).2
  have hcan : ∀ {ι : Type} (M M' : Matrix (Fin m) ι E), Z * M = Z * M' → M = M' := by
    intro ι M M' h
    ext i j
    exact congrFun (hinj (a₁ := fun i => M i j) (a₂ := fun i => M' i j)
      (funext fun a => congrFun (congrFun h a) j)) i
  have hPZ : P * Z = Z := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBZ, hAZ,
      Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]
  have hCZ : C * Z = 1 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPZ, Matrix.mul_one])
  have hCX : C * X = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPX, Matrix.mul_zero])
  have hCY : C * Y = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPY, Matrix.mul_zero])
  refine ⟨m, Z, Matrix.fromRows B (Matrix.fromRows C A), hA ▸ hAZ, hB ▸ hBZ, ?_, ?_⟩
  · rw [frm, Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      hBX, hBZ, hBY, hCX, hAX, hCZ, hCY, hAZ, hAY]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  · rw [frm, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, hZC, hPd]
    abel

end GlobalTheory.CompanionTheory.CFin

end
end

