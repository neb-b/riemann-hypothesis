module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetTwistedQuotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.DerivQuot

section Mat

variable (k : Type) [Field k]

noncomputable def eIter (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (eIter n j)

theorem glEmbMat_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) k) (a b : Fin (m + 1)) :
    glEmbMat k m A a b = if h : (a : ℕ) < m ∧ (b : ℕ) < m then A ⟨a, h.1⟩ ⟨b, h.2⟩
      else if (a : ℕ) = b then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast b =>
      have hb := b.isLt
      simp [glEmbMat, hb.ne']
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      have ha := a.isLt
      simp [glEmbMat, ha.ne]
    | cast b => simp [glEmbMat]

theorem eIter_apply (n : ℕ) : ∀ (j : ℕ) (g : GL (Fin n) k) (a b : Fin (n + j + 1)),
    (((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b =
      if h : (a : ℕ) < n ∧ (b : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨a, h.1⟩ ⟨b, h.2⟩
        else if (a : ℕ) = b then 1 else 0
  | 0, g, a, b => glEmbMat_apply k n _ a b
  | j + 1, g, a, b => by
    have e : (((eIter k n (j + 1) g : Mir k (n + (j + 1))) : GL (Fin (n + (j + 1) + 1)) k) :
        Matrix (Fin (n + (j + 1) + 1)) (Fin (n + (j + 1) + 1)) k) a b =
        glEmbMat k (n + j + 1) (((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
          Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b := rfl
    rw [e, glEmbMat_apply]
    by_cases h : (a : ℕ) < n + j + 1 ∧ (b : ℕ) < n + j + 1
    · rw [dite_eq_left h, eIter_apply n j g]
    · rw [dite_eq_right h]
      have h' : ¬ ((a : ℕ) < n ∧ (b : ℕ) < n) := fun h2 => h ⟨by omega, by omega⟩
      rw [dite_eq_right h']

theorem eIter_eq_leviEmb (n j : ℕ) (hd : ∑ a, (![n, j + 1] a) = n + j + 1) (g : GL (Fin n) k) :
    ((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g) := by
  set e := stdBlocks ![n, j + 1] hd with he
  have h0 : ∀ i : Fin n, (e ⟨0, i⟩ : ℕ) = i := fun i => by
    have := stdBlocks_val ![n, j + 1] hd 0 i
    simpa using this
  have h1 : ∀ i : Fin (j + 1), (e ⟨1, i⟩ : ℕ) = n + i := fun i => by
    have := stdBlocks_val ![n, j + 1] hd 1 i
    simpa using this
  have hsplit₀ : ∀ (a : Fin 2) (i : Fin (![n, j + 1] a)), (∃ l : Fin n, e ⟨a, i⟩ = e ⟨0, l⟩) ∨
      (∃ l : Fin (j + 1), e ⟨a, i⟩ = e ⟨1, l⟩) :=
    Fin.forall_fin_two.2 ⟨fun i => Or.inl ⟨i, rfl⟩, fun i => Or.inr ⟨i, rfl⟩⟩
  have hsplit : ∀ x : Fin (n + j + 1), (∃ i : Fin n, x = e ⟨0, i⟩) ∨ (∃ i : Fin (j + 1), x = e ⟨1, i⟩) := by
    intro x
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    exact hsplit₀ a i
  have hv0 : ∀ (i : Fin n) (h : (e ⟨0, i⟩ : ℕ) < n), (⟨(e ⟨0, i⟩ : ℕ), h⟩ : Fin n) = i := fun i _ => Fin.ext (h0 i)
  apply Units.ext
  ext x y
  rw [eIter_apply]
  rcases hsplit x with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hsplit y with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hi := i.isLt
    have hl := l.isLt
    rw [dite_eq_left ⟨by rw [h0]; exact hi, by rw [h0]; exact hl⟩]
    have := leviEmb_apply_same k e (firstEmb ![n, j + 1] g) 0 i l
    rw [this]
    have h2 : (firstEmb ![n, j + 1] g) 0 = g := by
      show (Pi.mulSingle (0 : Fin 2) g : ∀ a, GL (Fin (![n, j + 1] a)) k) 0 = g
      exact Pi.mulSingle_eq_same _ _
    rw [h2, hv0, hv0]
  · have hi := i.isLt
    rw [dite_eq_right (fun h => by have := h.2; rw [h1] at this; omega), ite_eq_right (by rw [h0, h1]; omega)]
    exact (leviEmb_apply_ne k e _ (a := 0) (b := 1) (by decide) i l).symm
  · have hl := l.isLt
    rw [dite_eq_right (fun h => by have := h.1; rw [h1] at this; omega), ite_eq_right (by rw [h0, h1]; omega)]
    exact (leviEmb_apply_ne k e _ (a := 1) (b := 0) (by decide) i l).symm
  · rw [dite_eq_right (fun h => by have := h.1; rw [h1] at this; omega)]
    have := leviEmb_apply_same k e (firstEmb ![n, j + 1] g) 1 i l
    rw [this]
    have h3 : (firstEmb ![n, j + 1] g) 1 = 1 := by
      show (Pi.mulSingle (0 : Fin 2) g : ∀ a, GL (Fin (![n, j + 1] a)) k) 1 = 1
      exact Pi.mulSingle_eq_of_ne (by decide) _
    rw [h3, h1, h1]
    by_cases hil : i = l
    · subst hil
      exact (ite_eq_left rfl).trans (Matrix.one_apply_eq i).symm
    · have : ¬ (n + (i : ℕ) = n + l) := fun h => hil (Fin.ext (by omega))
      rw [ite_eq_right this]
      exact (Matrix.one_apply_ne hil).symm

end Mat

section Quot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comap_twKer_phiMinus (ψ : AddChar k Circle) {m n : ℕ} (hnm : n ≤ m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (m + 1)) V) :
    (twKer (phiMinus k ψ τ) (derUnipM k m n) (derCharM k ψ m n)).comap
        (twKer τ (MirUin k (m + 1)) (mirChar k ψ m)).mkQ =
      twKer τ (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n) := by
  have twKer_eq_map {G M W : Type} [Group G] [Group M] [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ G W) (N₁ : Subgroup G) (θ₁ : N₁ →* ℂˣ) (s : M →* G)
      (hs : ∀ (m : M) (n : N₁), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N₁, θ₁ ⟨_, h⟩ = θ₁ n)
      (N₂ : Subgroup M) (θ₂ : N₂ →* ℂˣ) (N : Subgroup G) (θ : N →* ℂˣ)
      (h1 : ∀ u : N₁, ∃ h : (u : G) ∈ N, θ ⟨u, h⟩ = θ₁ u)
      (h2 : ∀ a : N₂, ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a)
      (h3 : ∀ u : N, ∃ u₁ : N₁, ∃ a : N₂, (u : G) = u₁ * s a) :
      twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂ = (twKer ρ N θ).map (twKer ρ N₁ θ₁).mkQ ∧
        twKer ρ N₁ θ₁ ≤ twKer ρ N θ := by
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · refine Submodule.span_le.2 ?_
      rintro w ⟨a, x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        obtain ⟨h, hθ⟩ := h2 a
        refine ⟨ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨⟨_, h⟩, v, rfl⟩, ?_⟩
        rw [hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        rfl
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨u₁, a, hu⟩ := h3 u
      obtain ⟨hu₁, e1⟩ := h1 u₁
      obtain ⟨ha, e2⟩ := h2 a
      have hθ : θ u = θ₁ u₁ * θ₂ a := by
        have : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
        rw [this, map_mul, e1, e2]
      have hdec : ρ (u : G) v - ((θ u : ℂˣ) : ℂ) • v =
          (ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v) +
            ((θ₁ u₁ : ℂˣ) : ℂ) • (ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v) := by
        rw [hθ, hu, map_mul, mul_apply_eq_comp, Units.val_mul, smul_sub, mul_smul]
        abel
      have hz : ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v ∈ twKer ρ N₁ θ₁ :=
        Submodule.subset_span ⟨u₁, _, rfl⟩
      show (twKer ρ N₁ θ₁).mkQ _ ∈ twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂
      rw [hdec, map_add (f := _), Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      rfl
    · refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨h, hθ⟩ := h1 u
      exact Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩
  obtain ⟨e, hle⟩ := twKer_eq_map τ (MirUin k (m + 1)) (mirChar k ψ m) _ (levi_stab ψ m)
    (derUnipM k m n) (derCharM k ψ m n) (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n)
    (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
    (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
  show (twKer (twAct τ (MirUin k (m + 1)) (mirChar k ψ m) _ (levi_stab ψ m)) (derUnipM k m n)
    (derCharM k ψ m n)).comap _ = _
  rw [e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

theorem ker_comp_mkQ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (K : Submodule ℂ V)
    (L : Submodule ℂ (V ⧸ K)) (q : (V ⧸ K) →ₗ[ℂ] W) (h : LinearMap.ker q = L) :
    LinearMap.ker (q ∘ₗ K.mkQ) = L.comap K.mkQ := by
  rw [LinearMap.ker_comp, h]

theorem exists_quotM (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ (g : GL (Fin n) k) (v : τ.V), q (τ.ρ (eIter k n j g) v) = derivM k ψ j τ g (q v) := by
  intro j
  induction j with
  | zero =>
    intro τ
    exact ⟨(twKer τ.ρ (MirUin k n) 1).mkQ, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n _ τ.ρ), fun g v => rfl⟩
  | succ j ih =>
    intro τ
    obtain ⟨q₁, hs, hk, he⟩ := ih (MRep.phiM k ψ τ)
    refine ⟨q₁ ∘ₗ (twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ,
      hs.comp (Submodule.mkQ_surjective _), ?_, fun g v => he g (Submodule.Quotient.mk v)⟩
    exact (ker_comp_mkQ _ _ q₁ hk).trans (comap_twKer_phiMinus ψ (Nat.le_add_right n j) τ.ρ)

theorem exists_deriv_quot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    ∃ q : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) ∧
      ∀ (g : GL (Fin n) k) (v : V), q (π (leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g)) v) =
        GlobalTheory.BZMir.deriv k ψ j π g (q v) := by
  intro k _ _ _ _ ψ n j V _ _ π hd
  obtain ⟨q, hs, hk, he⟩ := exists_quotM ψ n j (resM k π)
  refine ⟨q, hs, hk.trans (GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (n + j) n V π), fun g v => ?_⟩
  rw [← eIter_eq_leviEmb k n j hd g]
  exact he g v

end Quot

end GlobalTheory.CompanionTheory.DerivQuot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIso
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Norm

section Generic

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def twistEquivOf {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twist ρ χ).Equiv (twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • σ g (φ.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (φ.isIntertwining' g) v)

def pairT (a : V) (y : W) : ∀ x : Bool, TwoT V W x
  | false => a
  | true => y

theorem bool_tprod_pairT (a : V) (y : W) :
    Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ (pairT a y)) = (a ⊗ₜ[ℂ] y : V ⊗[ℂ] W) :=
  Exponents.boolTensorEquiv_tprod _

theorem tprod_pairT_smul (a : V) (c d : ℂ) (y : W) :
    PiTensorProduct.tprod ℂ (pairT (c • a) (d • y)) = (c * d) • PiTensorProduct.tprod ℂ (pairT a y) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V W)).injective
  rw [map_smul, bool_tprod_pairT, bool_tprod_pairT]
  exact TensorProduct.smul_tmul_smul c d a y

end Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Chars

theorem det_levi' (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  exact GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _

theorem det_unip' (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
  ext
  show (1 + colMat k n v.toAdd : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [colMat]
    · simp [colMat, hi]
  · intro a b hab
    have hb : b ≠ Fin.last n := fun h => by
      subst h
      exact absurd (Fin.le_last a) (not_le.2 hab)
    have hne : a ≠ b := fun h => by
      subst h
      exact lt_irrefl _ hab
    simp [colMat, hb, Matrix.one_apply, hne]

theorem dpowM_levi' (n : ℕ) (s : ℝ) (g : GL (Fin n) k) : dpowM n s (levi k n g) = dpow n s g := by
  show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _
  rw [det_levi']

theorem dpowM_of_mem' (n : ℕ) (s : ℝ) (u : Mir k n) (hu : u ∈ MirUin k n) : dpowM n s u = 1 := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1
  have hv' : (u : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv', det_unip', map_one]

theorem scalar_sum (i t : ℕ) (a b : kˣ) :
    absPow k ((-1 / 2 : ℝ) : ℂ) (a * b) * (absPow k 1 b * (absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) a *
        absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) b)) =
      absPow k ((t : ℂ) / 2) a * absPow k (-(i : ℂ) / 2) b * absPow k ((-1 / 2 : ℝ) : ℂ) a := by
  have e0 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by
    rw [← absPow_add]
    congr 1
    ring
  have e1 : absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k (-(i : ℂ) / 2) * (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg, ← absPow_add]
    congr 1
    push_cast
    ring
  have e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg]
    congr 1
    push_cast
    ring
  have e3 : absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k ((t : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  rw [e0, e1, e2, e3]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]
  generalize absPow k (1 / 2) a = A
  generalize absPow k (1 / 2) b = B
  generalize absPow k ((t : ℂ) / 2) a = T
  generalize absPow k (-(i : ℂ) / 2) b = R
  calc A⁻¹ * B⁻¹ * (B * B * (T * (R * B⁻¹))) = (B⁻¹ * B) * (B * B⁻¹) * (T * R * A⁻¹) := by ac_rfl
    _ = T * R * A⁻¹ := by rw [inv_mul_cancel, mul_inv_cancel, one_mul, one_mul]

theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem twKer_twist_dpowM {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (τ : Representation ℂ (Mir k n) V) (s : ℝ) :
    twKer (twist τ (dpowM n s)) (MirUin k n) 1 = twKer τ (MirUin k n) 1 := by
  unfold twKer
  congr 1
  ext w
  refine exists_congr fun u => exists_congr fun v => ?_
  have hu : dpowM n s (u : Mir k n) = 1 := dpowM_of_mem' n s u.1 u.2
  rw [twist_apply, hu, Units.val_one, one_smul]

end Chars

section Main

variable {i t : ℕ} (τ : MRep k i) (σ : GRep k t)

abbrev eIT (i t : ℕ) : (Σ x, Two (Fin i) (Fin t) x) ≃ Fin (i + t) := two (stdSum (rfl : i + t = i + t))

abbrev sigT : Representation ℂ (Qp k i t) (PiTensorProduct ℂ (TwoT (psiN τ).V σ.V)) :=
  (twist (piTensor (twoRep (psiN τ).ρ σ.ρ)) (deltaHalf k (Two (Fin i) (Fin t)))).comp (leviProj k (eIT i t))

abbrev mkT (s : ℝ) : τ.V →ₗ[ℂ] Jacquet (mtw τ s).ρ (MirUin k i) := (twKer (mtw τ s).ρ (MirUin k i) 1).mkQ

abbrev mkY : τ.V →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k i) 1).mkQ

def Lq (s : ℝ) : (Jacquet (mtw τ s).ρ (MirUin k i) ⊗[ℂ] σ.V) ≃ₗ[ℂ] PiTensorProduct ℂ (TwoT (psiN τ).V σ.V) :=
  (TensorProduct.congr (Submodule.quotEquivOfEq _ _ (twKer_twist_dpowM i τ.ρ s)) (LinearEquiv.refl ℂ σ.V)).trans
    (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).symm

theorem Lq_tmul (s : ℝ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s y ⊗ₜ[ℂ] w) = PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).injective
  rw [bool_tprod_pairT]
  refine (LinearEquiv.apply_symm_apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)) _).trans ?_
  rfl

theorem qRep_tmul (s₁ s₂ : ℝ) (q : Qp k i t) (y : τ.V) (w : σ.V) :
    qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) •
        (mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V)) := by
  have h : extTensor (psiMinus k (mtw τ s₁).ρ) (σ.tw s₂).ρ (qBlocks k i t q) (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V) := by
    refine (extTensor_tmul _ _ _ _ _).trans ?_
    show mkT τ s₁ (((dpowM i s₁ (levi k i (qBlocks k i t q).1) : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ] _ = _
    rw [dpowM_levi']
    rfl
  exact congrArg (fun z => ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) • z) h

theorem Lq_tmul_smul (s : ℝ) (c d : ℂ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s (c • y) ⊗ₜ[ℂ] (d • w : σ.V)) = (c * d) • PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  rw [Lq_tmul, map_smul, tprod_pairT_smul]

theorem scalar_q (i t : ℕ) (q : Qp k i t) :
    ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) *
        (((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) *
          (((dpow i (((t : ℕ) : ℝ) / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) *
            ((dpow t (-((i + 1 : ℕ) : ℝ) / 2) (qBlocks k i t q).2 : ℂˣ) : ℂ))) =
      ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) *
        ((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) := by
  have hlev : leviProj k (eIT i t) q = leviTwo k (Fin i) (Fin t) (qBlocks k i t q) := by
    funext x
    cases x
    · rfl
    · rfl
  have hdet : GeneralLinearGroup.det (q : GL (Fin (i + t)) k) =
      GeneralLinearGroup.det (qBlocks k i t q).1 * GeneralLinearGroup.det (qBlocks k i t q).2 := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
    rfl
  rw [hlev, deltaHalf_two]
  simp only [← Units.val_mul]
  congr 1
  have := scalar_sum (k := k) i t (GeneralLinearGroup.det (qBlocks k i t q).1)
    (GeneralLinearGroup.det (qBlocks k i t q).2)
  simp only [dpow, detChar_apply, hdet, Fintype.card_fin]
  exact this

def qEnd (s₁ s₂ : ℝ) (q : Qp k i t) :
    (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) →ₗ[ℂ] (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) :=
  qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q

theorem sigT_Lq (q : Qp k i t) (v : Jacquet (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (MirUin k i) ⊗[ℂ] σ.V) :
    sigT τ σ q (Lq τ σ (((t : ℕ) : ℝ) / 2) v) =
      ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) •
        Lq τ σ (((t : ℕ) : ℝ) / 2) (qEnd τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul x w =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h2 : (fun x => twoRep (psiN τ).ρ σ.ρ x (leviProj k (eIT i t) q x) (pairT (mkY τ y) w x)) =
        pairT (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y))
          ((1 : ℂ) • σ.ρ (qBlocks k i t q).2 w) := by
      funext x
      cases x
      · rfl
      · exact (one_smul ℂ _).symm
    have hL : sigT τ σ q (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) =
        ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
          (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) * 1) •
            PiTensorProduct.tprod ℂ (pairT (mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y)) (σ.ρ (qBlocks k i t q).2 w)) := by
      show ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
        piTensor (twoRep (psiN τ).ρ σ.ρ) (leviProj k (eIT i t) q) (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) = _
      rw [piTensor_tprod]
      exact congrArg _ ((congrArg (PiTensorProduct.tprod ℂ) h2).trans (tprod_pairT_smul _ _ _ _))
    have hR := qRep_tmul τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q y w
    refine (congrArg (sigT τ σ q) (Lq_tmul τ σ _ y w)).trans (hL.trans ?_)
    refine Eq.trans ?_ (congrArg (fun z => ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) z) hR.symm)
    show _ = ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) (_ • _)
    rw [map_smul, Lq_tmul_smul, smul_smul, smul_smul, smul_smul, mul_one]
    congr 1
    rw [← scalar_q i t q]
    ring

end Main

theorem psiN_prodPGn_of_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  intro k _ _ _ _ i t τ σ _ _ hE
  obtain ⟨E⟩ := hE
  exact ⟨(twistEquivOf E (dpow (i + t) (-1 / 2))).trans
    (GlobalTheory.LocGL.smIndTwistEquiv le_rfl le_rfl (isSmoothChar_dpow _ _) (Lq τ σ _) fun q v => sigT_Lq τ σ q v)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Norm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedesStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL (k := k)) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  first | exact @GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | exact GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | (intros; apply GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureOpenNonemptyNeZero
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem muD_toReal_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (E C : Set (Fin t → k)) (hE : IsOpen E) (hn : E.Nonempty) (hC : IsCompact C) (hEC : E ⊆ C),
    (muD (k := k) t E).toReal ≠ 0 := by
  intro k _ _ _ _ t E C hE hn hC hEC
  unfold muD
  rw [ENNReal.toReal_ne_zero]
  exact ⟨(hE.measure_pos _ hn).ne',
    ((MeasureTheory.measure_mono hEC).trans_lt hC.measure_lt_top).ne⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
end

