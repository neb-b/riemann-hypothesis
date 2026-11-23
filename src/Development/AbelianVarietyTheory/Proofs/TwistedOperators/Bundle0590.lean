module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Subst

variable {D : D7}

def fockSubAll {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
      else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)

end Subst

section Points

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def ptTop (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : GA D (G.V (.top n)) :=
  if h : n < D.R.m then (kappa W g).1 ⟨n, h⟩ else if h' : n = D.R.m then h' ▸ kappaTop W g else 1

def ptGrid (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : GA D (G.V (.grid i D.R.m)) :=
  if h : i < D.R.m + 1 then (kappa W g).2 ⟨i, h⟩ else 1

theorem ptTop_lt (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {n : ℕ} (h : n < D.R.m) :
    ptTop W g n = (kappa W g).1 ⟨n, h⟩ := by
  simp only [ptTop, dif_pos h]

theorem ptTop_m (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) : ptTop W g D.R.m = kappaTop W g := by
  simp only [ptTop, lt_irrefl, dif_neg (lt_irrefl _), not_false_eq_true]
  rfl

theorem ptGrid_le (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {i : ℕ} (h : i < D.R.m + 1) :
    ptGrid W g i = (kappa W g).2 ⟨i, h⟩ := by
  simp only [ptGrid, dif_pos h]

end Points

section Scal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def rowScal (j : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nR j.castSucc) (fun τ => (P τ).e j - (S.nR j.succ / 2 : ℕ)) ((rowComp S g) j.castSucc) *
    detChar (S.nR j.succ) (fun τ => -(P τ).e j + (S.nR j.castSucc / 2 : ℕ)) ((rowComp S g) j.succ) : ℂˣ) : ℂ)

def colScal (i : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nC i.castSucc) (fun τ => (P τ).c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (g.2 i.castSucc) *
    detChar (S.nC i.succ) (fun τ => -(P τ).c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (g.2 i.succ) : ℂˣ) : ℂ)

end Scal

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Frame

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def topFrame (W : G.Weil) (τ : D.what₂.Tau) : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin (G.V (.top D.R.m)).rank) ℂ :=
  Matrix.of fun a k =>
    Sum.elim (fun b : Fin ((rowSizes D).nC D.R.m) =>
        ((frameMat _ _ G.sp.topDec.ι).map (tauE D τ) * W.onb (.grid D.R.m D.R.m) τ) a (Fin.cast (rank_gridM G le_rfl).symm b))
      (fun _ : Fin 1 => (G.sp.topDec.a.map (tauE D τ)) a 0)
      ((finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)).symm (Fin.cast (rank_top G le_rfl) k))

end Frame

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section More

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem ptTop_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : ptTop W g n ∈ GinfC (G.V (.top n)) := by
  unfold ptTop
  split_ifs with h h'
  · exact kappa_fst_mem W g _
  · subst h'; exact kappaTop_mem W g
  · exact one_mem _

theorem ptGrid_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : ptGrid W g i ∈ GinfC (G.V (.grid i D.R.m)) := by
  unfold ptGrid
  split_ifs with h
  · exact kappa_snd_mem W g _
  · exact one_mem _

theorem isKMat_cast {a b : ℕ} (h : a = b) (u : Matrix.unitaryGroup (Fin b) ℂ) {p : ℕ} (hp : p = a ∨ p = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat p ((u : Matrix (Fin b) (Fin b) ℂ).submatrix (Fin.cast h) (Fin.cast h)) := by
  subst h
  refine ⟨by simpa using u.2, fun i j hij => absurd ?_ hij⟩
  rcases hp with rfl | rfl
  · exact iff_of_true i.2 j.2
  · exact iff_of_false (Nat.not_lt_zero _) (Nat.not_lt_zero _)

theorem trCol_injective (G : GridData L sc) (j : Fin D.R.m) : Function.Injective (trCol G j) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem trRow_injective (G : GridData L sc) (i : Fin D.R.m) : Function.Injective (trRow G i) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)

theorem eq_conj_of_inFrame {n : ℕ} {B M K : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B.det) (h : B⁻¹ * M * B = K) :
    M = B * K * B⁻¹ := by
  rw [← h]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]

end More

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefPairTens

open GlobalTheory.DefLift GlobalTheory.DefiniteMult Formalism.IndefR.Mult

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem sigma_one (M : DSModel V S) (τ : D.what₂.Tau) : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1

theorem sigma_mul (hp : AllPlus M) (τ : D.what₂.Tau) (a b : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    M.σ τ ((a : Matrix (Fin V.rank) (Fin V.rank) ℂ) * b) = (M.σ τ a).comp (M.σ τ b) := by
  have hm : ∀ x : Matrix.unitaryGroup (Fin V.rank) ℂ,
      (x : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * Formalism.REAL.Jm (M.ε τ) * x = Formalism.REAL.Jm (M.ε τ) := fun x => by
    rw [hp.jm τ, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff'.1 x.2
  exact (M.ds τ).2.2.1.1.2 _ (hm a) _ (hm b)

theorem sigma_comp_inv (hp : AllPlus M) (τ : D.what₂.Tau) (v : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ
      ((M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show M.σ τ v (M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) x) = x
  rw [← ContinuousLinearMap.comp_apply, ← sigma_mul hp, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
    sigma_one]
  rfl

theorem unfr_one (M : DSModel V S) (τ : D.what₂.Tau) : unfr M τ 1 = 1 := by
  unfold unfr
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem pairEquiv_realAll : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  intro D V S M θ c pr hθ hp hc hpr
  classical
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨-, inj, π, hπ, -⟩ := tensor_irreducible D V S M m hp
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (m τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  let E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ) := (LinearEquiv.ofBijective pr hb).trans e.symm.dualMap
  have hE : ∀ w y, E w y = pr w (e.symm y) := fun w y => rfl
  let F : ∀ τ, Matrix.unitaryGroup (Fin V.rank) ℂ → (M.H τ →ₗ[ℂ] M.H τ) := fun τ v =>
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)
  have hact : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ), actT M τ (unfr M τ v) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v)) := by
    intro τ v
    unfold actT
    rw [rep_unfr]
  have hπe : ∀ τ v x, π τ v x = e.symm (actT M τ (unfr M τ v) (e x)) := fun τ v x => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, he, hπ]
  have hinv : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) x, π τ v (π τ v⁻¹ x) = x := by
    intro τ v x
    rw [hπe, hπe, LinearEquiv.apply_symm_apply, hact, hact, ← LinearMap.comp_apply (PiTensorProduct.map _),
      ← PiTensorProduct.map_comp]
    have : (fun ρ => Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v) ρ ∘ₗ
        Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹) ρ) = fun ρ => LinearMap.id := by
      funext ρ
      by_cases h : ρ = τ
      · subst h
        simp only [Function.update_self]
        exact GlobalTheory.CoefPairTens.sigma_comp_inv hp ρ v
      · simp only [Function.update_of_ne h, LinearMap.id_comp]
    rw [this, PiTensorProduct.map_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply]
  have one : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) w,
      E (c.ρ (atTau θ V τ (unfr M τ v)) w) =
        E w ∘ₗ PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹)) := by
    intro τ v w
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearMap.comp_apply, hE, hE, ← hact, ← hπe, LinearEquiv.symm_apply_apply]
    have h1 := key τ v (c.ρ (atTau θ V τ (unfr M τ v)) w) (π τ v⁻¹ x)
    rw [hinv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
    exact h1
  refine ⟨E, fun u w => ?_⟩
  let us : Finset D.what₂.Tau → UG D.what₂.Tau V.rank := fun s ρ => if ρ ∈ s then u ρ else 1
  have hM : ∀ (s : Finset D.what₂.Tau) ρ, unfr M ρ (us s ρ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun s ρ =>
    hp.unfr_mem ρ _
  have ind : ∀ s : Finset D.what₂.Tau, ∀ w, E (c.ρ (realAll θ V (fun ρ => unfr M ρ (us s ρ))) w) =
      E w ∘ₗ PiTensorProduct.map (fun ρ => F ρ (us s ρ)⁻¹) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w
      have h0 : (fun ρ => unfr M ρ (us ∅ ρ)) = 1 := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        rw [this, OneMemClass.coe_one, Pi.one_apply]
        exact GlobalTheory.CoefPairTens.unfr_one M ρ
      have h1 : (fun ρ => F ρ (us ∅ ρ)⁻¹) = fun ρ => LinearMap.id := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        show ((M.σ ρ ((us ∅ ρ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) = _
        rw [this, inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      rw [h0, realAll_one hθ, map_one, Module.End.one_apply, h1, PiTensorProduct.map_id, LinearMap.comp_id]
    | insert τ s hτ ih =>
      intro w
      have hs : us s τ = 1 := if_neg hτ
      have h3 : us (insert τ s) τ = u τ := if_pos (Finset.mem_insert_self τ s)
      have h4 : ∀ ρ, ρ ≠ τ → us (insert τ s) ρ = us s ρ := fun ρ h => by
        simp only [us, Finset.mem_insert, h, false_or]
      rw [realAll_eq_atTau_mul hθ (hM (insert τ s)) τ]
      have h2 : Function.update (fun ρ => unfr M ρ (us (insert τ s) ρ)) τ 1 = fun ρ => unfr M ρ (us s ρ) := by
        funext ρ
        by_cases h : ρ = τ
        · rw [h, Function.update_self, hs, OneMemClass.coe_one, GlobalTheory.CoefPairTens.unfr_one]
        · rw [Function.update_of_ne h, h4 ρ h]
      rw [h2, map_mul, Module.End.mul_apply, h3, one, ih, LinearMap.comp_assoc, ← PiTensorProduct.map_comp]
      congr 2
      funext ρ
      by_cases h : ρ = τ
      · subst h
        rw [Function.update_self, hs, h3]
        show ((M.σ ρ ((1 : Matrix.unitaryGroup (Fin V.rank) ℂ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
          M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) ∘ₗ F ρ (u ρ)⁻¹ = F ρ (u ρ)⁻¹
        rw [inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      · rw [Function.update_of_ne h, h4 ρ h, LinearMap.comp_id]
  have huniv : us Finset.univ = u := funext fun ρ => if_pos (Finset.mem_univ ρ)
  have := ind Finset.univ w
  rw [huniv] at this
  exact this

end GlobalTheory.CoefPairTens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealCentralCharacterDefiniteVertexMultipli
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefCenChar

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem unframe_mem_UH {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.MainNotions.S.UJset (M.ε τ)) :
    (M.fr τ)⁻¹ * u * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : uᴴ * Formalism.REAL.Jm (M.ε τ) * u = Formalism.REAL.Jm (M.ε τ) := hu
  have e1 : M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) = u * M.fr τ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  change ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * u * M.fr τ) = gramAt D V τ
  rw [← M.fr_gram τ]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ)) := by
        rw [Matrix.conjTranspose_mul (M.fr τ)]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by
        rw [e1, Matrix.conjTranspose_mul]
        calc (M.fr τ)ᴴ * uᴴ * Formalism.REAL.Jm (M.ε τ) * (u * M.fr τ) = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hJ]

theorem rep_scalar {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {a : Matrix (Fin V.rank) (Fin V.rank) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), g * a = a * g) : ∃ c : ℂ, ∀ w, M.rep τ a w = c • w := by
  haveI : Nontrivial (M.H τ) := (M.ds τ).2.1
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  let A : Module.End ℂ (M.H τ) := (M.rep τ a : M.H τ →ₗ[ℂ] M.H τ)
  obtain ⟨c, hcA⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, fun w => ?_⟩
  have hirr := (M.ds τ).2.2.2.1
  have hinv : ∀ u ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ v ∈ A.eigenspace c, M.σ τ u v ∈ A.eigenspace c := by
    intro u hu v hv
    have hg := unframe_mem_UH M τ hu
    have e : M.σ τ u = M.rep τ ((M.fr τ)⁻¹ * u * M.fr τ) := by
      unfold DSModel.rep
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [e]
    show M.rep τ a (M.rep τ _ v) = c • M.rep τ _ v
    rw [← GlobalTheory.ConjMult.rep_mul M τ _ ha _ hg, ← hc _ hg, GlobalTheory.ConjMult.rep_mul M τ _ hg _ ha]
    have hv' : M.rep τ a v = c • v := hv
    rw [hv', map_smul]
  rcases hirr (A.eigenspace c) (Submodule.closed_of_finiteDimensional _) hinv with h | h
  · exact absurd h hcA
  · have hw : w ∈ A.eigenspace c := h ▸ Submodule.mem_top
    exact (Module.End.mem_eigenspace_iff).1 hw

theorem infMat_comm {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {z : GA D V} (hzc : z ∈ Subgroup.center (GA D V))
    (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    g * infMat D.sp.cm.sig V.gram (θ τ) z = infMat D.sp.cm.sig V.gram (θ τ) z * g := by
  have e := congrArg (infMat D.sp.cm.sig V.gram (θ τ)) (Subgroup.mem_center_iff.1 hzc (atTau θ V τ g))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul,
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg).2.1] at e
  exact e

theorem rTr_atTau_of_scalar {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {c : ℂ} (hc : ∀ w, M.rep τ g w = c • w) (v : M.Vec) :
    rTr V (atTau θ V τ g) (T v) = c • T v := by
  classical
  have e := hT.equiv τ g hg v (c • v τ) (by rw [hc]; rfl)
  rw [← e, T.map_update_smul, Function.update_eq_self]
  rfl

theorem rTr_realAll {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (Mz : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hM : ∀ ρ, Mz ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (c : D.what₂.Tau → ℂ) (hc : ∀ ρ w, M.rep ρ (Mz ρ) w = c ρ • w) (v : M.Vec) :
    rTr V (GlobalTheory.RowReal.realAll θ V Mz) (T v) = (∏ ρ, c ρ) • T v := by
  classical
  have key : ∀ s : Finset D.what₂.Tau,
      rTr V (GlobalTheory.RowReal.realAll θ V (fun ρ => if ρ ∈ s then Mz ρ else 1)) (T v) = (∏ ρ ∈ s, c ρ) • T v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : (fun ρ : D.what₂.Tau => if ρ ∈ (∅ : Finset D.what₂.Tau) then Mz ρ else 1) = 1 := by
        funext ρ; simp
      rw [e, GlobalTheory.RowReal.realAll_one hθ, Finset.prod_empty, one_smul]
      funext x; simp [rTr]
    | insert τ s hτ ih =>
      have hMs : ∀ ρ, (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun ρ => by
        dsimp only
        split_ifs
        · exact hM ρ
        · exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
      rw [GlobalTheory.RowReal.realAll_eq_atTau_mul hθ hMs τ]
      have e : Function.update (fun ρ => if ρ ∈ insert τ s then Mz ρ else 1) τ 1 =
          fun ρ => if ρ ∈ s then Mz ρ else 1 := by
        funext ρ
        by_cases h : ρ = τ
        · subst h; simp [hτ]
        · rw [Function.update_of_ne h]; simp [Finset.mem_insert, h]
      rw [e, Finset.prod_insert hτ]
      simp only [Finset.mem_insert_self, if_true]
      funext x
      have i1 := congrFun ih (x * atTau θ V τ (Mz τ))
      have i2 := congrFun (rTr_atTau_of_scalar hT τ (hM τ) (hc τ) v) x
      simp only [rTr, Pi.smul_apply, smul_eq_mul] at i1 i2 ⊢
      rw [← mul_assoc, i1, i2]
      ring
  have e : (fun ρ : D.what₂.Tau => if ρ ∈ (Finset.univ : Finset D.what₂.Tau) then Mz ρ else 1) = Mz := by
    funext ρ; simp
  have := key Finset.univ
  rwa [e] at this

theorem cusp_hasCen : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ν : ℕ) (P : D.what₂.Tau → SPar), N.Is ν 0 P → ∃ χ : GA D N.V → ℂ, ∀ (F : N.Cusp θ) (v : SmT N.M), GlobalTheory.SeeSaw.HasCen N.V χ (F.1 v) := by
  intro D θ hθ N ν P hN
  have hs : N.V.SigOK := hN.sigOK
  have hd : N.V.IsDefinite := fun τ => Or.inl (by rw [hN.sig, hN.rank]; simp)
  have hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have key : ∀ (z : GA D N.V) (ρ : D.what₂.Tau), ∃ c : ℂ, z ∈ Subgroup.center (GA D N.V) →
      ∀ w, N.M.rep ρ (infMat D.sp.cm.sig N.V.gram (θ ρ) z) w = c • w := by
    intro z ρ
    by_cases hz : z ∈ Subgroup.center (GA D N.V)
    · haveI := hfd ρ
      obtain ⟨c, hc⟩ := rep_scalar N.M ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ)
        (fun g hg => infMat_comm hθ hz ρ hg)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose c hc using key
  refine ⟨fun z => ∏ ρ, c z ρ, fun F v z hz hzc h => ?_⟩
  have hreal : ∀ T : MMap N.M, IsMultMap θ N.M ∅ 1 T → ∀ (u : N.M.Vec) (g : GA D N.V),
      T u (g * z) = (∏ ρ, c z ρ) * T u g := by
    intro T hT u g
    have e : GlobalTheory.RowReal.realAll θ N.V (fun ρ => infMat D.sp.cm.sig N.V.gram (θ ρ) z) = z :=
      GlobalTheory.RowReal.realAll_eq hθ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) ⟨hz, fun ρ => rfl⟩
    have := rTr_realAll hθ hT _ (fun ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ N.V z ρ) (c z)
      (fun ρ => hc z ρ hzc) u
    rw [e] at this
    exact congrFun this g
  have key2 : ∀ T ∈ Mult θ N.M ∅ 1, ∀ (x : SmT N.M) (g : GA D N.V),
      PiTensorProduct.lift T x (g * z) = (∏ ρ, c z ρ) * PiTensorProduct.lift T x g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        intro g
        simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul]
        rw [hreal T hT f g]
        ring
      | add a b ha hb =>
        intro g
        simp only [map_add (f := _), Pi.add_apply]
        rw [ha g, hb g]
        ring
    | zero => intro x g; simp
    | add T T' _ _ h1 h2 =>
      intro x g
      simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
      rw [h1 x g, h2 x g]
      ring
    | smul a T _ h =>
      intro x g
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [h x g]
      ring
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ N.M ∅ 1 := (mem_multT θ N.M ∅ 1 F.1).1 F.2
  have := key2 _ hm v h
  rw [LinearEquiv.apply_symm_apply] at this
  exact this

end GlobalTheory.DefCenChar

end
end

