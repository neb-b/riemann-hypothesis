module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameExists

theorem exists_signFrame {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (hd : IsUnit H.det) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = H := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  let l := hH.eigenvalues
  let S : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => ((Real.sqrt |l a| : ℝ) : ℂ)
  have hs : H = U * diagonal (fun a => ((l a : ℝ) : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hS : Sᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * S = diagonal (fun a => ((l a : ℝ) : ℂ)) := by
    simp only [S, Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : ((Real.sqrt |l a| : ℝ) : ℂ) * ((Real.sqrt |l a| : ℝ) : ℂ) = ((|l a| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [mul_right_comm, h1]
    by_cases h : 0 < l a
    · simp [h, abs_of_pos h]
    · simp [h, abs_of_nonpos (not_lt.1 h)]
  have key : (S * Uᴴ)ᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * (S * Uᴴ) = H := by
    rw [hs, ← hS, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  refine ⟨_, S * Uᴴ, ?_, key⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [← key, det_mul] at hd
  exact isUnit_of_mul_isUnit_right hd

theorem exists_perm_of_card {n : ℕ} {ε η : Fin n → Bool}
    (h : Nat.card {a // ε a = true} = Nat.card {a // η a = true}) :
    ∃ σ : Fin n ≃ Fin n, ∀ a, ε (σ a) = η a := by
  have hf : ∀ b : Bool, Nonempty ({a // η a = b} ≃ {a // ε a = b}) := by
    intro b
    rw [← Finite.card_eq]
    cases b
    · have e : ∀ θ : Fin n → Bool, Nat.card {a // θ a = false} = n - Nat.card {a // θ a = true} := by
        intro θ
        have := Fintype.card_subtype_compl (fun a => θ a = true)
        simp only [Nat.card_eq_fintype_card]
        simpa using this
      rw [e, e, h]
    · exact h.symm
  exact ⟨Equiv.ofFiberEquiv fun b => (hf b).some, fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem exists_signCompat {n p q : ℕ} {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature (Pᴴ * Formalism.REAL.Jm ε * P) p q) :
    ∃ e : Fin p ⊕ Fin q ≃ Fin n, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e := by
  obtain ⟨e, Q, hQ⟩ := h
  have hc : Formalism.UG.cT (starRingEnd ℂ) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := rfl
  rw [hc] at hQ
  have h1 : (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e)ᴴ * Formalism.REAL.Jm ε *
      (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e) =
      Formalism.REAL.Jm fun a => (e a).isLeft := by
    have h2 := congrArg (fun M => Matrix.submatrix M e e) hQ
    simp only [← submatrix_mul_equiv _ _ _ e, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self,
      submatrix_id_id] at h2
    rw [conjTranspose_mul, conjTranspose_submatrix]
    simp only [Matrix.mul_assoc] at h2 ⊢
    rw [h2]
    ext a b
    obtain ⟨x, rfl⟩ := e.symm.surjective a
    obtain ⟨y, rfl⟩ := e.symm.surjective b
    simp only [submatrix_apply, Formalism.REAL.Jm, Formalism.UG.Jpq, diagonal_apply, Equiv.apply_symm_apply]
    rcases x with i | i <;> rcases y with j | j <;> simp [Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨σ, hσ⟩ := exists_perm_of_card (GlobalTheory.SignCount.card_true_eq _ h1)
  exact ⟨e.symm.trans σ, fun a => by simp [hσ]⟩

theorem frame_exists_signCompat : ∀ (D : D7) (V : HSp D), Nonempty (GlobalTheory.ChainFr.Fr V) ∧ ∀ (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) (p q : ℕ), Formalism.UG.HasSignature (gramAt D V τ) p q → ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (A.ε τ) e := by
  intro D V
  refine ⟨?_, fun A τ p q h => exists_signCompat (P := A.fr τ) (by rw [A.fr_gram]; exact h)⟩
  choose ε P h1 h2 using fun τ => exists_signFrame (H := gramAt D V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  exact ⟨⟨ε, P, h1, h2⟩⟩

end GlobalTheory.FrameExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeMonoidAlgebraOfCharacterVanishesOffOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FreeOfCharacter

noncomputable def freeRep (P : Type) [Group P] (N : ℕ) :
    Representation ℂ P (Fin N → MonoidAlgebra ℂ P) where
  toFun g :=
    { toFun := fun x => (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [← MonoidAlgebra.one_def]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [smul_smul, MonoidAlgebra.single_mul_single]

theorem freeRep_apply {P : Type} [Group P] {N : ℕ} (g : P) (x : Fin N → MonoidAlgebra ℂ P) :
    freeRep P N g x = (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x := rfl

theorem trace_freeRep {P : Type} [Group P] [Finite P] (N : ℕ) {g : P} (hg : g ≠ 1) :
    LinearMap.trace ℂ _ (freeRep P N g) = 0 := by
  classical
  haveI := Fintype.ofFinite P
  let b := Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ
  have hb : ∀ (j : Fin N) (q : P), b ⟨j, q⟩ = Pi.single j (MonoidAlgebra.single q 1) := by
    intro j q
    simp [b, Pi.basis_apply]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨j, p⟩ := i
  have hmove : freeRep P N g (b ⟨j, p⟩) = b ⟨j, g * p⟩ := by
    rw [hb, hb, freeRep_apply]
    funext k
    by_cases hk : k = j
    · subst hk
      simp [MonoidAlgebra.single_mul_single]
    · simp [hk]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hmove, b.repr_self, Finsupp.single_apply, if_neg]
  intro h
  rw [Sigma.mk.inj_iff, heq_iff_eq] at h
  exact hg (mul_right_cancel (h.2.trans (one_mul p).symm))

theorem finrank_free (P : Type) [Group P] [Finite P] (N : ℕ) :
    Module.finrank ℂ (Fin N → MonoidAlgebra ℂ P) = Nat.card P * N := by
  haveI := Fintype.ofFinite P
  rw [Module.finrank_eq_card_basis (Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ),
    Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

theorem free_of_trace_eq_zero : ∀ (P M : Type) [Group P] [Finite P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ P M), (∀ g : P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M ∧ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ P] (Fin N → MonoidAlgebra ℂ P)) := by
  intro P M _ _ _ _ _ ρ hρ
  classical
  haveI := Fintype.ofFinite P
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  haveI : Invertible (Nat.card P : ℂ) := invertibleOfNonzero hcard

  have hz : ∀ g : P, g ≠ 1 → ρ.character g = 0 := hρ
  have havg := Representation.card_inv_mul_sum_char_eq_finrank ρ
  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => hz g hg) (by simp),
    Representation.char_one] at havg
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M := by
    refine ⟨Module.finrank ℂ (Representation.invariants ρ), ?_⟩
    have hc : ((Nat.card P * Module.finrank ℂ (Representation.invariants ρ) : ℕ) : ℂ) =
        (Module.finrank ℂ M : ℂ) := by
      push_cast
      rw [← havg, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    exact_mod_cast hc
  refine ⟨N, hN, ?_⟩
  haveI : FiniteDimensional ℂ (MonoidAlgebra ℂ P) :=
    Module.Finite.of_basis (MonoidAlgebra.basis P ℂ)

  have hχ : ρ.character = (freeRep P N).character := by
    funext g
    by_cases hg : g = 1
    · subst hg
      rw [Representation.char_one, Representation.char_one, finrank_free, hN]
    · exact (hz g hg).trans (trace_freeRep N hg).symm
  obtain ⟨e⟩ := GlobalTheory.CharacterDetermines.nonempty_equiv_of_character_eq P M
    (Fin N → MonoidAlgebra ℂ P) ρ (freeRep P N) hχ

  have hlin : ∀ (r : MonoidAlgebra ℂ P) (x : M),
      e.toLinearEquiv (ρ.asAlgebraHom r x) = (freeRep P N).asAlgebraHom r (e.toLinearEquiv x) := by
    intro r x
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      simp only [Representation.asAlgebraHom_of]
      exact e.toIntertwiningMap.isIntertwining _ _ g x
    | add f f' hf hf' => simp only [map_add (f := _), LinearMap.add_apply, hf, hf']
    | smul c f hf => simp only [map_smul, LinearMap.smul_apply, hf]

  have hact : ∀ (r : MonoidAlgebra ℂ P) (y : Fin N → MonoidAlgebra ℂ P),
      (freeRep P N).asAlgebraHom r y = r • y := by
    intro r y
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [Representation.asAlgebraHom_of, freeRep_apply, MonoidAlgebra.of_apply]
    | add f f' hf hf' => rw [map_add (f := _), LinearMap.add_apply, hf, hf', add_smul]
    | smul c f hf => rw [map_smul, LinearMap.smul_apply, hf, smul_assoc]
  exact ⟨{ (ρ.asModuleEquiv.trans e.toLinearEquiv).toAddEquiv with
    map_smul' := fun r x => by
      change e.toLinearEquiv (ρ.asModuleEquiv (r • x)) = r • e.toLinearEquiv (ρ.asModuleEquiv x)
      rw [Representation.asModuleEquiv_map_smul, hlin, hact] }⟩

end GlobalTheory.FreeOfCharacter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsDefiniteExist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRows

theorem goodForms_definite_exist : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodVectorsDefinite → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥ := by
  intro hGV eps heps
  obtain ⟨x₀, hx₀⟩ := hGV.2 eps heps
  refine ⟨x₀, ?_⟩
  intro D L hP heps' hxL hSz G _ _ Pl0 T A Ks _ _ _ R F hGiv b

  have hTie : GlobalTheory.GLq.ESerTie D := by
    intro k
    obtain ⟨LD, hT, hE, _⟩ := hGiv.types k
    exact ⟨LD, hT, hE⟩

  obtain ⟨kap, lam, hScal⟩ := Formalism.IndefR.Links.scal_exists (F := F) R
  have hSet : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.HidaSetting (R.upd6 kap lam) F :=
    { lev := hGiv.core.lev
      grp := { hGiv.core.grp with }
      fam := { hGiv.core.fam with }
      models := { hGiv.core.models with }
      chain := Formalism.IndefR.Links.RealDat.chain_of_scalar_update hGiv.core.chain kap lam
      thP := Formalism.IndefR.Links.RealDat.theta_props_of_scalar_update hGiv.core.thP kap lam
      scal := hScal }

  obtain ⟨i, hi⟩ := GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.exists_last D
  have hShare := hx₀ D L hP heps' hxL hSz hTie G Pl0 T A Ks (R.upd6 kap lam) F hSet i hi b
  exact ⟨i, GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodShare.ne_bot (R.upd6 kap lam) F hShare⟩

end GlobalTheory.LiftRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimes
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodProjProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem monicOf_injective {g N : ℕ} [Fact g.Prime] :
    Function.Injective fun c : Fin N → ZMod g => (Formalism.CyclotomicNorms.monicOf c : (ZMod g)[X]) := by
  intro c c' h
  funext i
  have key := congrArg (fun p : (ZMod g)[X] => p.coeff (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Nat.ne_of_lt i.isLt, if_false, zero_add] at key
  rwa [Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl,
    Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl] at key


open Classical in
theorem sum_good {g N m : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] [Fintype (ι → Fin N → ZMod g)]
    (ch : ι → Fin m → (ZMod g)ˣ) (h : (ι → (ZMod g)[X]) → ℂ) :
    (∑ a : ι → Fin N → ZMod g, if GlobalTheory.BadShare.Good g N ch (fun v => Formalism.CyclotomicNorms.monicOf (a v)) then
      h (fun v => Formalism.CyclotomicNorms.monicOf (a v)) else 0) = ∑ F ∈ GlobalTheory.BadShare.goodSet g N ch, h F := by
  have hinj : Function.Injective fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) :=
    by
      intro a b hab
      funext v
      have hv : Formalism.CyclotomicNorms.monicOf (a v) = (Formalism.CyclotomicNorms.monicOf (b v) : (ZMod g)[X]) := congrFun hab v
      exact monicOf_injective (g := g) (N := N) hv
  have hset : GlobalTheory.BadShare.goodSet g N ch =
      (Finset.univ.filter fun a : ι → Fin N → ZMod g => GlobalTheory.BadShare.Good g N ch fun v => Formalism.CyclotomicNorms.monicOf (a v)).image
        fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) := by
    ext F
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hF
      have hG := GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF
      have hsq := (GlobalTheory.BadShare.good_iff.1 hG).1
      have hc : ∀ v, ∃ c : Fin N → ZMod g, Formalism.CyclotomicNorms.monicOf c = F v := by
        intro v
        have hv := hsq v
        rw [GlobalTheory.BadShare.sqSet_eq_monicOf, Finset.mem_filter, Finset.mem_image] at hv
        obtain ⟨c, -, hc⟩ := hv.1
        exact ⟨c, hc⟩
      choose a ha using hc
      have hMa : (fun v => Formalism.CyclotomicNorms.monicOf (a v)) = F := funext ha
      refine ⟨a, ?_, hMa⟩
      rw [hMa]
      exact hG
    · rintro ⟨a, hG, rfl⟩
      exact GlobalTheory.BadShare.mem_goodSet_iff_good.2 hG
  rw [hset, Finset.sum_image (fun a _ b _ e => hinj e), Finset.sum_filter]

theorem sum_sigma_two {P : Fin 2 → Type} {A : Fin 2 → Type} [Fintype (∀ kv : (Σ k : Fin 2, P k), A kv.1)]
    [Fintype (P 0 → A 0)] [Fintype (P 1 → A 1)] (f0 : (P 0 → A 0) → ℂ) (f1 : (P 1 → A 1) → ℂ) :
    (∑ a : (∀ kv : (Σ k : Fin 2, P k), A kv.1), f0 (fun v => a ⟨0, v⟩) * f1 (fun v => a ⟨1, v⟩)) =
      (∑ a, f0 a) * ∑ b, f1 b := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.piCurry fun (k : Fin 2) (_ : P k) => A k).trans
    (piFinTwoEquiv fun k => P k → A k)) _ _ (fun a => rfl)

theorem goodProjector_coeff_eq_prod_at_two_typePrimes : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  intro D τ hτ γ
  classical
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0 := by
    unfold NTypes.e0
    rfl
  let f : ∀ k : Fin 2, (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) → ℂ := fun k b =>
    if GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (b v)) then
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (b v))).coeff (γ ⟨k, v⟩) else 0
  have hsplit : ∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) =
        f 0 (fun v => a ⟨0, v⟩) * f 1 (fun v => a ⟨1, v⟩) := by
    intro a
    have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
        ∀ k : Fin 2, GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := by
      unfold NTypes.goodTuple GlobalTheory.BadShare.Good
      exact Iff.rfl
    rw [Fintype.prod_sigma, Fin.prod_univ_two]
    by_cases h0 : GlobalTheory.BadShare.Good (D.host.g 0) D.R.r (D.nd.chiT 0) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
      by_cases h1 : GlobalTheory.BadShare.Good (D.host.g 1) D.R.r (D.nd.chiT 1) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
      simp [f, hg, Fin.forall_fin_two, h0, h1]
  have hk : ∀ k : Fin 2, ∑ b, f k b = GlobalTheory.BadShare.eGood (fun _ => τ k) (D.nd.chiT k) (fun v => γ ⟨k, v⟩) := by
    intro k
    refine (Eq.trans ?_ (sum_good (g := D.host.g k) (N := D.R.r) (D.nd.chiT k)
      (fun F => ∏ v, (D.ntypes.eSer k (F v)).coeff (γ ⟨k, v⟩)))).trans ?_
    · rfl
    · unfold GlobalTheory.BadShare.eGood
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl (fun F hF => ?_)
      have hsq := (GlobalTheory.BadShare.good_iff.1 (GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF)).1
      unfold GlobalTheory.BadShare.tens
      exact Finset.prod_congr rfl fun v _ => hτ k (F v) (hsq v) (γ ⟨k, v⟩)
  rw [he, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ hsplit,
    sum_sigma_two (P := fun k => D.nd.PlG k) (A := fun k => Fin D.R.r → ZMod (D.host.g k)) (f 0) (f 1), hk 0, hk 1]

end GlobalTheory.GoodProjProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentComponentMemFrameStabilizer
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompStab

theorem idem_mul {R : Type} [CommRing R] {n : ℕ} (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (f : R)
    (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem comp_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (φ : Formalism.L2.Herm.intAf F E) (hφ : φ * φ = φ)
    (x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β)
    (h : x'.1 = (φ : E ⊗[F] Formalism.L2.Herm.Af F) • x.1 + (1 - (φ : E ⊗[F] Formalism.L2.Herm.Af F)) • 1) : x' ∈ St β := by
  obtain ⟨y, rfl⟩ := hS
  refine ⟨⟨φ • y.1 + (1 - φ) • 1, φ • (y⁻¹).1 + (1 - φ) • 1, idem_mul φ hφ _ _ y.mul_inv,
    idem_mul φ hφ _ _ y.inv_mul⟩, Units.ext ?_⟩
  rw [h]
  show β.1 * (φ • y.1 + (1 - φ) • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))).map
      (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 =
    (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) + _
  rw [map_idem, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Units.mul_inv]
  rfl

theorem comm_int {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E := by
  refine AddSubgroup.closure_induction (p := fun z _ =>
    (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E z : E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, x, rfl⟩
    have : (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E (a ⊗ₜ[F] (x : E)) : E ⊗[F] Formalism.L2.Herm.Af F) =
        ((oToS F E x : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((1 : E) ⊗ₜ[F] a) := by
      rw [oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]; rfl
    rw [this]
    exact Subring.mul_mem _ (oToS F E x).2 (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · rw [map_zero]; exact Subring.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add (f := _)]; exact Subring.add_mem _ ha hb
  · intro a _ ha
    rw [map_neg]; exact Subring.neg_mem _ ha

end General

theorem component_mem_St : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g g' : GA D V) (f : AE D), f * f = f → finE V g ∈ St β → Formalism.L2.Theta.mt V g' = f • Formalism.L2.Theta.mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → finE V g' ∈ St β := by
  intro D V β g g' f hf hg h
  let ψ : AE D →+* Lev.EAf D := (swapAE D).comp (finPart D)
  have hi : ψ f ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    comm_int (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D f) (by rw [← RingHom.map_mul, hf]))
  refine comp_mem_St β ⟨ψ f, hi⟩ (Subtype.ext ?_) (finE V g) _ hg ?_
  · show ψ f * ψ f = ψ f
    rw [← RingHom.map_mul, hf]
  · show (Formalism.L2.Theta.mt V g').map ψ = ψ f • (Formalism.L2.Theta.mt V g).map ψ + (1 - ψ f) • 1
    rw [h, map_idem]

end GlobalTheory.CompStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfSStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_jacquet_eq_borelJacquet_of_small : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n), StrictMono (blk f) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ), jhMult (ofChar (leviChar c χ)) (jac f π) = jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  first | exact @GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | exact GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB | (intros; apply GlobalTheory.SmGL.EmptyBlocks.jhMult_jac_eq_jacB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConjStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stdMaxParabolic_of_blockParabolic_le_conj : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ) (hd : ∑ i, d i = r) (g : GL (Fin r) F),
    parab F (stdBlocks d hd) ≤ conjBy g (stdMaxParab F h) → g ∈ stdMaxParab F h := by
  first | exact @GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | exact GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy | (intros; apply GlobalTheory.ParabConj.mem_stdMaxParab_of_le_conjBy <;> assumption)
end

