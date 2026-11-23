module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectivePairingFiniteFamily
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Sep

variable {D : D7} {r : ℕ}

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR]
  rw [h]
  exact (hθ τ).1 x

theorem pairF_eq {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (a β : HermE D r) :
    pairF θ α a β =
      -∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (β.1 * a.1))).re := by
  unfold pairF lam
  simp only [← map_mul, theta_incA hθ]

def hermQ (D : D7) (r : ℕ) : Submodule ℚ (Matrix (Fin r) (Fin r) D.host.E) where
  carrier := {b | (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 h2 ⊢
    simp only [Matrix.add_apply, map_add (f := _), h1, h2]
  zero_mem' := by
    ext i j
    simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
    simp only [Matrix.smul_apply, map_rat_smul, h1]

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
  obtain ⟨τ, -⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 w
  exact ⟨τ⟩

theorem mem_hermQ {b : Matrix (Fin r) (Fin r) D.host.E} :
    b ∈ hermQ D r ↔ ∀ i j, D.sp.cm.sig (b j i) = b i j := by
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    exact Matrix.ext fun i j => h i j

def formH (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) : hermQ D r →+ ℝ :=
  AddMonoidHom.mk'
    (fun a => ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re)
    (by
      intro a b
      simp only [Submodule.coe_add, mul_add, Matrix.trace_add, map_add (f := _), Complex.add_re,
        Finset.sum_add_distrib])

theorem formH_apply (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α δ a =
      ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re := rfl

theorem formH_eq_zero {d : ℕ} (b : Module.Basis (Fin d) ℚ (hermQ D r)) {α : D.host.F}
    {δ : Matrix (Fin r) (Fin r) D.host.E} (h : ∀ k, formH α δ (b k) = 0) (a : hermQ D r) :
    formH α δ a = 0 := by
  have e : (formH α δ).toRatLinearMap = 0 := b.ext (fun k => by simpa using h k)
  simpa using LinearMap.congr_fun e a

theorem formH_sub_left (α : D.host.F) (b b' : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α (b - b') a = formH α b a - formH α b' a := by
  simp only [formH_apply, sub_mul, Matrix.trace_sub, mul_sub, map_sub, Complex.sub_re,
    Finset.sum_sub_distrib]

theorem pairF_eq_formH {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β : HermE D r)
    (a : hermQ D r) : pairF θ α ⟨a.1, a.2⟩ β = -formH α β.1 a :=
  pairF_eq hθ α ⟨a.1, a.2⟩ β

theorem formH_sub {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β β' : HermE D r)
    (a : hermQ D r) :
    formH α (β.1 - β'.1) a = pairF θ α ⟨a.1, a.2⟩ β' - pairF θ α ⟨a.1, a.2⟩ β := by
  have e := pairF_eq_formH hθ α β a
  have e' := pairF_eq_formH hθ α β' a
  have e'' := formH_sub_left α β.1 β'.1 a
  linarith

theorem trace_sq_ne_zero {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) (h0 : δ ≠ 0) :
    Matrix.trace (δ * δ) ≠ 0 := by
  intro hn
  obtain ⟨τ⟩ := tau_nonempty D
  have hm := mem_hermQ.1 hδ
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hc : ∀ i j, tauE D τ (δ j i) = starRingEnd ℂ (tauE D τ (δ i j)) := by
    intro i j
    rw [← hm j i]
    exact hcm.2.2.2 _ _
  have hs : ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) = 0 := by
    have e : tauE D τ (Matrix.trace (δ * δ)) =
        ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) := by
      push_cast
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hc i j, Complex.mul_conj]
    rw [← e, hn, map_zero]
  have hs' : (∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j))) = 0 := by exact_mod_cast hs
  apply h0
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).1 hs' i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg _)).1 h1 j (Finset.mem_univ j)
  have h3 : tauE D τ (δ i j) = 0 := Complex.normSq_eq_zero.1 h2
  simpa using h3

theorem sig_trace_sq {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) :
    D.sp.cm.sig (Matrix.trace (δ * δ)) = Matrix.trace (δ * δ) := by
  have hm := mem_hermQ.1 hδ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hm]
  rw [Finset.sum_comm]

theorem inv_smul_mem {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) {x : D.host.E}
    (hx : D.sp.cm.sig x = x) : x⁻¹ • δ ∈ hermQ D r := by
  have hm := mem_hermQ.1 hδ
  refine mem_hermQ.2 fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hx, hm]

theorem exists_separating : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ α : D.host.F, α ≠ 0 →
    ∃ (d : ℕ) (a : Fin d → HermE D r),
      Function.Injective (fun (β : HermE D r) (k : Fin d) => pairF θ α (a k) β) := by
  intro D r θ hθ α hα
  let b := Module.finBasis ℚ (hermQ D r)
  refine ⟨_, fun k => ⟨(b k).1, (b k).2⟩, ?_⟩
  intro β β' h
  by_contra hne
  have hδ : β.1 - β'.1 ∈ hermQ D r :=
    sub_mem (show β.1 ∈ hermQ D r from β.2) (show β'.1 ∈ hermQ D r from β'.2)
  have hδ0 : β.1 - β'.1 ≠ 0 := sub_ne_zero.2 fun e => hne (Subtype.ext e)
  have hz : ∀ a, formH α (β.1 - β'.1) a = 0 := by
    refine formH_eq_zero b fun k => ?_
    rw [formH_sub hθ]
    have := congrFun h k
    exact sub_eq_zero.2 this.symm
  set δ := β.1 - β'.1 with hδdef
  have hn := trace_sq_ne_zero hδ hδ0
  have hαE : algebraMap D.host.F D.host.E α ≠ 0 := by
    simpa using hα
  set x := algebraMap D.host.F D.host.E α * Matrix.trace (δ * δ) with hx
  have hx0 : x ≠ 0 := mul_ne_zero hαE hn
  have hxs : D.sp.cm.sig x = x := by
    rw [hx, map_mul, sig_trace_sq hδ, AlgHom.commutes]
  have hv := hz ⟨x⁻¹ • δ, inv_smul_mem hδ hxs⟩
  rw [formH_apply] at hv
  have h1 : algebraMap D.host.F D.host.E α * Matrix.trace (δ * (x⁻¹ • δ)) = 1 := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_comm _ x⁻¹, mul_assoc,
      ← hx, inv_mul_cancel₀ hx0]
  simp only [h1, map_one, Complex.one_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hv
  haveI := tau_nonempty D
  have : (Fintype.card D.what₂.Tau : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact this hv

end GlobalTheory.CompanionTheory.WSum.Sep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTer
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem coef_inv (hF : PFr s Jm Xm Ym) {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm)
    {d d' : Fin r → R} (e : M * Xm = Xm * diagonal d) (e' : M * Ym = Ym * diagonal d') (i : Fin r) :
    d i * s (d' i) = 1 := by
  have h := hF.inv_coef hM e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 := congrFun (congrFun h i) i
  have e3 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [e3, Matrix.diagonal_mul_diagonal] at h2
  simpa [mul_comm] using h2

theorem inv_mul_frame {M Mi : Matrix (Fin n) (Fin n) R} (hMi : Mi * M = 1) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) : Mi * Xm = Xm * diagonal c := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  calc Mi * Xm = Mi * (Xm * (diagonal d * diagonal c)) := by rw [h1, Matrix.mul_one]
    _ = Mi * M * Xm * diagonal c := by
      rw [← Matrix.mul_assoc Xm, ← e]
      simp only [Matrix.mul_assoc]
    _ = Xm * diagonal c := by rw [hMi, Matrix.one_mul]

theorem orth_mulVec {M : Matrix (Fin n) (Fin n) R} (hM : cT s M * Jm * M = Jm) {d c : Fin r → R}
    (hdc : ∀ i, d i * c i = 1) (e : M * Xm = Xm * diagonal d) {v : Fin n → R}
    (hv : (cT s Xm * Jm) *ᵥ v = 0) : (cT s Xm * Jm) *ᵥ (M *ᵥ v) = 0 := by
  have h1 : diagonal d * diagonal c = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hdc)
  have h := pgram_unitary hM (Xm * diagonal c) (1 : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.mul_assoc M, e, Matrix.mul_assoc Xm, h1, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one,
    Formalism.UG.cT_mul] at h
  rw [Matrix.mulVec_mulVec, h, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem clause_extend (hF : PFr s Jm Xm Ym) {U : Matrix (Fin n) (Fin n) R} {B : Matrix (Fin r) (Fin r) R}
    (hU : U * Xm = Xm * B) {P : Matrix (Fin n) (Fin n) R}
    (hP : P = 1 - Xm * (cT s Ym * Jm) - Ym * (cT s Xm * Jm))
    (hc : ∀ k, ∃ a : Fin r → R, (U - 1) *ᵥ (fun i => P i k) = Xm *ᵥ a) {w : Fin n → R}
    (hw : (cT s Xm * Jm) *ᵥ w = 0) : ∃ a : Fin r → R, (U - 1) *ᵥ w = Xm *ᵥ a := by
  choose A hA using hc
  have hUP : (U - 1) * P = Xm * (Matrix.of fun j k => A k j) := by
    ext i k
    have := congrFun (hA k) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hUX : (U - 1) * Xm = Xm * (B - 1) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hU, Matrix.mul_sub, Matrix.mul_one]
  have hwd : w = P *ᵥ w + Xm *ᵥ ((cT s Ym * Jm) *ᵥ w) := by
    rw [hP, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec w Ym, hw,
      Matrix.mulVec_zero, ← Matrix.mulVec_mulVec]
    abel
  refine ⟨(Matrix.of fun j k => A k j) *ᵥ w + (B - 1) *ᵥ ((cT s Ym * Jm) *ᵥ w), ?_⟩
  conv_lhs => rw [hwd]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUP, hUX, Matrix.mulVec_add]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

def orthProj (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    Matrix (Fin n) (Fin n) E :=
  1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)

theorem orth_orthProj (hW : IsWittFrame σ J X Y) : (cT (σ : E →+* E) X * J) * orthProj σ J X Y = 0 := by
  have e1 : cT (σ : E →+* E) X * J * (X * (cT (σ : E →+* E) Y * J)) = 0 := by
    rw [← Matrix.mul_assoc, hW.xx, Matrix.zero_mul]
  have e2 : cT (σ : E →+* E) X * J * (Y * (cT (σ : E →+* E) X * J)) = cT (σ : E →+* E) X * J := by
    rw [← Matrix.mul_assoc, hW.xy, Matrix.one_mul]
  rw [orthProj, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, e1, e2]
  abel

theorem leviMin_normalises_unipMin (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m : GAd σ J) (hm : m ∈ leviMin σ J X Y)
    (u : GAd σ J) (hu : u ∈ unipMin σ J X) : m⁻¹ * u * m ∈ unipMin σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  obtain ⟨B, hB, hB1, eU, hz⟩ := hu
  have hM := unitaryA_matHom m
  set M := (matHom _ σ J m).1 with hMdef
  set U := (matHom _ σ J u).1 with hUdef
  set Mi := (matHom _ σ J m⁻¹).1 with hMidef
  have hMi : Mi * M = 1 := by
    rw [hMidef, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  obtain ⟨c, hdc⟩ : ∃ c : Fin r → AF F ⊗[F] E, ∀ i, d i * c i = 1 := ⟨_, coef_inv hF hM e e'⟩
  have eMi := inv_mul_frame hMi hdc e
  have hV : (matHom _ σ J (m⁻¹ * u * m)).1 = Mi * U * M := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  refine ⟨diagonal c * B * diagonal d, ((Matrix.blockTriangular_diagonal _).mul hB).mul
    (Matrix.blockTriangular_diagonal _), ?_, ?_, ?_⟩
  · intro i
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hB1, mul_one, mul_comm]
    exact hdc i
  · rw [hV, Matrix.mul_assoc, e, ← Matrix.mul_assoc, Matrix.mul_assoc Mi, eU, ← Matrix.mul_assoc Mi, eMi]
    simp only [Matrix.mul_assoc]
  · intro z hzz
    have hcol : ∀ k, ∃ a, (U - 1) *ᵥ (fun i => ((orthProj σ J X Y).map (inclR (F := F) (AF F))) i k) =
        adMat F X *ᵥ a := by
      intro k
      refine hz (fun i => orthProj σ J X Y i k) ?_
      funext i
      have := congrFun (congrFun (orth_orthProj hW) i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have hv : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) *ᵥ
        (fun i => inclR (F := F) (AF F) (z i)) = 0 := by
      have e1 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J =
          (cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
        unfold JR
        rw [← cT_map_inclR, Matrix.map_mul]
        rfl
      rw [e1]
      funext i
      have := congrArg (inclR (F := F) (AF F)) (congrFun hzz i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul] using this
    obtain ⟨a, ha⟩ := clause_extend hF eU (by
      unfold JR
      rw [← cT_map_inclR, ← cT_map_inclR, orthProj, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]) hcol
      (orth_mulVec hM hdc e hv)
    refine ⟨diagonal c *ᵥ a, ?_⟩
    have e4 : Mi * U * M - 1 = Mi * (U - 1) * M := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hMi]
    rw [hV, e4, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, eMi,
      Matrix.mulVec_mulVec]

end GlobalTheory.CompanionTheory.ParCocompact.UnipNormal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosed
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
  GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviOne

section Frame

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem coef_mul_eq_one (hF : PFr s Jm Xm Ym) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm)
    {d d' : Fin r → R} (e : g * Xm = Xm * diagonal d) (e' : g * Ym = Ym * diagonal d') (i : Fin r) :
    s (d' i) * d i = 1 := by
  have h := hF.inv_coef hg e
  rw [e', ← Matrix.mul_assoc, hF.xy, Matrix.one_mul] at h
  have h2 : cT s (diagonal d') = diagonal (fun i => s (d' i)) := Matrix.ext fun a b => by
    by_cases hab : a = b
    · subst hab
      simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
  rw [h2, diagonal_mul_diagonal] at h
  simpa using congrFun (congrFun h i) i

theorem inv_act {g g' : Matrix (Fin n) (Fin n) R} (hg : g' * g = 1) {d e : Fin r → R}
    (he : ∀ i, e i * d i = 1) (h : g * Xm = Xm * diagonal d) : g' * Xm = Xm * diagonal e := by
  have h1 : diagonal d * diagonal e = (1 : Matrix (Fin r) (Fin r) R) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm, he i]
  calc g' * Xm = g' * (Xm * (diagonal d * diagonal e)) := by rw [h1, Matrix.mul_one]
    _ = g' * g * Xm * diagonal e := by
        rw [← Matrix.mul_assoc Xm, ← h]
        simp only [Matrix.mul_assoc]
    _ = Xm * diagonal e := by rw [hg, Matrix.one_mul]

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem one_mem_minParOne : (1 : GAd σ J) ∈ minParOne σ J X :=
  ⟨1, Matrix.blockTriangular_one, by simp, fun i => ⟨1, by simp, map_one _⟩⟩

theorem mul_mem_levi {a b : GAd σ J} (ha : a ∈ leviMin σ J X Y) (hb : b ∈ leviMin σ J X Y) :
    a * b ∈ leviMin σ J X Y := by
  obtain ⟨d₁, d₁', e₁, e₁'⟩ := ha
  obtain ⟨d₂, d₂', e₂, e₂'⟩ := hb
  refine ⟨d₁ * d₂, d₁' * d₂', ?_, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂, ← Matrix.mul_assoc, e₁, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, e₂', ← Matrix.mul_assoc, e₁', Matrix.mul_assoc,
      diagonal_mul_diagonal]
    rfl

theorem inv_mem (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {m : GAd σ J}
    (hm : m ∈ leviMin σ J X Y) (hm1 : m ∈ minParOne σ J X) :
    m⁻¹ ∈ leviMin σ J X Y ∧ m⁻¹ ∈ minParOne σ J X := by
  have hF := pfrA h hJ hW
  obtain ⟨d, d', e, e'⟩ := hm
  have hu := unitaryA_matHom m
  have h1 := coef_mul_eq_one hF hu e e'
  have hss := hF.ss
  have hinv : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : ∀ i, d i * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d' i) = 1 := fun i => by rw [mul_comm, h1 i]
  have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (d i) * d' i = 1 := coef_mul_eq_one (pfr_swap hF) hu e' e
  have f := inv_act hinv h1 e
  have f' := inv_act hinv h3 e'
  refine ⟨⟨_, _, f, f'⟩, ?_⟩
  obtain ⟨B, -, eB, hB⟩ := hm1
  have hBd : B = diagonal d := by rw [← Bm_eq hF eB, Bm_eq hF e]
  refine ⟨_, Matrix.blockTriangular_diagonal _, f, fun i => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hB i
  refine ⟨u⁻¹, ?_, by rw [map_inv, hu2, inv_one]⟩
  have hd : d i = u := by rw [← hu1, hBd, Matrix.diagonal_apply_eq]
  rw [Matrix.diagonal_apply_eq]
  exact (Units.inv_eq_of_mul_eq_one_left (by rw [← hd]; exact h1 i)).symm ▸ rfl

theorem leviMin_eq (hF : PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (adMat F X) (adMat F Y)) :
    leviMin σ J X Y = {m | (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal (fun i => Bm σ J X Y m i i)} ∩
      {m | (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal (fun i => Bm σ J Y X m i i)} := by
  ext m
  constructor
  · rintro ⟨d, d', e, e'⟩
    have a1 : (fun i => Bm σ J X Y m i i) = d := funext fun i => by
      rw [Bm_eq hF e, Matrix.diagonal_apply_eq]
    have a2 : (fun i => Bm σ J Y X m i i) = d' := funext fun i => by
      rw [Bm_eq (pfr_swap hF) e', Matrix.diagonal_apply_eq]
    exact ⟨by simpa only [Set.mem_setOf_eq, a1] using e, by simpa only [Set.mem_setOf_eq, a2] using e'⟩
  · rintro ⟨e, e'⟩
    exact ⟨_, _, e, e'⟩

theorem isClosed_leviMin (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (leviMin σ J X Y) := by
  have hF := pfrA h hJ hW
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hc : ∀ {X' Y' : Matrix (Fin n) (Fin r) E}, Continuous fun m : GAd σ J =>
      adMat F X' * diagonal (fun i => Bm σ J X' Y' m i i) := fun {X' Y'} => by
    have hd : Continuous fun m : GAd σ J => diagonal (fun i => Bm σ J X' Y' m i i) :=
      continuous_matrix fun a b => by
        by_cases hab : a = b
        · subst hab
          simpa using (continuous_Bm (σ := σ) (J := J) (X := X') (Y := Y')).matrix_elem a a
        · simpa [Matrix.diagonal_apply_ne _ hab] using continuous_const
    exact continuous_const.matrix_mul hd
  rw [leviMin_eq hF]
  exact (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc).inter
    (isClosed_eq ((continuous_matHom_val (σ := σ) (J := J)).matrix_mul continuous_const) hc)

end GlobalTheory.CompanionTheory.ParCocompact.LeviOne


open GlobalTheory.CompanionTheory.ParCocompact.LeviOne in
theorem GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ L : Subgroup (GAd σ J), (L : Set (GAd σ J)) = leviMin σ J X Y ∩ minParOne σ J X ∧ IsClosed (L : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  refine ⟨{ carrier := leviMin σ J X Y ∩ minParOne σ J X
            mul_mem' := fun {a b} ha hb => ⟨mul_mem_levi ha.1 hb.1, (minParOne_props h hJ hW).2 a ha.2 b hb.2⟩
            one_mem' := ⟨one_mem_leviMin σ J X Y, one_mem_minParOne⟩
            inv_mem' := fun {a} ha => inv_mem h hJ hW ha.1 ha.2 }, rfl, ?_⟩
  exact (isClosed_leviMin h hJ hW).inter (minParOne_props h hJ hW).1

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalFormStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singular_hermitian_congruent_block_normal_form : ∀ (D : D7) (r : ℕ) (β : HermE D r), β.1.det = 0 → ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r), a.det ≠ 0 ∧ GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t γ ∧ β = GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a γ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF <;> assumption)
end

