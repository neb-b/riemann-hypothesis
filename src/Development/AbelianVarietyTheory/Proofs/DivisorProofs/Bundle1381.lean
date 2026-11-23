module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceComplexStructureSigna
section
noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD GlobalTheory.VacBridge

namespace GlobalTheory.HoweD

theorem exists_bridgeD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (AE F E)) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a b A C ε hcm hfr
  have := hcm.1
  obtain ⟨-, hA, hC⟩ := hfr
  choose IA hIA using fun w =>
    frame_inv _ (A w) (Jm (P w) (Q w)) (jm_mul_self (P w) (Q w)) (hA w).1 (hA w).2
  choose IC hIC using fun w =>
    frame_inv _ (C w) (Jm (R w) (S w)) (jm_mul_self (R w) (S w)) (hC w).1 (hC w).2
  have hback : ∀ w (X : Matrix α β ℂ), A w * (IA w * X * (IC w)ᵀ) * (C w)ᵀ = X := by
    intro w X
    have hCt : (IC w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hIC w).2, Matrix.transpose_one]
    calc _ = (A w * IA w) * X * ((IC w)ᵀ * (C w)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [(hIA w).2, hCt, Matrix.one_mul, Matrix.mul_one]
  have hfwd : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), IA w * (A w * c * (C w)ᵀ) * (IC w)ᵀ = c := by
    intro w c
    have hCt : (C w)ᵀ * (IC w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hIC w).1, Matrix.transpose_one]
    calc _ = (IA w * A w) * c * ((C w)ᵀ * (IC w)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = c := by rw [(hIA w).1, hCt, Matrix.one_mul, Matrix.mul_one]
  let Ψl : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun y w => IA w * (mkD d y).map (piInf (τ w)) * (IC w)ᵀ
      map_add' := fun y y' => by
        funext w
        simp only [mkD_add, Pi.add_apply]
        rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r y => by
        funext w
        simp only [mkD_smul_real, map_smul_piInf, ext_realAd, RingHom.id_apply, Pi.smul_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul]
        ext i j
        simp [Complex.real_smul] }
  have hΨl : ∀ y w, A w * Ψl y w * (C w)ᵀ = (mkD d y).map (piInf (τ w)) := fun y w => hback w _
  have hinj : Function.Injective Ψl := by
    intro y y' h
    have hu : mkD d y = mkD d y' := eq_of_at_map σ hcm τ (at_mkD d y) (at_mkD d y') fun w => by
      rw [← hΨl, ← hΨl, h]
    rw [← coord_mkD d y, ← coord_mkD d y', hu]
  have hsurj : Function.Surjective Ψl := by
    intro c
    obtain ⟨u, hu, hM⟩ := exists_at_map σ hcm τ (fun w => A w * c w * (C w)ᵀ)
    refine ⟨coord d u, funext fun w => ?_⟩
    show IA w * (mkD d (coord d u)).map (piInf (τ w)) * (IC w)ᵀ = c w
    rw [mkD_coord d hu, hM w, hfwd]
  let Ψ := LinearEquiv.ofBijective Ψl ⟨hinj, hsurj⟩
  let L : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
        exact smul_comm _ _ _ }
  let Pm : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => (if ε w = -1 then (1 : ℂ) else 0) • c w
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hLL : ∀ c, L (L c) = -c := by
    intro c
    funext w
    show Complex.I • (Jm (P w) (Q w) * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * Jm (R w) (S w)) = -c w
    have key : Jm (P w) (Q w) * (Jm (P w) (Q w) * c w * Jm (R w) (S w)) * Jm (R w) (S w) = c w := by
      calc _ = (Jm (P w) (Q w) * Jm (P w) (Q w)) * c w * (Jm (R w) (S w) * Jm (R w) (S w)) := by
            simp only [Matrix.mul_assoc]
        _ = c w := by rw [jm_mul_self, jm_mul_self, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, key, Complex.I_mul_I, neg_one_smul]
  have hLP : ∀ c, L (Pm c) = Pm (L c) := by
    intro c
    funext w
    show Complex.I • (Jm (P w) (Q w) * ((if ε w = -1 then (1 : ℂ) else 0) • c w) * Jm (R w) (S w)) =
      (if ε w = -1 then (1 : ℂ) else 0) • (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w)))
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  let tm : AF F := ((fun w => if ε w = -1 then 1 else 0 : InfiniteAdeleRing F), 0)
  have htm : tm * tm = tm := by
    refine Prod.ext (funext fun w => ?_) ?_
    · show (if ε w = -1 then (1 : w.Completion) else 0) * (if ε w = -1 then 1 else 0) = if ε w = -1 then 1 else 0
      split_ifs <;> simp
    · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * 0 = 0
      exact mul_zero _
  have htt : evI F tm * evI F tm = evI F tm := by rw [← evI_mul, htm]
  have hext : ∀ w, InfinitePlace.Completion.extensionEmbedding w (tm.1 w) = if ε w = -1 then 1 else 0 := by
    intro w
    show InfinitePlace.Completion.extensionEmbedding w (if ε w = -1 then (1 : w.Completion) else 0) = _
    split_ifs <;> simp
  have hΨe : ∀ y, Ψl (mulP (evI F tm) y) = Pm (Ψl y) := by
    intro y
    funext w
    show IA w * (mkD d (mulP (evI F tm) y)).map (piInf (τ w)) * (IC w)ᵀ =
      (if ε w = -1 then (1 : ℂ) else 0) • (IA w * (mkD d y).map (piInf (τ w)) * (IC w)ᵀ)
    rw [mkD_mulP, map_smul_piInf, hext, Matrix.mul_smul, Matrix.smul_mul]
  let J : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    (Ψ.symm : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] _).comp (L.comp Ψl)
  have hΨJ : ∀ y, Ψl (J y) = L (Ψl y) := fun y => Ψ.apply_symm_apply _
  refine ⟨J, mulP (evI F tm), mulC (evI F tm), ?_, ?_, ?_, fun y => rfl, ?_, ?_⟩
  · intro y
    apply hinj
    rw [hΨJ, hΨJ, hLL, map_neg]
  · intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show evI F tm * (evI F tm * y.1 i) = evI F tm * y.1 i
      rw [← mul_assoc, htt]
    · show evI F tm * (evI F tm * y.2 i) = evI F tm * y.2 i
      rw [← mul_assoc, htt]
  · intro y
    apply hinj
    rw [hΨJ, hΨe, hΨe, hΨJ, hLP]
  · intro y x
    simp only [trPair_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show x i * (evI F tm * y.2 i) = (evI F tm * x i) * y.2 i
    ring
  · intro y
    refine ⟨mkD d y, mkD d (J (y - (2 : ℝ) • mulP (evI F tm) y)), mkD d (J y), Ψl y, at_mkD d _, at_mkD d _,
      at_mkD d _, fun w => (hΨl y w).symm, fun w => ?_, fun w => ?_, coord_mkD d _, coord_mkD d _, coord_mkD d _⟩
    · rw [← hΨl, hΨJ, map_sub, map_smul, hΨe]
      show A w * (Complex.I • (Jm (P w) (Q w) * (Ψl y w - (2 : ℝ) • ((if ε w = -1 then (1 : ℂ) else 0) • Ψl y w)) *
          Jm (R w) (S w))) * (C w)ᵀ =
        A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * Ψl y w * Jm (R w) (S w))) * (C w)ᵀ
      congr 2
      generalize Ψl y w = X
      rcases Int.units_eq_one_or (ε w) with h1 | h1
      · rw [h1, if_neg (by decide)]
        simp
      · rw [h1, if_pos rfl, one_smul, two_smul, sub_add_cancel_left]
        simp [Matrix.mul_neg, Matrix.neg_mul]
    · rw [← hΨl, hΨJ]
      rfl

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct
open Matrix
open Formalism.UG (cT)

namespace GlobalTheory.BlockFormsEmb

section Alg
variable {R : Type} [CommRing R] {n d : ℕ}

theorem cT_add' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A + B) = cT s A + cT s B :=
  Matrix.ext fun i j => by simp [cT]

theorem cT_sub' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A - B) = cT s A - cT s B :=
  Matrix.ext fun i j => by simp [cT]

def blk (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) R := 1 + a * (H - 1) * α + b * (K - 1) * β

variable {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}

theorem blk_one : blk a b α β 1 1 = 1 := by simp [blk]

theorem blk_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (H K H' K' : Matrix (Fin d) (Fin d) R) :
    blk a b α β H K * blk a b α β H' K' = blk a b α β (H * H') (K * K') := by
  first
  | exact @_root_.GlobalTheory.SquareDistanceExpansion.main
  | exact _root_.GlobalTheory.SquareDistanceExpansion.main
  | (apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareDistanceExpansion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareDistanceExpansion.main ..)

theorem blk_unitary (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R)
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT s α = Jm * b) (hβ : cT s β = Jm * a) (ha : cT s a * Jm = β) (hb : cT s b * Jm = α)
    (H K : Matrix (Fin d) (Fin d) R) (h1 : cT s K * H = 1) (h2 : cT s H * K = 1) :
    cT s (blk a b α β H K) * Jm * blk a b α β H K = Jm := by
  have key : cT s (blk a b α β H K) * Jm = Jm * blk a b α β (cT s K) (cT s H) := by
    unfold blk
    rw [cT_add', cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_sub', cT_sub',
      Formalism.UG.cT_one, hα, hβ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, ha, hb]
    abel
  rw [key, Matrix.mul_assoc, blk_mul hαa hβb hαb hβa, h1, h2, blk_one, Matrix.mul_one]

end Alg

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.BlockForms

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [sigR, inclR]

theorem cT_adMat (σ : E →ₐ[F] E) {m p : Type} (Z : Matrix m p E) :
    cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
  Matrix.ext fun i j => by simp only [cT, adMat, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]; rfl

theorem adMat_mul' {m p q : Type} [Fintype p] (A : Matrix m p E) (B : Matrix p q E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {m : Type} [Fintype m] [DecidableEq m] : adMat F (1 : Matrix m m E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_zero' {m p : Type} : adMat F (0 : Matrix m p E) = 0 := Matrix.map_zero _ (map_zero _)

theorem sigR_sigR' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem blkCols_gram {n r l d : ℕ} (h : l + d ≤ r) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (Z W : Matrix (Fin n) (Fin r) E) :
    cT (σ : E →+* E) (blkCols h Z) * J * blkCols h W =
      (cT (σ : E →+* E) Z * J * W).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
        (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := by
  first
  | rfl
  | (ext i j; simp [Matrix.mul_apply, blkCols, cT])

def embMat (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
    (a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E))
    (g : GlobalTheory.CuspRep.GA E d) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  blk a b α β (g.1.map Φ.symm) (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm))

variable (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
  {a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)} {α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E)}

theorem map_symm_mul (A B : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)) :
    (A * B).map Φ.symm = A.map Φ.symm * B.map Φ.symm := Matrix.map_mul (f := Φ.symm.toRingHom)

theorem map_symm_one : (1 : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)).map Φ.symm = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem embMat_one : embMat σ Φ a b α β 1 = 1 := by
  simp only [embMat, inv_one, Units.val_one, map_symm_one, Formalism.UG.cT_one, blk_one]

theorem embMat_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (g g' : GlobalTheory.CuspRep.GA E d) : embMat σ Φ a b α β (g * g') = embMat σ Φ a b α β g * embMat σ Φ a b α β g' := by
  unfold embMat
  rw [blk_mul hαa hβb hαb hβa, Units.val_mul, _root_.mul_inv_rev, Units.val_mul, map_symm_mul, map_symm_mul, Formalism.UG.cT_mul]

theorem embMat_unitary (hσ : ∀ x, σ (σ x) = x) (Jm : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT (sigR (AF F) σ) α = Jm * b) (hβ : cT (sigR (AF F) σ) β = Jm * a)
    (ha : cT (sigR (AF F) σ) a * Jm = β) (hb : cT (sigR (AF F) σ) b * Jm = α) (g : GlobalTheory.CuspRep.GA E d) :
    cT (sigR (AF F) σ) (embMat σ Φ a b α β g) * Jm * embMat σ Φ a b α β g = Jm := by
  have hcc : ∀ A : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), cT (sigR (AF F) σ) (cT (sigR (AF F) σ) A) = A :=
    fun A => Matrix.ext fun i j => by simp only [cT, Matrix.transpose_apply, Matrix.map_apply]; exact sigR_sigR' σ hσ _
  have hgg : (g⁻¹).1.map Φ.symm * g.1.map Φ.symm = 1 := by
    rw [← map_symm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_symm_one]
  unfold embMat
  refine blk_unitary _ Jm hαa hβb hαb hβa hα hβ ha hb _ _ ?_ ?_
  · rw [hcc, hgg]
  · rw [← Formalism.UG.cT_mul, hgg, Formalism.UG.cT_one]

end Main

theorem exists_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (l d : ℕ) (h : l + d ≤ r), ∃ ι : GlobalTheory.CuspRep.GA E d →* GAd σ J, GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW l d h
  obtain ⟨Φ, j, hc1, hc2, hj, hΦ⟩ := GlobalTheory.HeckeBridge.exists_tensor_adele_equiv F E σ hcm
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJT : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : ∀ {m p : Type} (Z : Matrix m p E), cT (σ : E →+* E) (cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun _ _ => hσ _
  have hyx : cT (σ : E →+* E) Yf * J * Xf = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcc, hJT, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have he : Function.Injective (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := fun i k e =>
    Fin.ext (by have := congrArg Fin.val e; simp only at this; omega)
  have q1 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Xf = 1 := by
    rw [blkCols_gram, hyx, Matrix.submatrix_one _ he]
  have q2 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Yf = 1 := by
    rw [blkCols_gram, hW.xy, Matrix.submatrix_one _ he]
  have q3 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Yf = 0 := by
    rw [blkCols_gram, hW.yy, Matrix.submatrix_zero]; rfl
  have q4 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Xf = 0 := by
    rw [blkCols_gram, hW.xx, Matrix.submatrix_zero]; rfl
  have hαa : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Xf) = 1 := by
    rw [← adMat_mul', q1, adMat_one']
  have hβb : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Yf) = 1 := by
    rw [← adMat_mul', q2, adMat_one']
  have hαb : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Yf) = 0 := by
    rw [← adMat_mul', q3, adMat_zero']
  have hβa : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Xf) = 0 := by
    rw [← adMat_mul', q4, adMat_zero']
  have hα : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) = adMat F J * adMat F (blkCols h Yf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have hβ : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J)) = adMat F J * adMat F (blkCols h Xf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have ha : cT (sigR (AF F) σ) (adMat F (blkCols h Xf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  have hb : cT (sigR (AF F) σ) (adMat F (blkCols h Yf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  let M := embMat σ Φ (adMat F (blkCols h Xf)) (adMat F (blkCols h Yf))
    (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J))
  have hMmul : ∀ g g', M (g * g') = M g * M g' := embMat_mul σ Φ hαa hβb hαb hβa
  have hMone : M 1 = 1 := embMat_one σ Φ
  have hMu : ∀ g, cT (sigR (AF F) σ) (M g) * JR (AF F) J * M g = JR (AF F) J :=
    embMat_unitary σ Φ hσ (adMat F J) hαa hβb hαb hβa hα hβ ha hb
  let U : GlobalTheory.CuspRep.GA E d → GL (Fin n) (AF F ⊗[F] E) := fun g =>
    ⟨M g, M g⁻¹, by rw [← hMmul, mul_inv_cancel, hMone], by rw [← hMmul, inv_mul_cancel, hMone]⟩
  let ι : GlobalTheory.CuspRep.GA E d →* GAd σ J :=
    { toFun := fun g => (⟨U g, hMu g⟩ : HR (AF F) σ J)
      map_one' := Subtype.ext (Units.ext hMone)
      map_mul' := fun g g' => Subtype.ext (Units.ext (hMmul g g')) }
  exact ⟨ι, Φ, j, hc1, hc2, hj, hΦ, fun g => rfl⟩

end GlobalTheory.BlockFormsEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizer
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.CptTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twCent_commute (hE : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) {g : GLw n w}
    (hg : g ∈ twCent (thL n w) y) : Commute g (nrmL n w y) := by
  have hinv : ∀ x, thL n w (thL n w x) = x := (GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE n w).2.1
  have hg' : g * y = y * thL n w g := hg
  unfold nrmL
  split_ifs with hs
  · have ht : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    rw [ht] at hg'
    exact hg'
  · have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
    rw [ht] at hg' hinv
    show g * (y * thetaGL n (cj w) y) = (y * thetaGL n (cj w) y) * g
    calc g * (y * thetaGL n (cj w) y) = (g * y) * thetaGL n (cj w) y := by rw [mul_assoc]
      _ = y * (thetaGL n (cj w) g * thetaGL n (cj w) y) := by rw [hg', mul_assoc]
      _ = y * thetaGL n (cj w) (g * y) := by rw [map_mul]
      _ = y * thetaGL n (cj w) (y * thetaGL n (cj w) g) := by rw [hg']
      _ = (y * thetaGL n (cj w) y) * g := by rw [map_mul, hinv, mul_assoc]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w),
    (nrmL n w y).val.charpoly.Separable →
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  intro E _ _ _ hE n w y hs
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.LocBounded.bounded_of_isIntegral E w n N hs
  have hB := _root_.GlobalTheory.BoundedGL.isCompact_bounded E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨twCent_commute hE n w y ht, htc⟩

end GlobalTheory.CptTorus
end
end

