module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | exact GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split | (intros; apply GlobalTheory.DblVacSiegelAny.eigen_eq_one_of_diag_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UnitaryEmbeddingLine

variable {D : D7}

theorem tmul_mul_inc (α : AF D.host.F) (b x : D.host.E) :
    (α ⊗ₜ[D.host.F] b : AE D) * incA D x = α ⊗ₜ[D.host.F] (b * x) := by
  change (α ⊗ₜ[D.host.F] b) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem exists_coeff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (p : Fin c) :
    ∃ r : Fin B.rank → D.host.E, ∀ (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E),
      r ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = u p := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have h2 : (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 := d.perp
  have h3 : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at this
    exact this
  have hκ : antiDiagonalSignGramMatrix c ε p.rev p ≠ 0 := by
    have := p.2
    have e : p.rev.1 + p.1 + 1 = c := by rw [Fin.val_rev]; omega
    simp only [antiDiagonalSignGramMatrix, if_pos e]
    split_ifs
    · exact hε
    · exact one_ne_zero
  refine ⟨(antiDiagonalSignGramMatrix c ε p.rev p)⁻¹ • (d.aᴴ * B.gram) p.rev, fun y u => ?_⟩
  have e : (d.aᴴ * B.gram) p.rev ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) =
      ((d.aᴴ * B.gram) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u)) p.rev := rfl
  rw [smul_dotProduct, e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h3, zero_mulVec, zero_add]
  have e2 : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = antiDiagonalSignGramMatrix c ε p.rev p * u p := by
    show ∑ q, antiDiagonalSignGramMatrix c ε p.rev q * u q = _
    refine Finset.sum_eq_single p (fun q _ hq => ?_) (by simp)
    have := p.2
    have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
      intro h; apply hq; apply Fin.ext; rw [Fin.val_rev] at h; omega
    simp only [antiDiagonalSignGramMatrix, if_neg hne, zero_mul]
  rw [e2, smul_eq_mul, inv_mul_cancel_left₀ hκ]

def formHom {R : Type} [CommRing R] {n : ℕ} (r : Fin n → R) : (Fin n → R) →+ R where
  toFun y := ∑ k, y k * r k
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

def lineHom {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) : R →+ (Fin n → R) where
  toFun s := fun k => s * a k
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp only [Pi.add_apply, add_mul]

theorem form_line {K R : Type} [CommRing K] [CommRing R] (f : K →+* R) {n : ℕ} (r a : Fin n → K) (h : r ⬝ᵥ a = 1) (s : R) :
    formHom (fun k => f (r k)) (fun k => s * f (a k)) = s := by
  show ∑ k, s * f (a k) * f (r k) = s
  simp only [mul_assoc, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.mul_sum, ← map_sum]
  have : ∑ k, a k * r k = 1 := by
    rw [← h, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this, map_one, mul_one]

theorem col_eq {K : Type} [CommRing K] {n k c : ℕ} (M : Matrix (Fin n) (Fin k) K) (a : Matrix (Fin n) (Fin c) K) (p : Fin c)
    (b : K) : (fun i => b * a i p) = M *ᵥ 0 + a *ᵥ Pi.single p b := by
  funext k; simp [mul_comm]

theorem line_mp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I) (s : AE D)
    (h : (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)) : s ∈ GlobalTheory.SeeSaw.idV I v := by
  obtain ⟨r, hr⟩ := exists_coeff d hε p
  have key : GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ≤ (GlobalTheory.SeeSaw.idV I v).comap (formHom fun k => incA D (r k)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, a, ha, x, ⟨y0, -, u, hu, hx⟩, rfl⟩
    have e : ∑ k, ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x k) : AE D) * incA D (r k) =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) := by
      rw [Finset.sum_congr rfl fun k _ => tmul_mul_inc (pairA D.host.F 0 α) (a * x k) (r k),
        ← TensorProduct.tmul_sum, ← hr y0 u, ← hx, dotProduct, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    have h2 : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) ∈ GlobalTheory.SeeSaw.idV I v :=
      AddSubgroup.subset_closure ⟨α, hα, hαv, _, hI a ha _ (hu p), rfl⟩
    rw [← e] at h2
    exact h2
  have h1 := hr 0 (Pi.single p 1)
  rw [← col_eq, Pi.single_eq_same] at h1
  simp only [one_mul] at h1
  have := AddSubgroup.mem_comap.1 (key h)
  rwa [form_line (incA D) r (fun k => d.a k p) h1 s] at this

theorem line_mpr {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) (h : s ∈ GlobalTheory.SeeSaw.idV I v) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) := by
  have key : GlobalTheory.SeeSaw.idV I v ≤ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, z, hz, rfl⟩
    refine hI' (fun z => ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] z : AE D) ∈
      (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))) ?_ ?_ z hz
    · intro a ha b hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, fun k => b * d.a k p,
        ⟨0, Λ.zero_mem, Pi.single p b, fun q => ?_, col_eq _ _ p b⟩, ?_⟩)
      · by_cases hq : q = p
        · subst hq; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
      · funext k
        exact (tmul_mul_inc _ _ _).trans (congrArg _ (mul_assoc _ _ _))
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
  exact AddSubgroup.mem_comap.1 (key h)

theorem line_gen {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV I v :=
  ⟨line_mp d Λ 𝔟 p v S I hε hI s, line_mpr d Λ 𝔟 p v S I hI' s⟩

theorem embedding_line_mem_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  intro D A B c ε d hε Λ 𝔟 p v s
  refine ⟨line_gen d Λ 𝔟 p v {1} (𝔟 p) hε ?_ ?_ s, line_gen d Λ 𝔟 p v {a | a ∈ D.host.AA} _ hε ?_ ?_ s⟩
  · rintro a rfl b hb; rwa [one_mul]
  · intro C h _ z hz
    have := h 1 rfl z hz
    rwa [one_mul] at this
  · intro a ha b hb; exact FractionalIdeal.mul_mem_mul ha hb
  · intro C h h' z hz
    exact FractionalIdeal.mul_induction_on hz h h'

end GlobalTheory.AscFin.UnitaryEmbeddingLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  first | exact @GlobalTheory.PlaceCut.exists_cut | exact GlobalTheory.PlaceCut.exists_cut | (intros; apply GlobalTheory.PlaceCut.exists_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitSign.exists_split_sign | exact GlobalTheory.SplitSign.exists_split_sign | (intros; apply GlobalTheory.SplitSign.exists_split_sign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOperatorWeilRepPureTensor
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical


open GlobalTheory.ArchFactor in
theorem GlobalTheory.ArchFactorPair.exists_archOperator_pair :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (T f) := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hweil h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om (1, h) Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hcomm := comm_offI hweil (1, h) h1 hh
  obtain ⟨R, hR0, hR⟩ := _root_.GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d),
      ∀ t, g t = (R 0)⁻¹ * om (1, h) (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.ArchSlice.exists_schwartz_slice _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
    exact ⟨g, fun t => by rw [hg]; rfl⟩
  choose Tf hTf using hB
  have htens_add : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R := by
    intro f g; funext x; simp only [tens, SchwartzMap.add_apply, Pi.add_apply]; ring
  have htens_smul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R := by
    intro c f; funext x; simp only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) :=
    { toFun := Tf
      map_add' := fun f g => by
        ext t
        rw [SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add (f := _), Pi.add_apply]; ring
      map_smul' := fun c f => by
        ext t
        rw [SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]; ring }
  refine ⟨T, fun f r hr => ?_⟩
  funext y
  set T0 := om (1, h) with hT0
  set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  set p : Fin n × Fin d → AF F := liftI (fun i => evI F (y i)) with hpdef
  have hyp : y + u • (-y) = p := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI,
      RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 * (-(y i)).1 = (y i).1
      simp
    · show (y i).2 + 1 * (-(y i)).2 = 0
      rw [one_mul]
      exact add_neg_cancel ((y i).2)
  have hpat : At (evI F) p := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (p i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (p i).2 = 0
      simp [hpdef, liftI]
  set Φ₀ := tens (evI F) (⇑f) R with hΦ₀
  set Φ₁ := tens (evI F) (⇑f) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR f).2
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
    have hpz : At (evI F) (p + z) := fun u' hu' => by
      rw [smul_add, hpat u' hu', hz u' hu', add_zero]
    have e3 : R (p + z) = R 0 := by simpa using (hR f).1 0 (p + z) hpz
    have e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e4, e2, e3, e1]
    field_simp
    ring
  have h0 := _root_.GlobalTheory.FinFibre.fibre_zero ψ T0 hstd hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
    (sub_mem hr.2 hm₂) y hfz
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y)) := by
    have h := hcomm u hu (-y) 0 Φ₀ hm₀
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  have h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p := by
    rw [hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]
  show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y
  rw [h0, h2]
  show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y
  rw [hTf]
  show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y
  rw [div_eq_mul_inv]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteSupportMulLatticeStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TruncAway

open GlobalTheory.AdelicU

theorem exists_trunc_mul_inK : ∀ {D : D7} (V : HSp D) (L : GlobalTheory.FinPl.Lat V), L.FG → Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (b : GA D V), ∃ (b' : GA D V) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b' = 1) ∧ GlobalTheory.FinPl.InK V L (fun v => v ∉ S) (b'⁻¹ * b) := by
  intro D V L hfg hspan S b
  haveI : Submodule.IsLattice D.host.E L := Submodule.IsLattice.of_fg _ hfg
  haveI : Submodule.IsFullLattice D.host.E L := ⟨hspan⟩
  have hfin := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram L b)
  classical
  let P : Finset (HeightOneSpectrum (𝓞 D.host.F)) := S ∪ hfin.toFinset
  let b' : GA D V := ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram b) *
    embAt D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b)
  have hat := mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram P (projAt D.sp.cm.sig V.gram P b))
  have hout : ∀ v ∉ P, proj D.sp.cm.sig V.gram v b' = 1 := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact hat.2 v hv
  have hin : ∀ v ∈ P, proj D.sp.cm.sig V.gram v b' = proj D.sp.cm.sig V.gram v b := fun v hv => by
    simp only [b', map_mul, proj_ofInf, one_mul]
    exact proj_embAt D.sp.cm.sig V.gram P _ ⟨v, hv⟩
  have hinf : projInf D.sp.cm.sig V.gram b' = projInf D.sp.cm.sig V.gram b := by
    simp only [b', map_mul, projInf_ofInf, mem_finPts.1 hat.1, mul_one]
  refine ⟨b', P, hout, ?_, ?_⟩
  · rw [GlobalTheory.FinPl.KOpen.mem_grpAt_iff]
    refine ⟨mem_finPts.2 ?_, fun v hv => ?_⟩
    · rw [map_mul, map_inv, hinf, inv_mul_cancel]
    · have hvP : v ∈ P := Finset.mem_union_left _ (not_not.1 hv)
      rw [map_mul, map_inv, hin v hvP, inv_mul_cancel]
  · refine GlobalTheory.FinPl.KOpen.moves_of_levelOpen V L hfg _ (mem_levelOpen.2 fun v => ?_)
    by_cases hv : v ∈ P
    · rw [map_mul, map_inv, hin v hv, inv_mul_cancel]; exact one_mem _
    · rw [map_mul, map_inv, hout v hv, inv_one, one_mul]
      by_contra h
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))

end GlobalTheory.TruncAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodRationalSchroedingerModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree


open Classical in
theorem exists_good_model : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ {n d : ℕ} (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
    V.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
    ∀ (μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)) (dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)),
      μ.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig V.J) dom μ →
    ∃ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws, M.μ = μ ∧ M.dom = dom ∧ M.IsGood Bs.ψ := by
  intro D Bs hB n d V Ws r s r' s' hV hW μ dom hμ hdom
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig Bs V Ws r s r' s' hB hV hW
  let M0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws := ⟨co, fun _ => 0, μ, dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  have hc := _root_.GlobalTheory.StdVacuum.eventually_isVac_indicator D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin n × Fin d → Fv D.host.F v) → ℂ := fun v =>
    Set.indicator {x : Fin n × Fin d → Fv D.host.F v | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  refine ⟨⟨co, fun v => if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose, μ, dom⟩, rfl, rfl, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hμ, hdom⟩
  · change M0.IsVac Bs.ψ v (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose)
    split_ifs with h
    · exact h
    · exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    change (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose) = ind v
    exact if_pos hv

end GlobalTheory.SquareAgree
end

