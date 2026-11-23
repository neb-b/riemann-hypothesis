module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIsometryIsotropicFrameLocalRing
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.WittFrame

open Matrix

variable {O : Type} [CommRing O]

theorem cT_mul_r (s : O →+* O) {a b c : Type} [Fintype b] (M : Matrix a b O) (N : Matrix b c O) :
    Formalism.UG.cT s (M * N) = Formalism.UG.cT s N * Formalism.UG.cT s M := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_r (s : O →+* O) {a : Type} [DecidableEq a] : Formalism.UG.cT s (1 : Matrix a a O) = 1 := by
  ext i j; by_cases h : i = j <;> simp [Formalism.UG.cT, Matrix.one_apply, h, eq_comm]

theorem cT_zero_r (s : O →+* O) {a b : Type} : Formalism.UG.cT s (0 : Matrix a b O) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub_r (s : O →+* O) {a b : Type} (M N : Matrix a b O) :
    Formalism.UG.cT s (M - N) = Formalism.UG.cT s M - Formalism.UG.cT s N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT_r {s : O →+* O} (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b O) :
    Formalism.UG.cT s (Formalism.UG.cT s M) = M := by
  ext i j; exact hs _

theorem cT_fromCols_r (s : O →+* O) {a b c : Type} (X : Matrix a b O) (Y : Matrix a c O) :
    Formalism.UG.cT s (fromCols X Y) = fromRows (Formalism.UG.cT s X) (Formalism.UG.cT s Y) := by
  ext (i | i) j <;> rfl

theorem assoc3 {a b c d : Type} [Fintype b] [Fintype c] {X : Matrix a b O} {Y : Matrix b c O}
    {Z : Matrix c d O} {V : Matrix a d O} (h : X * Y * Z = V) : X * (Y * Z) = V := by
  rw [← Matrix.mul_assoc, h]

theorem tail3 {a b c d : Type} [Fintype b] [Fintype c] [Fintype d] {X : Matrix a b O} {Y : Matrix b c O}
    {Z : Matrix c d O} {V : Matrix a d O} (h : X * Y * Z = V) {p : Type} (W : Matrix d p O) :
    X * (Y * (Z * W)) = V * W := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

theorem tail2 {a b c : Type} [Fintype b] [Fintype c] {X : Matrix a b O} {Y : Matrix b c O}
    {V : Matrix a c O} (h : X * Y = V) {p : Type} (W : Matrix c p O) : X * (Y * W) = V * W := by
  rw [← Matrix.mul_assoc, h]

theorem idem_factor [IsLocalRing O] {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι O) (hP : P * P = P) :
    ∃ (m : ℕ) (B : Matrix ι (Fin m) O) (B' : Matrix (Fin m) ι O), B' * B = 1 ∧ B * B' = P := by
  have hfix : ∀ y ∈ LinearMap.range (Matrix.mulVecLin P), P *ᵥ y = y := by
    rintro y ⟨w, rfl⟩
    show P *ᵥ (P *ᵥ w) = P *ᵥ w
    rw [mulVec_mulVec, hP]
  haveI : Module.Projective O (LinearMap.range (Matrix.mulVecLin P)) := by
    refine Module.Projective.of_split (LinearMap.range (Matrix.mulVecLin P)).subtype
      (Matrix.mulVecLin P).rangeRestrict ?_
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact hfix _ x.2
  haveI : Module.Free O (LinearMap.range (Matrix.mulVecLin P)) := Module.free_of_flat_of_isLocalRing
  set b := Module.finBasis O (LinearMap.range (Matrix.mulVecLin P)) with hb
  have hmul : ∀ c : Fin _ → O, (Matrix.of fun x i => (b i : ι → O) x) *ᵥ c =
      ((b.equivFun.symm c : LinearMap.range (Matrix.mulVecLin P)) : ι → O) := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    funext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hres : ∀ y : LinearMap.range (Matrix.mulVecLin P), (Matrix.mulVecLin P).rangeRestrict (y : ι → O) = y :=
    fun y => Subtype.ext (hfix _ y.2)
  refine ⟨_, Matrix.of fun x i => (b i : ι → O) x,
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ (Matrix.mulVecLin P).rangeRestrict), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro c
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply,
      hmul, LinearMap.comp_apply, hres]
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply, hmul,
      LinearMap.comp_apply]
    simp

theorem card_eq_of_inv [Nontrivial O] {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {S : Matrix b a O} {T : Matrix a b O} (h1 : S * T = 1) (h2 : T * S = 1) : Fintype.card a = Fintype.card b := by
  let e : (b → O) ≃ₗ[O] (a → O) := LinearEquiv.ofLinear (Matrix.toLin' T) (Matrix.toLin' S)
    (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
  have := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem exists_completion [IsLocalRing O] {s : O →+* O} (hs : ∀ x, s (s x) = x) {τ : O} (hτ : τ + s τ = 1)
    (hnorm : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u)
    {n r : ℕ} {Q : Matrix (Fin n) (Fin n) O} (hQ : Formalism.UG.cT s Q = Q) (hu : IsUnit Q)
    {C : Matrix (Fin n) (Fin r) O} {L : Matrix (Fin r) (Fin n) O} (hL : L * C = 1)
    (hC : Formalism.UG.cT s C * Q * C = 0) :
    ∃ (m : ℕ) (T : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) O) (S : Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) (Fin n) O),
      S * T = 1 ∧ T * S = 1 ∧
      Formalism.UG.cT s T * Q * T = fromBlocks (fromBlocks 0 1 1 0) 0 0 1 ∧
      T * (fromRows (fromRows (1 : Matrix (Fin r) (Fin r) O) 0) (0 : Matrix (Fin m) (Fin r) O) :
        Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) (Fin r) O) = C := by
  obtain ⟨Z, h1, h2, h3⟩ := GlobalTheory.InertIwasawa.exists_dual_isotropic hs hτ hQ hu hL hC
  have key : ∀ {a b : Type} [Fintype a] [Fintype b] (X : Matrix (Fin n) a O) (X' : Matrix (Fin n) b O),
      Formalism.UG.cT s (Formalism.UG.cT s X * Q * X') = Formalism.UG.cT s X' * Q * X := fun X X' => by
    rw [cT_mul_r, cT_mul_r, cT_cT_r hs, hQ, Matrix.mul_assoc]
  obtain ⟨π, hπ⟩ : ∃ π : Matrix (Fin n) (Fin n) O,
      π = 1 - C * (Formalism.UG.cT s Z * Q) - Z * (Formalism.UG.cT s C * Q) := ⟨_, rfl⟩
  have hπC : π * C = 0 := by
    rw [hπ]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, assoc3 h2, assoc3 hC, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have hπZ : π * Z = 0 := by
    rw [hπ]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, assoc3 h3, assoc3 h1, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have hCπ : Formalism.UG.cT s C * Q * π = 0 := by
    rw [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, tail3 hC, tail3 h1, Matrix.zero_mul,
      Matrix.one_mul, sub_zero, sub_self]
  have hZπ : Formalism.UG.cT s Z * Q * π = 0 := by
    rw [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, tail3 h2, tail3 h3, Matrix.zero_mul,
      Matrix.one_mul, sub_zero, sub_self]
  have hππ : π * π = π := by
    nth_rewrite 2 [hπ]
    simp only [Matrix.mul_sub, Matrix.mul_one, tail2 hπC, tail2 hπZ, Matrix.zero_mul, sub_zero]
  have hπQ : Formalism.UG.cT s π * Q = Q * π := by
    rw [hπ]
    simp only [cT_sub_r, cT_one_r, cT_mul_r, cT_cT_r hs, hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
    abel
  obtain ⟨m, B0, B0', hB0, hB0π⟩ := idem_factor π hππ
  have hBπ0 : π * B0 = B0 := by rw [← hB0π, Matrix.mul_assoc, hB0, Matrix.mul_one]
  have hG : Formalism.UG.cT s B0 * Q * B0 * (B0' * (hu.unit⁻¹).1 * Formalism.UG.cT s B0') = 1 := by
    calc Formalism.UG.cT s B0 * Q * B0 * (B0' * (hu.unit⁻¹).1 * Formalism.UG.cT s B0')
          = Formalism.UG.cT s B0 * (Q * π) * (hu.unit⁻¹).1 * Formalism.UG.cT s B0' := by
            rw [← hB0π]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s B0 * Formalism.UG.cT s π * (Q * (hu.unit⁻¹).1) * Formalism.UG.cT s B0' := by
            rw [← hπQ]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s (π * B0) * Formalism.UG.cT s B0' := by
            rw [hu.mul_val_inv, Matrix.mul_one, cT_mul_r]
      _ = 1 := by rw [hBπ0, ← cT_mul_r, hB0, cT_one_r]
  have hGu : IsUnit (Formalism.UG.cT s B0 * Q * B0) :=
    ⟨⟨_, _, hG, mul_eq_one_comm.mp hG⟩, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_orthonormal_basis_unimodular_hermitian_local_ring O s hs ⟨τ, hτ⟩ hnorm m (Formalism.UG.cT s B0 * Q * B0) (key B0 B0) hGu
  obtain ⟨B, B', hB, hBB, hBg⟩ : ∃ (B : Matrix (Fin n) (Fin m) O) (B' : Matrix (Fin m) (Fin n) O),
      B' * B = 1 ∧ B * B' = π ∧ Formalism.UG.cT s B * Q * B = 1 := by
    refine ⟨B0 * a.1, (a⁻¹).1 * B0', ?_, ?_, ?_⟩
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B0', hB0, Matrix.one_mul, Units.inv_mul]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc a.1, Units.mul_inv, Matrix.one_mul, hB0π]
    · rw [← ha, cT_mul_r]; simp only [Matrix.mul_assoc]
  have hπB : π * B = B := by rw [← hBB, Matrix.mul_assoc, hB, Matrix.mul_one]
  have hB'π : B' * π = B' := by rw [← hBB, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hCB : Formalism.UG.cT s C * Q * B = 0 := by rw [← hπB, ← Matrix.mul_assoc, hCπ, Matrix.zero_mul]
  have hZB : Formalism.UG.cT s Z * Q * B = 0 := by rw [← hπB, ← Matrix.mul_assoc, hZπ, Matrix.zero_mul]
  have hB'C : B' * C = 0 := by rw [← hB'π, Matrix.mul_assoc, hπC, Matrix.mul_zero]
  have hB'Z : B' * Z = 0 := by rw [← hB'π, Matrix.mul_assoc, hπZ, Matrix.mul_zero]
  have hBC : Formalism.UG.cT s B * Q * C = 0 := by rw [← key, hCB, cT_zero_r]
  have hBZ : Formalism.UG.cT s B * Q * Z = 0 := by rw [← key, hZB, cT_zero_r]
  refine ⟨m, fromCols (fromCols C Z) B, fromRows (fromRows (Formalism.UG.cT s Z * Q) (Formalism.UG.cT s C * Q)) B',
    ?_, ?_, ?_, ?_⟩
  · simp only [fromRows_mul_fromCols, fromRows_mul, mul_fromCols, h1, h2, h3, hC, hCB, hZB, hB'C, hB'Z, hB]
    ext (((i|i)|i)) (((j|j)|j)) <;> simp [Matrix.one_apply]
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, hBB, hπ]
    abel
  · rw [cT_fromCols_r, cT_fromCols_r]
    simp only [fromRows_mul, mul_fromCols, h1, h2, h3, hC, hCB, hZB, hBC, hBZ, hBg]
    ext (((i|i)|i)) (((j|j)|j)) <;> simp
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows]
    simp

theorem exists_isometry_frame : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O), (∀ x, s (s x) = x) → (∃ τ : O, τ + s τ = 1) → (∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u) → ∀ (n r : ℕ) (Q : Matrix (Fin n) (Fin n) O), Formalism.UG.cT s Q = Q → IsUnit Q → ∀ C C' : Matrix (Fin n) (Fin r) O, (∃ L : Matrix (Fin r) (Fin n) O, L * C = 1) → (∃ L : Matrix (Fin r) (Fin n) O, L * C' = 1) → Formalism.UG.cT s C * Q * C = 0 → Formalism.UG.cT s C' * Q * C' = 0 → ∃ k : GL (Fin n) O, Formalism.UG.cT s k.1 * Q * k.1 = Q ∧ k.1 * C = C' := by
  intro O _ _ s hs hτ hnorm n r Q hQ hu C C' hL hL' hC hC'
  obtain ⟨τ, hτ⟩ := hτ
  obtain ⟨L, hL⟩ := hL
  obtain ⟨L', hL'⟩ := hL'
  obtain ⟨m, T, S, h1, h2, h3, h4⟩ := exists_completion hs hτ hnorm hQ hu hL hC
  obtain ⟨m', T', S', h1', h2', h3', h4'⟩ := exists_completion hs hτ hnorm hQ hu hL' hC'
  have hm : m = m' := by
    have e1 := card_eq_of_inv h1 h2
    have e2 := card_eq_of_inv h1' h2'
    simp only [Fintype.card_sum, Fintype.card_fin] at e1 e2
    omega
  subst hm
  have hk1 : Formalism.UG.cT s (T' * S) * Q * (T' * S) = Q := by
    calc Formalism.UG.cT s (T' * S) * Q * (T' * S) = Formalism.UG.cT s S * (Formalism.UG.cT s T' * Q * T') * S := by
          rw [cT_mul_r]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s (T * S) * Q * (T * S) := by
          rw [h3', ← h3, cT_mul_r]; simp only [Matrix.mul_assoc]
      _ = Q := by rw [h2, cT_one_r, Matrix.one_mul, Matrix.mul_one]
  have hk2 : T' * S * C = C' := by
    rw [← h4, ← h4', ← Matrix.mul_assoc (T' * S), Matrix.mul_assoc T' S T, h1, Matrix.mul_one]
  refine ⟨⟨T' * S, T * S', ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, h1, Matrix.one_mul, h2']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', h1', Matrix.one_mul, h2]
  · exact hk1
  · exact hk2

end GlobalTheory.WittFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealComp

theorem eq_zero_of_map_eq_zero {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    {I : Type} {B : I → Type} [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)] (f : ∀ i, A →ₐ[F] B i)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0) (z : A ⊗[F] E)
    (hz : ∀ i, Algebra.TensorProduct.map (f i) (AlgHom.id F E) z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis F E
  have key : ∀ i (y : A ⊗[F] E) k,
      (Algebra.TensorProduct.basis (B i) b).repr (Algebra.TensorProduct.map (f i) (AlgHom.id F E) y) k =
        f i ((Algebra.TensorProduct.basis A b).repr y k) := by
    intro i y k
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  apply (Algebra.TensorProduct.basis A b).repr.injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hf _ fun i => ?_
  rw [← key, hz, map_zero, Finsupp.zero_apply]

theorem compInf_eq_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (z : AF F ⊗[F] E) : compInf F E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {D : D7}

theorem compInf_eq (w : InfinitePlace D.host.F) (z : AE D) : compInf D.host.F D.host.E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E) (infPart D z) :=
  compInf_eq_map w z

theorem compInf_zero_iff (z : AE D) : (∀ w, compInf D.host.F D.host.E w z = 0) ↔ infPart D z = 0 := by
  refine ⟨fun h => ?_, fun h w => by rw [compInf_eq, h, map_zero]⟩
  exact eq_zero_of_map_eq_zero (fun w => GlobalTheory.AutFunCompare.evW w) (fun a ha => funext ha) _
    fun w => (compInf_eq w z).symm.trans (h w)

theorem theta_zero_iff {θ : InfFam D} (hθ : IsInfFam θ) (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    (∀ τ, θ τ y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h τ => by rw [h, map_zero]⟩
  refine (GlobalTheory.Mem.VolExists.infEmb_bijective (isCMExt_host D)
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hθ).1 (funext fun τ => ?_)
  exact (h τ).trans (map_zero _).symm

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem eq_zero_of_parts (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  rw [map_zero]
  exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h2)

theorem real_components : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ z : AE D, (∀ w, compInf D.host.F D.host.E w z = 0) ↔ ∀ τ, θ τ (infPart D z) = 0) ∧ (∀ z τ, θ τ (infPart D (cA D z)) = conj (θ τ (infPart D z))) ∧ (∀ x τ, θ τ (infPart D (incA D x)) = tauE D τ x) ∧ (∀ z : AE D, (∀ τ, θ τ (infPart D z) = 0) → finPart D z = 0 → z = 0) := by
  intro D θ hθ
  refine ⟨fun z => (compInf_zero_iff z).trans (theta_zero_iff hθ _).symm, fun z τ => ?_, fun x τ => (hθ τ).1 x,
    fun z h1 h2 => eq_zero_of_parts z ((theta_zero_iff hθ _).1 h1) h2⟩
  rw [infPart_conj]
  exact GlobalTheory.Mem.VolExists.infEmb_sigR (isCMExt_host D) (hθ τ) _

end GlobalTheory.StdUnn.RealComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
section
noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction

open Formalism.UG (bc)

theorem row_ne_zero {A : Type} [CommRing A] [Nontrivial A] {r n : ℕ} {M : Matrix (Fin r) (Fin n) A}
    {N : Matrix (Fin n) (Fin r) A} (h : M * N = 1) (i : Fin r) : ¬∀ x, M i x = 0 := fun h2 => by
  have h5 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_zero fun x _ => by rw [h2, zero_mul]] at h5
  exact zero_ne_one h5

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

variable (d : HypDec T T₀ r)

theorem nB_mem (b : Mx D r T₀.rank) : d.nB b ∈ stab d := ⟨1, by rw [d.nB_jX, Units.val_one, Matrix.mul_one]⟩

theorem nC_mem (c : skewA D r) : d.nC c ∈ stab d := ⟨1, by rw [d.nC_jX, Units.val_one, Matrix.mul_one]⟩

theorem wittCoreEmbedding_mem_isotropicStabilizer (g : GA D T₀) : d.emb0 g ∈ stab d := ⟨1, by rw [d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩

theorem exists_decomp (p : stab d) : ∃ b c g, (p : GA D T) = d.nB b * d.nC c * d.emb0 g * d.levi (onX d p) := by
  have h : (p : GA D T) * d.levi (onX d p)⁻¹ ∈ MixPer.stabX d := by
    show mt T (p * d.levi (onX d p)⁻¹) ⬝ d.jX = d.jX
    rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (mul_jX d p), Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  obtain ⟨n, hn, g, e⟩ := (MixPer.Decomp.mem_stabX_iff d).1 h
  obtain ⟨b, c, rfl⟩ := (MixPer.Decomp.mem_radX_iff d).1 hn
  exact ⟨b, c, g, by rw [← e, map_inv, inv_mul_cancel_right]⟩

theorem reduction_GL_diagonalUnitPowers_compact {E A : Type} [Field E] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (j : E →+* A) {s : Aˣ} {ν : Aˣ →* ℝ≥0} (hν : Continuous ν) (hj : ∀ u : Eˣ, ν (Units.map j.toMonoidHom u) = 1)
    {b : ℝ} (hb : 0 < b) (hs : (ν s : ℝ) = b⁻¹) {r : ℕ}
    (hR : ∃ Ω : Set A, IsCompact Ω ∧ ∀ β : GL (Fin r) A, ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ) (c : GL (Fin r) A),
      (∀ i k, c.1 i k ∈ Ω ∧ c⁻¹.1 i k ∈ Ω) ∧ δ.1.map j * β.1 = diagonal (fun i => (s ^ l i).1) * c.1) :
    ∃ (L : Set (GL (Fin r) A)) (C : ℝ), IsCompact L ∧ ∀ α : GL (Fin r) A,
    ∃ (δ : GL (Fin r) E) (l : Fin r → ℤ), ∃ c ∈ L, bc j δ * α = dg s l * c ∧
      (ν (GeneralLinearGroup.det α) : ℝ) ≤ C * ∏ i, (b ^ l i)⁻¹ := by
  obtain ⟨Ω, hΩ, hR⟩ := hR
  choose δ l c hcΩ hred using hR
  replace hred : ∀ β, bc j (δ β) * β = dg s (l β) * c β := fun β => Units.ext (hred β)
  obtain ⟨L, hL, hcL⟩ : Bdd c :=
    bdd_units (bdd_matrix hΩ fun q i k => (hcΩ q i k).1) (bdd_matrix hΩ fun q i k => (hcΩ q i k).2)
  have hdet : Continuous (GeneralLinearGroup.det : GL (Fin r) A → Aˣ) := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  obtain ⟨B, hB⟩ := (hL.image (NNReal.continuous_coe.comp (hν.comp hdet))).bddAbove
  refine ⟨L, B, hL, fun α => ⟨δ α, l α, c α, hcL α, hred α, ?_⟩⟩
  have h1 : GeneralLinearGroup.det (bc j (δ α)) = Units.map j.toMonoidHom (GeneralLinearGroup.det (δ α)) :=
    Units.ext (j.map_det (δ α).1).symm
  have h3 := congrArg (fun x => (ν (GeneralLinearGroup.det x) : ℝ)) (hred α)
  beta_reduce at h3
  rw [map_mul, map_mul, map_mul, map_mul, h1, hj, one_mul, det_dg, map_prod, NNReal.coe_mul, NNReal.coe_prod] at h3
  have h4 : ∀ i, (ν (s ^ l α i) : ℝ) = (b ^ l α i)⁻¹ := fun i => by
    rw [map_zpow, NNReal.coe_zpow, hs, _root_.inv_zpow]
  rw [h3, mul_comm, Finset.prod_congr rfl fun i _ => h4 i]
  exact mul_le_mul_of_nonneg_right (hB ⟨_, hcL α, rfl⟩) (by positivity)

theorem bound_aux {E A : Type} [Field E] [CommRing A] (j : E →+* A) {s : Aˣ} {Ω : Set A} {m₀ r n : ℕ}
    (hm₀ : ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, j x = s.1 ^ m * ω → x = 0) {l : Fin r → ℤ} {y : Matrix (Fin r) (Fin n) E}
    {w : Matrix (Fin r) (Fin n) A} (hw : ∀ i x, w i x ∈ Ω) (e : y.map j = (dg s l)⁻¹.1 * w) (i : Fin r)
    (h : ¬∀ x, y.map j i x = 0) : -(m₀ : ℤ) ≤ l i := by
  by_contra! hlt
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (a := -l i) (by omega)
  refine h fun x => ?_
  have h3 : j (y i x) = s.1 ^ m * w i x := by
    refine (congrFun (congrFun e i) x).trans ?_
    rw [show (dg s l)⁻¹.1 = diagonal fun i => (s ^ l i)⁻¹.1 from rfl, diagonal_mul, ← _root_.zpow_neg, hm, zpow_natCast,
      Units.val_pow_eq_pow_val]
  rw [map_apply, hm₀ m (by omega) _ (hw i x) _ h3, map_zero]

end GlobalTheory.GodementSectionReduction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramUnimodular
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unimod

theorem hform_frame {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J B : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform σ J (B *ᵥ x) (B *ᵥ y) = ∑ i, σ (x i) * ((Formalism.UG.cT σ B * J * B) *ᵥ y) i := by
  have h1 : ∀ (u w : Fin n → R), Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := fun u w => by
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : (fun i => σ ((B *ᵥ x) i)) = (B.map σ) *ᵥ (fun i => σ (x i)) := funext fun i => RingHom.map_mulVec σ B x i
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec]
  rfl

theorem gram_int {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (O : Subring R) (hσ : ∀ z ∈ O, σ z ∈ O)
    (J B C H' : Matrix (Fin n) (Fin n) R) (L : (Fin n → R) → Prop) (hBC : B * C = 1)
    (hH : Formalism.UG.cT σ B * J * B * H' = 1)
    (hf : ∀ y, (∀ i, y i ∈ O) ↔ L (B *ᵥ y)) (hd : ∀ y, L y ↔ ∀ x, L x → Formalism.UG.hform σ J x y ∈ O) :
    (∀ i j, (Formalism.UG.cT σ B * J * B) i j ∈ O) ∧ ∀ i j, H' i j ∈ O := by
  have hs : ∀ i k : Fin n, (Pi.single i 1 : Fin n → R) k ∈ O := fun i k => by
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  constructor
  · intro i j
    have h := (hd _).1 ((hf _).1 (hs j)) _ ((hf _).1 (hs i))
    rw [hform_frame, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h
    simpa using h
  · intro i j
    have h : L (B *ᵥ (H' *ᵥ Pi.single j 1)) := by
      refine (hd _).2 fun x hx => ?_
      have e : x = B *ᵥ (C *ᵥ x) := by rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
      have hz : ∀ k, (C *ᵥ x) k ∈ O := (hf _).2 (e ▸ hx)
      rw [e, hform_frame]
      refine sum_mem fun k _ => mul_mem (hσ _ (hz k)) ?_
      rw [Matrix.mulVec_mulVec, hH, Matrix.one_mulVec]
      exact hs j k
    simpa using (hf _).2 h i

theorem compFin_cA {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_gram {D : D7} (A : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (b : Mx D A.rank A.rank) :
    (adj b * gA A * b).map (compFin D.host.F D.host.E v) =
      Formalism.UG.cT (sigR _ D.sp.cm.sig) (b.map (compFin D.host.F D.host.E v)) * JR (Fv D.host.F v) A.gram *
        b.map (compFin D.host.F D.host.E v) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  funext i j; exact compFin_cA v _

theorem gram_unimodular : ∀ (D : D7) (A : HSp D) (b : GL (Fin A.rank) (AE D)), IsLatticeFrame (frameLat A) b → ∃ Hm : GL (Fin A.rank) (AE D), Hm.1 = adj b.1 * gA A * b.1 ∧ IntGL Hm := by
  intro D A b hb
  have h1 : adj b.1 * adj (b⁻¹).1 = 1 := by
    rw [← adj_mul, Units.inv_mul, adj_one]
  have h2 : adj (b⁻¹).1 * adj b.1 = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  let Hm : GL (Fin A.rank) (AE D) :=
    (⟨adj b.1, adj (b⁻¹).1, h1, h2⟩ * ⟨gA A, giA A, gA_mul_giA A, giA_mul_gA A⟩ * b : (Mx D A.rank A.rank)ˣ)
  have hH : Hm.1 = adj b.1 * gA A * b.1 := rfl
  have key := fun v : HeightOneSpectrum (𝓞 D.host.F) =>
    gram_int (sigR _ D.sp.cm.sig) (intLoc D.host.F D.host.E v) (fun z hz => sigR_mem_intLoc _ hz)
      (JR (Fv D.host.F v) A.gram) (b.1.map (compFin D.host.F D.host.E v)) ((b⁻¹).1.map (compFin D.host.F D.host.E v))
      ((Hm⁻¹).1.map (compFin D.host.F D.host.E v)) (fun y => y ∈ latLoc D.host.F (frameLat A) v)
      (by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← map_gram, ← hH, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (hb v) (fun y => by
        have := SelfDual.isSelfDualAt_frameLat D A v
        exact (SetLike.ext_iff.1 this) y)
  refine ⟨Hm, hH, fun i j v => ?_, fun i j v => (key v).2 i j⟩
  have := (key v).1 i j
  rw [← map_gram, ← hH] at this
  exact this

end GlobalTheory.StdUnn.Unimod
end

