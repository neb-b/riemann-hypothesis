module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSum
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.TraceCas

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth GlobalTheory.CompanionTheory.HCRep

theorem sum_sq_eq {L A ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [LieRing L] [LieAlgebra ℝ L]
    [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    (B : LinearMap.BilinForm ℝ L) (hs : ∀ X Y, B X Y = B Y X) (l : L →ₗ[ℝ] A)
    (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (c c' : κ → L) (hc : ∀ Y, Y = ∑ k, B (c' k) Y • c k) :
    ∑ i, ε i • (l (b i) * l (b i)) = ∑ k, l (c k) * l (c' k) := by
  have h1 : ∀ i, l (b i) = ∑ k, B (c' k) (b i) • l (c k) := fun i => by
    conv_lhs => rw [hc (b i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have h2 : ∀ k, l (c' k) = ∑ i, (ε i * B (b i) (c' k)) • l (b i) := fun k => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (c' k)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  calc ∑ i, ε i • (l (b i) * l (b i))
      = ∑ i, ε i • ((∑ k, B (c' k) (b i) • l (c k)) * l (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h1 i]
    _ = ∑ k, l (c k) * ∑ i, (ε i * B (b i) (c' k)) • l (b i) := by
        simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hs (c' k) (b i)]
    _ = ∑ k, l (c k) * l (c' k) := Finset.sum_congr rfl fun k _ => by rw [← h2 k]

theorem half_sum {A : Type*} [Ring A] [Algebra ℂ A] (e₁ f₁ e₂ f₂ : A) :
    (2 : ℂ) • (((1 / 2 : ℂ) • (e₁ - Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ - Complex.I • f₂)) +
      ((1 / 2 : ℂ) • (e₁ + Complex.I • f₁)) * ((1 / 2 : ℂ) • (e₂ + Complex.I • f₂))) =
      e₁ * e₂ - f₁ * f₂ := by
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, add_mul, mul_add, smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp

theorem mul_neg_add {A : Type*} [Ring A] (x y z t : A) : x * -y + z * t = z * t - x * y := by
  rw [mul_neg]
  abel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  classical
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

theorem atEmb_neg (τ : E →+* ℂ) (z : ℂ) : atEmb τ (-z) = -atEmb τ z := by
  rw [atEmb_eq τ (-z), atEmb_eq τ z]
  simp only [Complex.neg_re, Complex.neg_im, neg_smul]
  abel

theorem place_formula (τ : E →+* ℂ) :
    (2 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) τ) + Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ))) =
      ∑ i, ∑ j, (lieS E a i j (atEmb τ 1) * lieS E a j i (atEmb τ 1) -
        lieS E a i j (atEmb τ Complex.I) * lieS E a j i (atEmb τ Complex.I)) := by
  have hc : ∀ i j : Fin a, Eop (a := a) (ComplexEmbedding.conjugate τ) i j =
      (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) + Complex.I • lieS E a i j (atEmb τ Complex.I)) := by
    intro i j
    simp only [Eop, atEmb_conj, map_one, Complex.conj_I, atEmb_neg, map_neg, smul_neg, sub_neg_eq_add]
  simp only [Formalism.REAL.Cas, hc, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact half_sum (A := Module.End ℂ (Sm E a)) (lieS E a i j (atEmb τ 1)) (lieS E a i j (atEmb τ Complex.I))
    (lieS E a j i (atEmb τ 1)) (lieS E a j i (atEmb τ Complex.I))

def cInv (z : Cinf E) : mixedEmbedding.mixedSpace E := (0, fun v => z v.1)

theorem cMap_cInv (z : Cinf E) : cMap E (cInv z) = z := rfl

theorem cInv_cMap (x : mixedEmbedding.mixedSpace E) : cInv (cMap E x) = x := by
  refine Prod.ext (funext fun v => ?_) rfl
  exact absurd (IsTotallyComplex.isComplex v.1) (InfinitePlace.not_isComplex_iff_isReal.2 v.2)

theorem mMap_injective : Function.Injective (mMap E a) := by
  intro X Y h
  funext p q
  have h' : cMap E ((X : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) =
      cMap E ((Y : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) p q) := congrFun (congrFun h p) q
  have := congrArg cInv h'
  rwa [cInv_cMap, cInv_cMap] at this

def Mt (i j : Fin a) (x : Cinf E) : (isExpLieAlgebra E a).lieSubalgebra :=
  ⟨(Matrix.single i j (cInv x) : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), mem_lie _⟩

def coordL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Lie E a where
  toFun X := mMap E a (X : ArchMatrix E a)
  map_add' X Y := map_add (mMap E a) (X : ArchMatrix E a) (Y : ArchMatrix E a)
  map_smul' r X := map_smul (mMap E a) r (X : ArchMatrix E a)

theorem coordL_Mt (i j : Fin a) (x : Cinf E) : coordL (Mt i j x) = toL (Matrix.single i j x) := by
  funext p q
  change cMap E (Matrix.single i j (cInv x) p q) = Matrix.single i j x p q
  simp only [Matrix.single_apply]
  split_ifs
  · exact cMap_cInv x
  · exact map_zero _

def liBL : (isExpLieAlgebra E a).lieSubalgebra →ₗ[ℝ] Module.End ℂ (Sm E a) := (lie E a).comp coordL

theorem liBL_apply (X : (isExpLieAlgebra E a).lieSubalgebra) : liBL X = liB X := rfl

theorem liBL_Mt (i j : Fin a) (x : Cinf E) : liBL (Mt i j x) = lieS E a i j x := by
  rw [lieS_apply]
  change lie E a (coordL (Mt i j x)) = _
  rw [coordL_Mt]

theorem trace_Mt (i j : Fin a) (x : Cinf E) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (Mt j i x) Y = ∑ w, (x w * coordL Y i j w).re := by
  have h : Matrix.trace (mat ((Mt j i x : (isExpLieAlgebra E a).lieSubalgebra) : ArchMatrix E a) *
      mat (Y : ArchMatrix E a)) = cInv x * mat (Y : ArchMatrix E a) i j := by
    change Matrix.trace (Matrix.single j i (cInv x) * mat (Y : ArchMatrix E a)) = _
    rw [Matrix.trace, Finset.sum_eq_single j]
    · simp [Matrix.diag, Matrix.single_mul_apply_same]
    · intro c _ hc
      exact Matrix.single_mul_apply_of_ne _ _ _ _ _ hc _
    · simp
  rw [archTraceForm_apply, h, mixedTraceL_apply]
  simp only [Prod.fst_mul, Pi.mul_apply, cInv, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Prod.snd_mul]
  refine Finset.sum_bij (fun v _ => v.1) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro w _
    exact ⟨⟨w, IsTotallyComplex.isComplex w⟩, by simp, rfl⟩
  · intro v _
    rfl

open Classical in
theorem toL_single_atEmb (i j p q : Fin a) (w v : InfinitePlace E) (z : ℂ) :
    toL (Matrix.single i j (atEmb w.embedding z)) p q v = if (w, i, j) = (v, p, q) then z else 0 := by
  change Matrix.single i j (atEmb w.embedding z) p q v = _
  simp only [Matrix.single_apply, Prod.mk.injEq]
  by_cases h1 : i = p <;> by_cases h2 : j = q <;> by_cases h3 : w = v <;>
    simp [h1, h2, h3, atEmb_embedding_apply, eq_comm]

def cc : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt i j (atEmb w.embedding 1)
  | ((w, i, j), true) => Mt i j (atEmb w.embedding Complex.I)

def cc' : (InfinitePlace E × Fin a × Fin a) × Bool → (isExpLieAlgebra E a).lieSubalgebra
  | ((w, i, j), false) => Mt j i (atEmb w.embedding 1)
  | ((w, i, j), true) => -Mt j i (atEmb w.embedding Complex.I)

theorem trace_cc'_false (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), false)) Y = (coordL Y i j w).re := by
  classical
  change archTraceForm E a (Mt j i (atEmb w.embedding 1)) Y = _
  rw [trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem trace_cc'_true (w : InfinitePlace E) (i j : Fin a) (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a (cc' ((w, i, j), true)) Y = (coordL Y i j w).im := by
  classical
  change archTraceForm E a (-Mt j i (atEmb w.embedding Complex.I)) Y = _
  rw [map_neg, LinearMap.neg_apply, trace_Mt]
  simp [atEmb_embedding_apply, apply_ite Complex.re]

theorem expansion (Y : (isExpLieAlgebra E a).lieSubalgebra) :
    Y = ∑ k, archTraceForm E a (cc' k) Y • cc k := by
  classical
  apply Subtype.ext
  apply mMap_injective
  change coordL Y = coordL (∑ k, archTraceForm E a (cc' k) Y • cc k)
  have term : ∀ (p q : Fin a) (v : InfinitePlace E) (t : InfinitePlace E × Fin a × Fin a),
      (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v =
        if t = (v, p, q) then coordL Y p q v else 0 := by
    rintro p q v ⟨w, i, j⟩
    rw [Fintype.sum_bool, map_smul, map_smul, trace_cc'_true, trace_cc'_false]
    change (((coordL Y i j w).im • coordL (Mt i j (atEmb w.embedding Complex.I)) +
      (coordL Y i j w).re • coordL (Mt i j (atEmb w.embedding 1))) p q v) = _
    rw [coordL_Mt, coordL_Mt]
    simp only [Pi.add_apply, Pi.smul_apply, toL_single_atEmb]
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ : w = v ∧ i = p ∧ j = q := by simpa using h
      apply Complex.ext <;> simp
    · simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Fintype.sum_prod_type]
  funext p q v
  let ev : Lie E a →+ ℂ := ⟨⟨fun X => X p q v, rfl⟩, fun _ _ => rfl⟩
  change ev (coordL Y) = ev (∑ t, ∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  change _ = ∑ t, (∑ b, coordL (archTraceForm E a (cc' (t, b)) Y • cc (t, b))) p q v
  simp only [term]
  simp [ev]

theorem omegaOp_eq_two_cas (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have key := sum_sq_eq (A := Module.End ℂ (Sm E a)) (archTraceForm E a) archTraceForm_symm (liBL (E := E) (a := a)) b ε hε2 horth cc cc' expansion
  have hL : omegaOp (⇑b) ε = ∑ i, ε i • (liBL (b i) * liBL (b i)) := by
    unfold omegaOp
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [liBL_apply]
    ext φ
    simp
  rw [hL, key, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [place_formula, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  change liBL (Mt i j (atEmb w.embedding Complex.I)) * liBL (-Mt j i (atEmb w.embedding Complex.I)) +
    liBL (Mt i j (atEmb w.embedding 1)) * liBL (Mt j i (atEmb w.embedding 1)) = _
  rw [map_neg, liBL_Mt, liBL_Mt, liBL_Mt, liBL_Mt]
  exact mul_neg_add (A := Module.End ℂ (Sm E a)) _ _ _ _

end GlobalTheory.CompanionTheory.HCRep.TraceCas

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitarySendsIsotropic
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov


open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module in
theorem exists_ratPts_sends_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ v : Fin n → E, v ≠ 0 → hE σ J v v = 0 → ∃ γ ∈ ratPts σ J, Sends σ J γ (Xᵀ 0) v := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW v hv hvv
  obtain ⟨hF, hEc, h2, hc⟩ := hσ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  have hH : IsHermitianFor (conjHom F E) J := Matrix.ext fun i j => hJ.1 i j
  obtain ⟨h, hg, hform⟩ : ∃ h : HermitianForm F E (Fin n → E), gram h.toSesq (Pi.basisFun E (Fin n)) = J ∧
      ∀ x y, h.toSesq x y = hE (conj F E).toAlgHom J x y :=
    ⟨HermitianForm.ofGram J hH hu, gram_ofGram J hH hu, fun x y => rfl⟩
  have key : ∀ A B : Matrix (Fin n) (Fin (r + 1)) E, h.toSesq (Aᵀ 0) (Bᵀ 0) =
      (cT (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) A * J * B) 0 0 := by
    intro A B
    rw [hform]
    simp only [hE, Formalism.UG.hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hxx : h.toSesq (Xᵀ 0) (Xᵀ 0) = 0 := by rw [key, hW.xx]; rfl
  have hyy : h.toSesq (Yᵀ 0) (Yᵀ 0) = 0 := by rw [key, hW.yy]; rfl
  have hxy : h.toSesq (Xᵀ 0) (Yᵀ 0) = 1 := by rw [key, hW.xy]; simp
  obtain ⟨w, hvw, hww⟩ := WittPartner.full h v hv (by rw [hform]; exact hvv)
  obtain ⟨g, hgv, -⟩ := HyperbolicPairTransitive.full h (Xᵀ 0) (Yᵀ 0) v w ⟨hxx, hyy, hxy⟩
    ⟨by rw [hform]; exact hvv, hww, hvw⟩
  obtain ⟨M, hM, hact⟩ : ∃ M : GL (Fin n) E, M ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J ∧
      (M : Matrix (Fin n) (Fin n) E) *ᵥ (Xᵀ 0) = v := by
    have h3 : ∀ N : GL (Fin n) E, N ∈ unitaryGroupMatrix (conjHom F E) (gram h.toSesq (Pi.basisFun E (Fin n))) →
        N ∈ Formalism.UG.UJ (((conj F E).toAlgHom : E →ₐ[F] E) : E →+* E) J := by
      rw [hg]
      exact fun N hN => hN
    refine ⟨_, h3 _ (unitaryGroupEquivMatrix h (Pi.basisFun E (Fin n)) g).2, ?_⟩
    rw [unitaryGroupEquivMatrix_apply, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_mulVec]
    exact hgv
  refine ⟨ratEmb _ J ⟨M, hM⟩, by rw [← range_ratEmb]; exact ⟨_, rfl⟩, ?_⟩
  unfold Sends
  funext i
  rw [← hact]
  have e : (matHom _ _ J (ratEmb _ J ⟨M, hM⟩)).1 = (M : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := rfl
  rw [e]
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ _ i).symm

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugate
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem rt_infGL_mul_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (g : GL (Fin a) (Cinf E)) (X : Lie E a) :
    rt E a (infGL E a g) * lie E a X =
      lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  refine LinearMap.ext fun ψ => Subtype.ext <| funext fun x => ?_
  have hd : DifferentiableAt ℝ (chart ψ.1 x) (toL g.val) :=
    (contDiffAt_chart ψ.2 x (val_mem_invSet g)).differentiableAt (by simp)
  have e1 : lmul (toL g.val) (oneL E a) = toL g.val := mul_one g.val
  have e2 : rmul (toL g.val) (oneL E a) = toL g.val := one_mul g.val
  have e3 : lmul (toL g.val) X = rmul (toL g.val) (toL (g.val * Matrix.of X * (g⁻¹).val)) := by
    change g.val * Matrix.of X = g.val * Matrix.of X * (g⁻¹).val * g.val
    rw [mul_assoc (g.val * Matrix.of X), ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  change fderiv ℝ (chart ψ.1 (x * infGL E a g)) (oneL E a) X =
    fderiv ℝ (chart (fun y => ψ.1 (y * infGL E a g)) x) (oneL E a)
      (toL (g.val * Matrix.of X * (g⁻¹).val))
  rw [chart_mul, chart_rt_inf,
    fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL g.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL g.val)).differentiableAt,
    e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [e3]

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatrices
section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCoeffs

theorem exists_coeff_matrices_of_span_eq {K : Type} [Field K] {n r : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c)
    (hs : Submodule.span K (Set.range c) = Submodule.span K (Set.range C)) :
    ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
      C = T * c ∧ c = L * C ∧ L * T = 1 := by
  have hT0 : ∀ j, ∃ t : Fin r → K, ∑ i, t i • c i = C j := by
    intro j
    have hj : C j ∈ Submodule.span K (Set.range c) := by
      rw [hs]
      exact Submodule.subset_span (Set.mem_range_self j)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hj
  have hL0 : ∀ i, ∃ t : Fin n → K, ∑ j, t j • C j = c i := by
    intro i
    have hi : c i ∈ Submodule.span K (Set.range C) := by
      rw [← hs]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hi
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin r) K, ∀ j, ∑ i, T j i • c i = C j :=
    ⟨fun j => (hT0 j).choose, fun j => (hT0 j).choose_spec⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) K, ∀ i, ∑ j, L i j • C j = c i :=
    ⟨fun i => (hL0 i).choose, fun i => (hL0 i).choose_spec⟩
  have hCT : C = T * c := by
    ext j k
    rw [← hT j, Matrix.mul_apply]
    simp [Finset.sum_apply]
  have hcL : c = L * C := by
    ext i k
    rw [← hL i, Matrix.mul_apply]
    simp [Finset.sum_apply]
  refine ⟨T, L, hCT, hcL, ?_⟩
  have hLT : L * T * c = c := by rw [Matrix.mul_assoc, ← hCT, ← hcL]
  have hz0 : (L * T - 1) * c = 0 := by rw [Matrix.sub_mul, hLT, Matrix.one_mul, sub_self]
  have hc' := Fintype.linearIndependent_iff.mp hc
  ext i0 i
  have hrow : ∑ i, (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i • c i = 0 := by
    funext k
    have h0 := congrFun (congrFun hz0 i0) k
    rw [Matrix.mul_apply] at h0
    simpa [Finset.sum_apply] using h0
  have h1 : (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i = 0 := hc' (fun i => (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i) hrow i
  rwa [Matrix.sub_apply, sub_eq_zero] at h1

end GlobalTheory.CompanionTheory.BruhatCoeffs
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzHeisLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (evI realAd At tens Rest IsStd SInf)
open GlobalTheory.WeilM (schr)
open scoped SchwartzMap LineDeriv

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum]


open scoped Classical in
theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add (f := _), map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]

end GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
end

