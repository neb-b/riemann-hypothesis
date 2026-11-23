module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreases
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis

section Conj

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conj_isom_iff (c : R →+* R) (B g : GL ι R) (D J : Matrix ι ι R)
    (h : (B : Matrix ι ι R)ᵀ * D * (B : Matrix ι ι R).map c = J) :
    (((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c = J) ↔
      (g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c = D := by
  have h1 : (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have h2 : (B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have h1' : (B : Matrix ι ι R)ᵀ * (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have h2' : ((B⁻¹ : GL ι R) : Matrix ι ι R).map c * (B : Matrix ι ι R).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero c) (map_one c)]
  have key : ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R)ᵀ * J * ((B⁻¹ * g * B : GL ι R) : Matrix ι ι R).map c =
      (B : Matrix ι ι R)ᵀ * ((g : Matrix ι ι R)ᵀ * D * (g : Matrix ι ι R).map c) * (B : Matrix ι ι R).map c := by
    subst h
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (B : Matrix ι ι R)ᵀ * (g : Matrix ι ι R)ᵀ * ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * D *
          ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) * (g : Matrix ι ι R).map c *
          (B : Matrix ι ι R).map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [key]
  constructor
  · intro e
    have e' := congrArg (fun M => (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * M * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) e
    subst h
    have l : ∀ M : Matrix ι ι R, (((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * ((B : Matrix ι ι R)ᵀ * M * (B : Matrix ι ι R).map c) *
        ((B⁻¹ : GL ι R) : Matrix ι ι R).map c = M := fun M => by
      calc _ = ((((B⁻¹ : GL ι R) : Matrix ι ι R))ᵀ * (B : Matrix ι ι R)ᵀ) * M *
            ((B : Matrix ι ι R).map c * ((B⁻¹ : GL ι R) : Matrix ι ι R).map c) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [l] at e'
    rw [e', l]
  · intro e
    rw [e, h]

end Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def bA (b : GL (Fin n ⊕ Fin n) E) : GL (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F)) b

theorem bA_val (b : GL (Fin n ⊕ Fin n) E) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = incM F b.1 := rfl

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

theorem gram_frame (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ *
        dbl (incM F Y.J) * ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map
          (adCM σ χ).σ = Ad.J (AE F E) ε (Fin n) := by
  have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) hb
  have e1 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1.map (adCM σ χ).σ = (b.1.map σ).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    exact cA_inclR σ _
  have e2 : dbl (incM F Y.J) = (dbl Y.J).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl, incM]
  have e3 : (bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)).1ᵀ = (b.1ᵀ).map (inclR (F := F) (E := E) (AF F)) := rfl
  have e4 : Ad.J (AE F E) ε (Fin n) = (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E).map (inclR (F := F) (E := E) (AF F)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;> simp [Ad.J, h, Matrix.one_apply]
  rw [e1, e2, e3, e4, ← this]
  simp only [Matrix.map_mul]

def frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    G2 σ Y ≃* (adCM σ χ).U ε (Fin n) where
  toFun x := ⟨(bA b)⁻¹ * x.1 * bA b, (conj_isom_iff (adCM σ χ).σ (bA b) x.1 _ _ (gram_frame χ ε b hb)).2 x.2⟩
  invFun y := ⟨bA b * y.1 * (bA b)⁻¹, by
    have h := (conj_isom_iff (adCM σ χ).σ (bA (F := F) b) (bA b * y.1 * (bA b)⁻¹) _ _ (gram_frame χ ε b hb)).1
    apply h
    have : (bA (F := F) b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1 := by group
    rw [this]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    show bA b * ((bA b)⁻¹ * x.1 * bA b) * (bA b)⁻¹ = x.1
    group
  right_inv y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (bA b * y.1 * (bA b)⁻¹) * bA b = y.1
    group
  map_mul' x y := by
    apply Subtype.ext
    show (bA b)⁻¹ * (x.1 * y.1) * bA b = ((bA b)⁻¹ * x.1 * bA b) * ((bA b)⁻¹ * y.1 * bA b)
    group

theorem frameEquiv_val (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    (frameEquiv χ ε b hb x).1 = (bA b)⁻¹ * x.1 * bA b := rfl

theorem continuous_frameEquiv (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb) := by
  refine Continuous.subtype_mk ?_ _
  set_option synthInstance.maxHeartbeats 400000 in
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem continuous_frameEquiv_symm (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    Continuous (frameEquiv χ ε b hb).symm := by
  refine Continuous.subtype_mk ?_ _
  set_option synthInstance.maxHeartbeats 400000 in
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.CompanionTheory.SiegelFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

section Gen

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [CommRing A] [Algebra F A]

theorem trace_one_tmul' (e : E) :
    Algebra.trace A (A ⊗[F] E) ((1 : A) ⊗ₜ[F] e) = algebraMap F A (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem ann_gen (P : A → Prop) (hP : ∀ x : A, (∀ t : F, P (algebraMap F A t * x)) → ∃ c : F, x = algebraMap F A c)
    (z : A ⊗[F] E) (h : ∀ e : E, P (Algebra.trace A (A ⊗[F] E) (((1 : A) ⊗ₜ[F] e) * z))) :
    ∃ w : E, z = (1 : A) ⊗ₜ[F] w := by
  classical
  let b := Module.finBasis F E
  have hnd := traceForm_nondegenerate F E
  let d := (Algebra.traceForm F E).dualBasis hnd b
  let B := Algebra.TensorProduct.basis A b
  have hB : ∀ k, B k = (1 : A) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  have hz : ∑ k, B.repr z k • ((1 : A) ⊗ₜ[F] b k) = z := by
    simpa only [hB] using B.sum_repr z
  have ht : ∀ e : E, Algebra.trace A (A ⊗[F] E) (((1 : A) ⊗ₜ[F] e) * z) =
      ∑ k, B.repr z k * algebraMap F A (Algebra.trace F E (e * b k)) := by
    intro e
    conv_lhs => rw [← hz]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_smul, trace_one_tmul', smul_eq_mul]
  have hak : ∀ k, ∃ c : F, B.repr z k = algebraMap F A c := fun k => by
    refine hP _ fun t => ?_
    have h1 := h (t • d k)
    rw [ht] at h1
    have h2 : ∀ l, Algebra.trace F E (t • d k * b l) = if l = k then t else 0 := fun l => by
      have h3 : Algebra.trace F E (d k * b l) = if l = k then 1 else 0 :=
        LinearMap.BilinForm.apply_dualBasis_left hnd b k l
      rw [smul_mul_assoc, map_smul, h3]
      split_ifs <;> simp
    simp only [h2] at h1
    have h4 : ∑ l, B.repr z l * algebraMap F A (if l = k then t else 0) =
        algebraMap F A t * B.repr z k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [if_neg hl, map_zero, mul_zero])
        (fun hk => absurd (Finset.mem_univ k) hk), if_pos rfl, mul_comm]
    rwa [h4] at h1
  choose c hc using hak
  refine ⟨∑ k, c k • b k, ?_⟩
  rw [← hz, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc k, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end Gen

theorem halfTr_add' (a b : AE D) : halfTr (a + b) = halfTr a + halfTr b := by
  simp only [halfTr, trA, map_add (f := _), mul_add]

theorem halfTr_zero' : halfTr (0 : AE D) = 0 := by
  simp [halfTr]

theorem halfTr_neg' (a : AE D) : halfTr (-a) = -halfTr a := by
  simp only [halfTr, trA, map_neg, mul_neg]

theorem halfTr_add_cA (w : AE D) : halfTr (w + cA D w) = Algebra.trace (AF D.host.F) (AE D) w := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  simp only [halfTr, trA, map_add (f := _), Formalism.IndefR.Datum.Brg.trace_cA, mul_add]
  rw [← add_mul, h2, one_mul]

theorem halfTr_incA' (e : D.host.E) :
    halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
  rw [halfTr, trA, Formalism.IndefR.Fin.trace_incA, map_mul]

theorem continuous_halfTr' : Continuous (halfTr : AE D → AF D.host.F) :=
  continuous_const.mul Formalism.IndefR.Fin.cont_trace

def hE (i j : Fin r) (w : AE D) : Mx D r r :=
  Matrix.single j i w + Matrix.single i j (cA D w)

theorem adj_single' (a b : Fin r) (v : AE D) :
    adj (Matrix.single a b v : Mx D r r) = Matrix.single b a (cA D v) := by
  ext k l
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
  by_cases h : a = l ∧ b = k
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg (by tauto), map_zero]

theorem hE_mem (i j : Fin r) (w : AE D) : hE i j w ∈ hermA D r := by
  change adj (hE i j w) = hE i j w
  rw [hE, adj_add, adj_single', adj_single', cA_cA, add_comm]

theorem trace_hE_mul (i j : Fin r) (w : AE D) {z : Mx D r r} (hz : z ∈ hermA D r) :
    Matrix.trace (HMul.hMul (hE i j w) z : Mx D r r) = w * z i j + cA D (w * z i j) := by
  have h : adj z = z := hz
  have hji : z j i = cA D (z i j) := (congrFun (congrFun h j) i).symm
  rw [hE, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, hji, map_mul]
  rfl

theorem rat_single' (a b : Fin r) (e : D.host.E) :
    (rat (Matrix.single a b e) : Mx D r r) = Matrix.single a b (incA D e) := by
  ext k l
  simp only [rat, Matrix.map_apply, Matrix.single_apply]
  by_cases h : a = k ∧ b = l
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

theorem hE_rat (i j : Fin r) (e : D.host.E) : hE i j (incA D e) ∈ ratMx D r r := by
  refine ⟨Matrix.single j i e + Matrix.single i j (star e), ?_⟩
  show rat _ = _
  rw [rat_add, rat_single', rat_single', hE, GlobalTheory.DualPairCheck.cA_incA]

theorem ann_E {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (z : AE D)
    (h : ∀ e : D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * z)) = 1) :
    ∃ w : D.host.E, z = incA D w :=
  ann_gen (F := D.host.F) (E := D.host.E) (A := AF D.host.F) (fun x => ψ x = 1)
    (fun x hx => _root_.GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq D.host.F D.sp.cm.totReal ψ hψ x hx) z h

def chi (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b : hermA D r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul m b.1 : Mx D r r)))

theorem chi_add_left (ψ : AddChar (AF D.host.F) ℂ) (m m' : Mx D r r) (b : hermA D r) :
    chi ψ (m + m') b = chi ψ m b * chi ψ m' b := by
  simp only [chi]
  rw [Matrix.add_mul, Matrix.trace_add, halfTr_add', AddChar.map_add_eq_mul]

theorem chi_add_right (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b c : hermA D r) :
    chi ψ m (b + c) = chi ψ m b * chi ψ m c := by
  simp only [chi, AddSubgroup.coe_add]
  rw [Matrix.mul_add, Matrix.trace_add, halfTr_add', AddChar.map_add_eq_mul]

theorem chi_zero_left (ψ : AddChar (AF D.host.F) ℂ) (b : hermA D r) : chi ψ (0 : Mx D r r) b = 1 := by
  simp only [chi]
  rw [Matrix.zero_mul, Matrix.trace_zero, halfTr_zero', AddChar.map_zero_eq_one]

theorem chi_zero_right (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) : chi ψ m (0 : hermA D r) = 1 := by
  simp only [chi, AddSubgroup.coe_zero]
  rw [Matrix.mul_zero, Matrix.trace_zero, halfTr_zero', AddChar.map_zero_eq_one]

theorem chi_neg_left (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b : hermA D r) :
    chi ψ (-m) b = ψ (-halfTr (Matrix.trace (HMul.hMul m b.1 : Mx D r r))) := by
  simp only [chi]
  rw [Matrix.neg_mul, Matrix.trace_neg, halfTr_neg']

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {m : Mx D r r}
    (hm : m ∈ ratMx D r r) (c : ratHerm D r) : chi ψ m c.1 = 1 := by
  obtain ⟨γ, rfl⟩ := hm
  obtain ⟨δ, hδ⟩ := AddSubgroup.mem_comap.1 c.2
  have hδ' : rat δ = c.1.1 := hδ
  have h1 : (HMul.hMul (rat γ) c.1.1 : Mx D r r) = rat (γ * δ) := by rw [← hδ', rat_mul]
  have h2 : Matrix.trace (rat (γ * δ) : Mx D r r) = incA D (Matrix.trace (γ * δ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  show ψ (halfTr (Matrix.trace (HMul.hMul (rat γ) c.1.1 : Mx D r r))) = 1
  rw [h1, h2, halfTr_incA']
  exact hψ.2.2.1 _

theorem continuous_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (m : Mx D r r) :
    Continuous (chi ψ m : hermA D r → ℂ) := by
  refine hψ.1.comp (continuous_halfTr'.comp ?_)
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_trace

theorem star_psi' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ψ a * star (ψ a) = 1 := by
    have := hψ.2.1 a
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]
    simp
  rw [AddChar.map_neg_eq_inv]
  exact eq_inv_of_mul_eq_one_right h1

theorem rat_of_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (z : hermA D r)
    (h : ∀ t : ratHerm D r, chi ψ t.1.1 z = 1) : z ∈ ratHerm D r := by
  have key : ∀ i j, ∃ w : D.host.E, z.1 i j = incA D w := fun i j => by
    refine ann_E hψ _ fun e => ?_
    have h1 := h ⟨⟨hE i j (incA D e), hE_mem _ _ _⟩, AddSubgroup.mem_comap.2 (hE_rat i j e)⟩
    have h2 : chi ψ (hE i j (incA D e)) z = ψ (halfTr (Matrix.trace (HMul.hMul (hE i j (incA D e)) z.1 : Mx D r r))) := rfl
    rw [show chi ψ (hE i j (incA D e)) z = 1 from h1] at h2
    rw [trace_hE_mul i j _ z.2, halfTr_add_cA] at h2
    exact h2.symm
  choose w hw using key
  refine AddSubgroup.mem_comap.2 ⟨Matrix.of w, ?_⟩
  ext i j
  exact (hw i j).symm

theorem exists_chi_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : ratHerm D r)
    (hu : u ≠ 0) : ∃ b : hermA D r, chi ψ u.1.1 b ≠ 1 := by
  obtain ⟨γ, hγ⟩ := AddSubgroup.mem_comap.1 u.2
  have hγ' : rat γ = u.1.1 := hγ
  obtain ⟨x₀, hx₀⟩ := hψ.2.2.2
  obtain ⟨i, j, hij⟩ : ∃ i j, γ i j ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hu
    apply Subtype.ext
    apply Subtype.ext
    have : γ = 0 := Matrix.ext fun i j => hc i j
    rw [← hγ', this, rat_zero]
    rfl
  obtain ⟨e₀, he₀⟩ := Algebra.trace_surjective D.host.F D.host.E 1
  let w : AE D := incA D (γ i j)⁻¹ * (x₀ • incA D e₀)
  refine ⟨⟨hE i j w, hE_mem _ _ _⟩, ?_⟩
  have h1 : chi ψ u.1.1 ⟨hE i j w, hE_mem _ _ _⟩ =
      ψ (halfTr (Matrix.trace (HMul.hMul (hE i j w) u.1.1 : Mx D r r))) := by
    simp only [chi]
    rw [Matrix.trace_mul_comm]
  rw [h1, trace_hE_mul i j _ u.1.2, halfTr_add_cA]
  have h2 : w * u.1.1 i j = x₀ • incA D e₀ := by
    rw [← hγ']
    show incA D (γ i j)⁻¹ * (x₀ • incA D e₀) * incA D (γ i j) = _
    rw [mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hij, map_one, one_mul]
  rw [h2, map_smul, Formalism.IndefR.Fin.trace_incA, he₀, map_one, smul_eq_mul, mul_one]
  exact hx₀

end GlobalTheory.CompanionTheory.HermPoisson
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityZeroOfSplitColumn
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

noncomputable section

namespace GlobalTheory.CompanionTheory.FineProd.CellMulti

set_option synthInstance.maxHeartbeats 400000

theorem jhMult_cell_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h r : ℕ} (x : Fin h → IrrGL (k := k)) (y : Fin r → IrrGL (k := k)), (∀ j, (y j).IsCusp) → ∀ (b : Fin h → Fin r → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (y j).1) (j : Fin r) (i i' : Fin h), i ≠ i' → b i j ≠ 0 → b i' j ≠ 0 → jhMult (piTensor fun j => (y j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = 0 := by
  intro k _ _ _ _ hA h r x y hy b hrow hcol j i i' hii hi hi'
  classical
  by_contra h0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, -, hS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2 _ _
    (fun i => (x i).2.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (x i).2.rep.irr) hτ hτs h0
  have h1 := GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (fun j => multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s i j).ρ) j
    (y j).2.rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j).trans
      (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp hS _))
  let Y : Fin h → IrrGL (k := k) := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr
  have hYb : ∀ c, (Y c).1 = b c j := fun _ => rfl
  let ψ := prodIrrEquiv (hcol j) (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr
  have h2 := h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective)
  let S : Finset (Fin h) := Finset.univ.filter fun c => b c j ≠ 0
  let o : Fin S.card ↪o Fin h := S.orderEmbOfFin rfl
  have hcard : 2 ≤ S.card := Finset.one_lt_card.2 ⟨i, by simp [S, hi], i', by simp [S, hi'], hii⟩
  have ho : ∀ a, o a ∈ S := fun a => Finset.orderEmbOfFin_mem _ _ _
  have hrange : ∀ c, (Y c).1 ≠ 0 → c ∈ Set.range o := fun c hc => by
    rw [Finset.range_orderEmbOfFin]
    simpa [S, hYb] using hc
  have hsum : ∑ a, (Y (o a)).1 = (y j).1 := by
    have e1 : ∑ a, (Y (o a)).1 = ∑ c : S, b c j :=
      Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ fun a => rfl
    rw [e1, Finset.sum_coe_sort S (fun c => b c j), ← hcol j]
    exact Finset.sum_subset (Finset.subset_univ _) fun c _ hc => by simpa [S] using hc
  obtain ⟨E⟩ := GlobalTheory.T.induced_product_drop_zero_factors Y (hcol j) o o.strictMono hrange hsum
  have h3 := h2.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  refine jhMult_ne_zero_iff.2 h3
    (GlobalTheory.T.cuspidal_multiplicity_product_zero hA (y j) (fun a => Y (o a)) hsum (hy j) hcard fun a => Nat.pos_of_ne_zero ?_)
  have := ho a
  simpa [S, hYb] using this

end GlobalTheory.CompanionTheory.FineProd.CellMulti
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOrderBoundedHeckeSupport
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem det_mem_Ov {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)} (hM : IsInt w M) : M.det ∈ Ov E w := by
  have hN : M = (Ov E w).subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : Ov E w)) := by
    ext i j; rfl
  rw [hN, ← RingHom.map_det]
  exact SetLike.coe_mem _

private theorem v_eq_ofAdd_lemma {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (x : w.adicCompletion E) (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [ordL, dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem ordL_det_range : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ g : GL (Fin n) (w.adicCompletion E), IsInt w g.val → IsInt w (ϖ • (g⁻¹).val) → ∃ i ≤ n, ordL g.val.det = (i : ℤ) := by
  intro E _ _ w n ϖ hϖ g hg hgi
  have hd : g.val.det ∈ Ov E w := det_mem_Ov hg
  have hdi : (ϖ • (g⁻¹).val).det ∈ Ov E w := det_mem_Ov hgi
  have hmul : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hd0 : g.val.det ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hdi0 : (g⁻¹).val.det ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  rw [Matrix.det_smul, Fintype.card_fin] at hdi
  simp only [Ov, ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers] at hd hdi
  rw [map_mul, map_pow, show Valued.v ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from hϖ,
    v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_pow, ← WithZero.coe_mul, ← ofAdd_nsmul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le,
    nsmul_eq_mul, mul_neg, mul_one] at hdi
  rw [v_eq_ofAdd_lemma _ hd0, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at hd
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one, v_eq_ofAdd_lemma _ hd0, v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_mul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one] at hm
  refine ⟨(ordL g.val.det).toNat, ?_, ?_⟩
  · omega
  · omega

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCellStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_closed_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | exact GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one | (intros; apply GlobalTheory.CompanionTheory.BZRes.locSec_parab_mir_one <;> assumption)
end

