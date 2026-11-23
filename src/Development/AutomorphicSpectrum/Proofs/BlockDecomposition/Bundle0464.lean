module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatPtsUnn

def blkD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr k))

def blkA' {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  fun i k => M (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl k))

theorem det_eq_of_lowerLeft_zero {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (h : ∀ i j : Fin n, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    M.det = (blkA' M).det * (blkD M).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M,
    ← Matrix.fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)]
  have h0 : (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j; exact h i j
  rw [h0, Matrix.det_fromBlocks_zero₂₁]
  rfl

theorem mem_upperHalf {D : D7} {n : ℕ} (x : Fin (n + n) → AE D) :
    x ∈ upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i)) = 0 := by
  unfold upperHalf
  rw [LinearMap.mem_ker]
  exact funext_iff

end GlobalTheory.CompanionTheory.RatPtsUnn

namespace GlobalTheory.CompanionTheory.RatPtsUnn

theorem mulVec_inr {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (x : Fin (n + n) → R) (i : Fin n) :
    (M *ᵥ x) (finSumFinEquiv (Sum.inr i)) =
      (∑ j, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) +
        (blkD M *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  rfl

variable {D : D7} {n : ℕ}

theorem exists_ratEmb_of_mem {γ : G D n} (hγ : γ ∈ GF D n) :
    ∃ g0 : GRat D.sp.cm.sig (Jst D n), ratEmb _ _ g0 = γ := by
  have h : γ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := by rw [range_ratEmb]; exact hγ
  exact h

theorem mat_ratEmb (g0 : GRat D.sp.cm.sig (Jst D n)) :
    mat (ratEmb _ _ g0) = (g0.1 : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E).map (incA D) := rfl

theorem clause1 : ∀ γ ∈ GF D n, ∃ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det ∧
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g ∧ mat γ = g.map (incA D) := by
  intro γ hγ
  obtain ⟨g0, rfl⟩ := exists_ratEmb_of_mem hγ
  exact ⟨g0.1.1, (Matrix.isUnit_iff_isUnit_det _).1 g0.1.isUnit, g0.2, mat_ratEmb g0⟩

theorem clause2 : ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, IsUnit g.det →
      IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) g → ∃ γ ∈ GF D n, mat γ = g.map (incA D) := by
  intro g hg hu
  let u : GL (Fin (n + n)) D.host.E := ((Matrix.isUnit_iff_isUnit_det g).2 hg).unit
  have hu' : u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := hu
  refine ⟨ratEmb _ _ ⟨u, hu'⟩, ?_, rfl⟩
  have h : ratEmb D.sp.cm.sig (Jst D n) ⟨u, hu'⟩ ∈ (ratEmb D.sp.cm.sig (Jst D n)).range := ⟨_, rfl⟩
  rw [range_ratEmb] at h
  exact h

theorem mem_P_iff (γ : G D n) :
    γ ∈ P D n ↔ ∀ x : Fin (n + n) → AE D, x ∈ upperHalf D n ↔ mat γ *ᵥ x ∈ upperHalf D n := by
  unfold P
  rw [Subgroup.mem_comap]
  exact Iff.rfl

theorem clause3 : ∀ γ ∈ GF D n, ∀ g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = g.map (incA D) →
      (γ ∈ P D n ↔ IsSiegelP g) := by
  intro γ _ g hg
  rw [mem_P_iff, hg]
  constructor
  · intro h i j
    have hx : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
      rw [mem_upperHalf]
      intro k
      exact Pi.single_eq_of_ne (fun e => Sum.inr_ne_inl (finSumFinEquiv.injective e)) _
    have h2 := (mem_upperHalf _).1 ((h _).1 hx) i
    rw [Matrix.mulVec_single_one] at h2
    change incA D (g _ _) = 0 at h2
    exact incA_injective (h2.trans (map_zero _).symm)
  · intro hS
    have hM : ∀ i j : Fin n, g.map (incA D) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
      intro i j; rw [Matrix.map_apply, hS i j, map_zero]
    have hdet : IsUnit (blkD (g.map (incA D))).det := by
      have h1 : IsUnit (mat γ).det := by
        unfold mat
        exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
      rw [hg] at h1
      rw [det_eq_of_lowerLeft_zero _ hM] at h1
      exact isUnit_of_mul_isUnit_right h1
    have hinj : ∀ y : Fin n → AE D, blkD (g.map (incA D)) *ᵥ y = 0 → y = 0 := by
      intro y hy
      rw [← Matrix.one_mulVec y, ← Matrix.nonsing_inv_mul _ hdet, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]
    have hsum : ∀ (x : Fin (n + n) → AE D) (i : Fin n), (∑ j, g.map (incA D) (finSumFinEquiv (Sum.inr i))
        (finSumFinEquiv (Sum.inl j)) * x (finSumFinEquiv (Sum.inl j))) = 0 := fun x i =>
      Finset.sum_eq_zero fun j _ => by rw [hM i j, zero_mul]
    intro x
    rw [mem_upperHalf, mem_upperHalf]
    constructor
    · intro hx i
      rw [mulVec_inr]
      have h0 : (fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := funext hx
      rw [hsum, h0, Matrix.mulVec_zero, zero_add]
      rfl
    · intro hx
      have h0 : (blkD (g.map (incA D)) *ᵥ fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := by
        funext i
        have := hx i
        rw [mulVec_inr, hsum, zero_add] at this
        exact this
      have h1 := hinj _ h0
      exact fun i => congrFun h1 i

theorem ratPtsUnn : RatPts := fun _ _ => ⟨clause1, clause2, clause3⟩

end GlobalTheory.CompanionTheory.RatPtsUnn
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSiegelParabolicInvariance
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {R : Type} [CommRing R] {n : ℕ}

theorem block_matrix_mul_comm_ring (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blk4_map_alt {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem block_matrix_diagonal_one_eq_one : (blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1) = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_injective {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M : Matrix (Fin (n + n)) (Fin (n + n)) R =>
    M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.mp h2

theorem block_matrix_eta (g : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    g = blk4 (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
      (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ := by
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

end Blocks

theorem block_matrix_conj_transpose {K : Type} [Field K] [StarRing K] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b c d)ᴴ = blk4 aᴴ cᴴ bᴴ dᴴ := by
  unfold blk4
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

theorem jst_eq (n : ℕ) : Jst D n = blk4 0 1 (-1) 0 := rfl

theorem rat_form {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E)
    (hu : gᴴ * Jst D n * g = Jst D n)
    (hP : ∀ i j : Fin n, g (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    ∃ a b d : Matrix (Fin n) (Fin n) D.host.E, g = blk4 a b 0 d ∧ aᴴ * d = 1 ∧ dᴴ * a = 1 := by
  have hg := block_matrix_eta g
  set M := g.submatrix finSumFinEquiv finSumFinEquiv
  have hc : M.toBlocks₂₁ = 0 := by
    exact Matrix.ext fun i j => hP i j
  rw [hc] at hg
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₂, hg, ?_⟩
  rw [hg, jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring] at hu
  have h := block_matrix_injective hu
  simp at h
  exact ⟨h.1, h.2.1⟩

theorem sigR_incA (x : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [sigR, incA, inclR]

theorem lift_mem {n : ℕ} (g0 : GL (Fin (n + n)) D.host.E)
    (h : g0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n)) :
    Formalism.UG.bc (incA D) g0 ∈ HR (AF D.host.F) D.sp.cm.sig (Jst D n) := by
  have h' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1 * Jst D n * g0.1 = Jst D n := h
  show Formalism.UG.cT _ _ * _ * _ = _
  have e1 : Units.val (Formalism.UG.bc (incA D) g0) = g0.1.map (incA D) := rfl
  have e2 : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g0.1.map (incA D)) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g0.1).map (incA D) := by
    ext i j
    simp [Formalism.UG.cT, sigR_incA]
  rw [e1, e2, show JR (AF D.host.F) (Jst D n) = (Jst D n).map (incA D) from rfl, ← Matrix.map_mul,
    ← Matrix.map_mul, h']

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

theorem mat_mul' {n : ℕ} (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem rat_of_mem {n : ℕ} (p : G D n) (hp : p ∈ P D n ⊓ GF D n) :
    ∃ g0 : GL (Fin (n + n)) D.host.E, g0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) ∧
      mat p = g0.1.map (incA D) ∧
      ∀ i j : Fin n, g0.1 (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  obtain ⟨hpP, hpF⟩ := Subgroup.mem_inf.mp hp
  have hF : p.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (Jst D n) := hpF
  obtain ⟨g0, hg0, hg0p⟩ := Subgroup.mem_map.mp hF
  have hmat : mat p = g0.1.map (incA D) := by
    show p.1.1 = _
    rw [← hg0p]
    rfl
  refine ⟨g0, hg0, hmat, fun i j => ?_⟩
  apply incA_injective (D := D)
  rw [map_zero]
  have hst := (Subgroup.mem_comap.mp hpP)
  have key := (hst (Pi.single (finSumFinEquiv (Sum.inl j)) 1)).mp ?_
  · rw [upperHalf, LinearMap.mem_ker] at key
    have := congrFun key i
    simp only [LinearMap.funLeft_apply, Pi.zero_apply, Matrix.mulVec_single_one] at this
    change (mat p)ᵀ _ _ = 0 at this
    rw [hmat] at this
    exact this
  · rw [upperHalf, LinearMap.mem_ker]
    funext k
    simp only [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega) _

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open Matrix PositivityTheory.GramSchwartzFunctions.EC

variable {D : D7}

theorem adj_incA {n : ℕ} (d : Matrix (Fin n) (Fin n) D.host.E) :
    adj ((dᴴ).map (incA D)) = d.map (incA D) := by
  ext i j
  show cA D (incA D (star (d i j))) = incA D (d i j)
  rw [show cA D (incA D (star (d i j))) = incA D (star (star (d i j))) from rfl, star_star]

theorem ratLevi {n : ℕ} (a d : Matrix (Fin n) (Fin n) D.host.E) (had : aᴴ * d = 1) (hda : dᴴ * a = 1) :
    blk4 a 0 0 d * blk4 dᴴ 0 0 aᴴ = 1 ∧ blk4 dᴴ 0 0 aᴴ * blk4 a 0 0 d = 1 ∧
      (blk4 a 0 0 d)ᴴ * Jst D n * blk4 a 0 0 d = Jst D n := by
  have h1 : a * dᴴ = 1 := mul_eq_one_comm.mp hda
  have h2 : d * aᴴ = 1 := mul_eq_one_comm.mp had
  refine ⟨?_, ?_, ?_⟩
  · rw [block_matrix_mul_comm_ring]; simp [h1, h2, block_matrix_diagonal_one_eq_one]
  · rw [block_matrix_mul_comm_ring]; simp [had, hda, block_matrix_diagonal_one_eq_one]
  · rw [jst_eq, block_matrix_conj_transpose, block_matrix_mul_comm_ring, block_matrix_mul_comm_ring]; simp [had, hda]

theorem core {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hχ : IsHeckeChar D χ) (hω : IsWeilSch ψ χ θ V μ ω) (p : G D n) (hp : p ∈ P D n ⊓ GF D n)
    (Ψ : schwartzA θ V.rank n) : (ω p Ψ).1 0 = Ψ.1 0 := by
  obtain ⟨g0, hg0, hmat, hlow⟩ := rat_of_mem p hp
  obtain ⟨a, b, d, hg, had, hda⟩ := rat_form g0.1 hg0 hlow
  obtain ⟨hm1, hm2, hmU⟩ := ratLevi (D := D) (n := n) a d had hda
  let a0 : GL (Fin n) D.host.E := ⟨a, dᴴ, mul_eq_one_comm.mp hda, hda⟩
  let m0 : GL (Fin (n + n)) D.host.E := ⟨blk4 a 0 0 d, blk4 dᴴ 0 0 aᴴ, hm1, hm2⟩
  let mEl : G D n := ⟨Formalism.UG.bc (incA D) m0, lift_mem m0 hmU⟩
  let A : GL (Fin n) (AE D) := Formalism.UG.bc (incA D) a0
  have hmEl : mat mEl = blk4 A.1 0 0 (adj (A⁻¹).1) := by
    show (blk4 a 0 0 d).map (incA D) = blk4 (a.map (incA D)) 0 0 (adj ((dᴴ).map (incA D)))
    rw [blk4_map_alt, adj_incA, Matrix.map_zero _ (map_zero _)]
  let nEl : G D n := p * mEl⁻¹
  have hpe : p = nEl * mEl := by simp [nEl]
  have hinv : mat mEl⁻¹ = (blk4 dᴴ 0 0 aᴴ).map (incA D) := by
    simp only [mat, map_inv]
    rfl
  have hnEl : mat nEl = blk4 1 ((b * aᴴ).map (incA D)) 0 1 := by
    rw [mat_mul', hinv, hmat, hg, ← Matrix.map_mul, block_matrix_mul_comm_ring]
    have h1 : a * dᴴ = 1 := mul_eq_one_comm.mp hda
    have h2 : d * aᴴ = 1 := mul_eq_one_comm.mp had
    simp [h1, h2, blk4_map_alt]
  have hdet : Matrix.GeneralLinearGroup.det A = Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0) := by
    ext
    simp [A, Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [hpe, map_mul, Module.End.mul_apply, hω.unip nEl _ hnEl, hω.levi mEl A hmEl, hdet, hχ.2]
  have hab : absA D (Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a0)) = 1 :=
    absE_inclR _
  simp [npow, GlobalTheory.StdUnn.inner, halfTr]
  erw [hab]
  simp

end GlobalTheory.CompanionTheory.EisCellsPInv

namespace GlobalTheory.CompanionTheory.EisCellsPInv

open PositivityTheory.GramSchwartzFunctions.EC

theorem pInv : PositivityTheory.GramSchwartzFunctions.EC.PInv := by
  intro D n V ψ χ θ μ ω hS Φ γ hγ g
  have hχ : IsHeckeChar D χ := hS.2.2.2.1
  have hω : IsWeilSch ψ χ θ V μ ω := hS.2.2.2.2.2.2.2
  show (ω (γ * g) Φ).1 0 = (ω g Φ).1 0
  rw [map_mul, Module.End.mul_apply]
  exact core hχ hω γ hγ _

end GlobalTheory.CompanionTheory.EisCellsPInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupOfFinset
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_of_finset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ unipB k (Fin N) →
      ∃ L : Subgroup (GL (Fin N) k), L ≤ unipB k (Fin N) ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
        IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N s hs
  let c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  have heq : unipB k (Fin N) = GlobalTheory.InertSupp.unipOf k c := by
    ext g
    rw [GlobalTheory.SmGL.mem_unipB, GlobalTheory.InertSupp.mem_unipOf]
    constructor
    · rintro ⟨h1, h2⟩ i j hij
      have hji : j ≤ i := by
        dsimp [c] at hij
        rw [not_lt] at hij
        exact Fin.le_def.2 (by exact_mod_cast hij)
      rcases hji.lt_or_eq with h | h
      · rw [h1 i j h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h; rw [h2 j, Matrix.one_apply_eq]
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
          have := Fin.lt_def.1 hji
          omega
        rw [h i j this, Matrix.one_apply_ne (ne_of_gt hji)]
      · rw [h i i (lt_irrefl _), Matrix.one_apply_eq]
  have hQU : (↑s : Set (GL (Fin N) k)) ⊆ GlobalTheory.InertSupp.unipOf k c := by
    simpa [← heq] using hs
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (GlobalTheory.InertSupp.unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (GlobalTheory.UnipCptSub.isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ GlobalTheory.InertSupp.unipOf k c
      · left
        have key : ∀ x : GL (Fin N) k, x ∈ GlobalTheory.InertSupp.unipOf k c →
            (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
            ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
          intro x hx hd i j
          by_cases hij : c i < c j
          · refine (hd i j).mono ?_
            have : (m : ℤ) ≤ M := by exact_mod_cast hmM
            nlinarith
          · rw [GlobalTheory.InertSupp.mem_unipOf.1 hx i j hij]
            by_cases e : i = j
            · subst e
              simp [GlobalTheory.IwahoriInj.deep_zero_iff]
            · simp [Matrix.one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
        exact ⟨key g hu hg.1, key g⁻¹ (inv_mem hu) hg.2⟩
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : (↑s : Set (GL (Fin N) k)) ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := s.finite_toSet.isCompact.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipB k (Fin N), inf_le_right, ?_, ?_⟩
  · intro g hg
    refine ⟨?_, hs hg⟩
    rcases hM hg with h | h
    · exact h
    · exact absurd (hQU hg) h
  · rw [Subgroup.coe_inf]
    apply (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right
    rw [heq]
    exact GlobalTheory.UnipCompact.isClosed_unipOf _

end GlobalTheory.CompanionTheory.UnipExhaust
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenIntegralSubgroup
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevelU

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  intro E _ _ _ N L hL
  refine ⟨L.subgroupOf (AdelicGLn.integralFiniteGL E N), hL.preimage continuous_subtype_val, ?_⟩
  intro u
  exact ⟨_, Subgroup.mem_subgroupOf.1 u.2, GlobalTheory.CompanionTheory.AutLevel.finEmb_eq_finGL E N _⟩

end GlobalTheory.CompanionTheory.Conc.LevelU
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem absFin_minor_mul_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl (F := F)) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hκ : ∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) (f e : Fin n → ι) :
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  have hent : ∀ i j, absFin F v (compFin F E v ((X.1 * κ) i j)) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) := by
    intro i j
    have h1 : compFin F E v ((X.1 * κ) i j) = ((X.1.map (compFin F E v)) * (κ.map (compFin F E v))) i j := by
      rw [← Matrix.map_mul]; rfl
    rw [h1]
    refine (absFin_le_normFin F v _ i j).trans ((normFin_mul_le F v _ _).trans ?_)
    have h2 : normFin F v (κ.map (compFin F E v)) ≤ 1 := (normFin_le_iff F v).2 fun a b => hκ a b
    exact (mul_le_of_le_one_right' h2).trans (le_htOf (normFin F v) (Formalism.UG.bc (compFin F E v) X))
  rw [RingHom.map_det, Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun σ _ => ?_
  have hprod : absFin F v (∏ i : Fin n, ((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i)
      ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
    calc _ ≤ ∏ i : Fin n, absFin F v (((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, htFin F v (Formalism.UG.bc (compFin F E v) X) :=
          Finset.prod_le_prod' fun i _ => hent _ _
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hprod
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hprod

end GlobalTheory.CompanionTheory.GodementH
end

