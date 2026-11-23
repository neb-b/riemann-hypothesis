module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixAddIntegralReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.FrameAdjAdd

theorem frMapAdj_add_isIntM_redM : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T),
  IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapAdj S T βS βT y) →
  IsIntM (frMapAdj S T βS βT (x + y)) ∧
  ∀ PP : Pl D.host.E, redM PP (frMapAdj S T βS βT (x + y)) = redM PP (frMapAdj S T βS βT x) + redM PP (frMapAdj S T βS βT y) := by
  intro D S T βS βT x y hx hy
  have hadd : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
    unfold frMapAdj
    rw [Matrix.map_add (⇑(cA D)) (map_add (cA D)), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.map_add (⇑(toEAf D)) (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]
  have hI : IsIntM (frMapAdj S T βS βT (x + y)) := by
    intro i j
    rw [hadd]
    exact add_mem (hx i j) (hy i j)
  refine ⟨hI, fun PP => ?_⟩
  ext i j
  have h1 := hI i j
  have h2 := hx i j
  have h3 := hy i j
  simp only [redM, Matrix.add_apply, dif_pos h1, dif_pos h2, dif_pos h3]
  rw [← RingHom.map_add (f := _)]
  congr 1
  apply Subtype.ext
  simp [hadd]

end GlobalTheory.FrameAdjAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegmentStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment : ∀ (q : ℂˣ) (n n' : ℕ), n ≤ n' → ∀ α : Fin (n / 2) → ℂˣ, (bcParam n' (liftPar q n n' α)).map (fun x => ((-1 : ℂˣ) ^ n)⁻¹ * x) = (bcParam n α).map (fun x => ((-1 : ℂˣ) ^ n')⁻¹ * x) + str q ((n' : ℤ) - n) := by
  first | exact @GlobalTheory.SphTheta.bcParam_liftPar | exact GlobalTheory.SphTheta.bcParam_liftPar | (intros; apply GlobalTheory.SphTheta.bcParam_liftPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ}

theorem mt_emb_one (o : OrthDec S₀ A L) : mt S₀ (o.emb (1, 1)) = 1 := by
  rw [show ((1 : GA D A), (1 : GA D L)) = 1 from rfl, map_one, mt_one]

theorem mt_emb_mul (o : OrthDec S₀ A L) (h h' : GA D A) :
    mt S₀ (o.emb (h * h', 1)) = mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h', 1)) := by
  rw [← mt_mul, ← map_mul, Prod.mk_mul_mk, mul_one]

def Good (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A)) (g : GA D S) : Prop :=
  (∃ M : GL (Fin ρ) (AE D), mt S g * d.jX = d.jX * M.1) ∧
    ∃ h ∈ T, ∃ B : Mx D ρ S₀.rank, mt S g * d.j0 = d.j0 * mt S₀ (o.emb (h, 1)) + d.jX * B

section Good

variable (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (T : Subgroup (GA D A))

theorem good_one : Good d o T 1 :=
  ⟨⟨1, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩,
    1, T.one_mem, 0, by rw [mt_one, Matrix.one_mul, mt_emb_one, Matrix.mul_one, Matrix.mul_zero, add_zero]⟩

theorem good_mul {g g' : GA D S} (hg : Good d o T g) (hg' : Good d o T g') : Good d o T (g * g') := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  obtain ⟨⟨M', hM'⟩, h', hT', B', hB'⟩ := hg'
  refine ⟨⟨M * M', ?_⟩, h * h', T.mul_mem hT hT', B * mt S₀ (o.emb (h', 1)) + M.1 * B', ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, hM', ← Matrix.mul_assoc, hM, Matrix.mul_assoc, Units.val_mul]
  · rw [mt_mul, Matrix.mul_assoc, hB', Matrix.mul_add, ← Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hM, mt_emb_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]

theorem good_inv {g : GA D S} (hg : Good d o T g) : Good d o T g⁻¹ := by
  obtain ⟨⟨M, hM⟩, h, hT, B, hB⟩ := hg
  have hI : mt S g⁻¹ * mt S g = 1 := mt_inv_mul S g
  have hMM : (M.1 : Mx D ρ ρ) * (M⁻¹).1 = 1 := M.mul_inv
  have hX : mt S g⁻¹ * d.jX = d.jX * (M⁻¹).1 := by
    calc mt S g⁻¹ * d.jX = mt S g⁻¹ * (d.jX * M.1) * (M⁻¹).1 := by
          rw [Matrix.mul_assoc (mt S g⁻¹), Matrix.mul_assoc d.jX, hMM, Matrix.mul_one]
      _ = d.jX * (M⁻¹).1 := by rw [← hM, ← Matrix.mul_assoc, hI, Matrix.one_mul]
  refine ⟨⟨M⁻¹, hX⟩, h⁻¹, T.inv_mem hT, -((M⁻¹).1 * B * mt S₀ (o.emb (h⁻¹, 1))), ?_⟩
  have hH : mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h⁻¹, 1)) = 1 := by
    rw [← mt_emb_mul, mul_inv_cancel, mt_emb_one]
  have h1 : mt S g⁻¹ * d.j0 * mt S₀ (o.emb (h, 1)) + d.jX * (M⁻¹).1 * B = d.j0 := by
    have h2 : mt S g⁻¹ * (mt S g * d.j0) = d.j0 := by rw [← Matrix.mul_assoc, hI, Matrix.one_mul]
    rw [hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX] at h2
    exact h2
  calc mt S g⁻¹ * d.j0 = mt S g⁻¹ * d.j0 * mt S₀ (o.emb (h, 1)) * mt S₀ (o.emb (h⁻¹, 1)) := by
        rw [Matrix.mul_assoc _ (mt S₀ _), hH, Matrix.mul_one]
    _ = (d.j0 - d.jX * (M⁻¹).1 * B) * mt S₀ (o.emb (h⁻¹, 1)) := by rw [eq_sub_of_add_eq h1]
    _ = _ := by simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]

def goodSub : Subgroup (GA D S) where
  carrier := {g | Good d o T g}
  one_mem' := good_one d o T
  mul_mem' := fun {g g'} hg hg' => good_mul d o T (g := g) (g' := g') hg hg'
  inv_mem' := fun {g} hg => good_inv d o T (g := g) hg

end Good

end GlobalTheory.BesProj

namespace GlobalTheory.BesProj

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

theorem eH_gram_i₀ : d.eᴴ * S.gram * d.i₀ = 0 := by
  have := congrArg Matrix.conjTranspose d.i₀e
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at this

theorem flagN_le_goodSub (T : Subgroup (GA D A)) : flagN d ≤ goodSub d o T := by
  show Subgroup.closure _ ≤ _
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨h1, h2⟩
  choose a ha1 ha2 using h1
  have hz : ∀ k : Fin S₀.rank, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * S.gram).mulVec
      (fun l => d.i₀ l k) = 0 := by
    intro k; funext j
    exact congrFun (congrFun (eH_gram_i₀ d) j) k
  choose b hb using fun k => h2 _ (hz k)
  let U : Mx D ρ ρ := Matrix.of fun j i => a i j
  let B : Mx D ρ S₀.rank := Matrix.of fun i k => b k i
  have hU : (mt S g - 1) * d.jX = d.jX * U := by
    ext k i
    exact congrFun (ha2 i) k
  have hB : (mt S g - 1) * d.j0 = d.jX * B := by
    ext k i
    exact congrFun (hb i) k
  have hdet : (1 + U).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [U, ha1 i i le_rfl]
    · intro i j hji
      have hij : i ≠ j := ne_of_gt hji
      simp [U, ha1 j i hji.le, Matrix.one_apply_ne hij]
  have hdu : IsUnit (1 + U).det := by rw [hdet]; exact isUnit_one
  let M : GL (Fin ρ) (AE D) := ⟨1 + U, (1 + U)⁻¹, Matrix.mul_nonsing_inv _ hdu, Matrix.nonsing_inv_mul _ hdu⟩
  refine ⟨⟨M, ?_⟩, 1, T.one_mem, B, ?_⟩
  · show mt S g * d.jX = d.jX * (1 + U)
    rw [Matrix.mul_add, Matrix.mul_one, ← hU, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  · rw [mt_emb_one, Matrix.mul_one, ← hB, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

theorem embA_mem_goodSub (h : GA D A) : embA d o h ∈ goodSub d o ⊤ :=
  ⟨⟨1, by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩, h, Subgroup.mem_top h, 0,
    by rw [embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_zero, add_zero]⟩

theorem besGrp_le_goodSub : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) ≤ goodSub d o ⊤ :=
  sup_le (flagN_le_goodSub d o ⊤) (by rintro _ ⟨h, rfl⟩; exact embA_mem_goodSub d o h)

def matP (g : GA D S) : Mx D A.rank A.rank := o.pA * (d.p0 * mt S g * d.j0) * o.jA

theorem bessel_flag_stabilizer_anisotropic_block_exists {T : Subgroup (GA D A)} {g : GA D S} (hg : g ∈ goodSub d o T) :
    ∃ h ∈ T, d.p0 * mt S g * d.j0 = mt S₀ (o.emb (h, 1)) := by
  obtain ⟨-, h, hT, B, hB⟩ := hg
  refine ⟨h, hT, ?_⟩
  rw [Matrix.mul_assoc, hB, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.one_mul,
    Matrix.zero_mul, add_zero]

theorem pA_emb_jA (h : GA D A) : o.pA * mt S₀ (o.emb (h, 1)) * o.jA = mt A h := by
  rw [Matrix.mul_assoc, o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]

theorem anisotropicBlock_unitary {g : GA D S} (hg : g ∈ (flagN d ⊔ (embA d o).range : Subgroup (GA D S))) :
    adj (matP d o g) * (gA A * matP d o g) = gA A := by
  obtain ⟨h, -, hh⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (besGrp_le_goodSub d o hg)
  rw [matP, hh, pA_emb_jA]
  exact mt_unitary A h

theorem anisotropicBlock_mul_embA (n : flagN d) (h : GA D A) : matP d o (n.1 * embA d o h) = mt A h := by
  obtain ⟨h', hh', hn⟩ := bessel_flag_stabilizer_anisotropic_block_exists d o (flagN_le_goodSub d o ⊥ n.2)
  rw [Subgroup.mem_bot] at hh'
  rw [hh', mt_emb_one] at hn
  have : d.p0 * mt S (n.1 * embA d o h) * d.j0 = mt S₀ (o.emb (h, 1)) := by
    rw [mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hn,
      Matrix.one_mul]
  rw [matP, this, pA_emb_jA]

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    ∃ p : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) → GA D A, Continuous p ∧
      ∀ (h : GA D A) (n : flagN d), p ⟨n.1 * embA d o h, mul_mem (Subgroup.mem_sup_left n.2)
        (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ A L ρ d o
  refine ⟨fun g => ofMat A (matP d o g.1) (anisotropicBlock_unitary d o g.2), ?_, fun h n => ?_⟩
  · refine continuous_of_mt A ?_
    show Continuous fun g : (flagN d ⊔ (embA d o).range : Subgroup (GA D S)) => matP d o g.1
    exact (continuous_const.matrix_mul ((continuous_const.matrix_mul ((continuous_mt S).comp continuous_subtype_val)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  · exact mt_injective A (by rw [mt_ofMat]; exact anisotropicBlock_mul_embA d o n h)

end GlobalTheory.BesProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7}

theorem blkGL_mem (V V₁ : HSp D) (g : GA D V × GA D V₁) :
    blkGL finSumFinEquiv (g.1.1, g.2.1) ∈ HR (AF D.host.F) D.sp.cm.sig (hsum V V₁).gram := by
  have hJ : JR (F := D.host.F) (AF D.host.F) (hsum V V₁).gram =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) V.gram) (JR (F := D.host.F) (AF D.host.F) V₁.gram) := by
    unfold JR
    rw [gram_hsum]
    exact blkMat_map _ _ (map_zero _) _ _
  unfold HR
  rw [hJ]
  exact (blkGL_mem_UJ finSumFinEquiv).2 ⟨g.1.2, g.2.2⟩

def blk (V V₁ : HSp D) : GA D V × GA D V₁ →* GA D (hsum V V₁) where
  toFun g := ⟨blkGL finSumFinEquiv (g.1.1, g.2.1), blkGL_mem V V₁ g⟩
  map_one' := Subtype.ext (map_one (blkGL finSumFinEquiv))
  map_mul' g h := Subtype.ext (map_mul (blkGL finSumFinEquiv) (g.1.1, g.2.1) (h.1.1, h.2.1))

theorem mt_blk (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    Formalism.L2.Theta.mt (hsum V V₁) (blk V V₁ (g, g₁)) =
      blkMat finSumFinEquiv (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁) := rfl

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]; exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases h : a = b
        · subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']
        · simp [Formalism.REAL.Jm, h]
      show (A.fr τ)ᴴ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = gramAt D (neg V) τ
      rw [e, e', ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

def frSum {V V₁ : HSp D} (A : Fr V) (B : Fr V₁) : Fr (hsum V V₁) where
  ε τ := Fin.append (A.ε τ) (B.ε τ)
  fr τ := blkMat finSumFinEquiv (A.fr τ) (B.fr τ)
  fr_unit τ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_blkMat]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)).mul ((Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ))
  fr_gram τ := by
    have e : gramAt D (hsum V V₁) τ = blkMat finSumFinEquiv (gramAt D V τ) (gramAt D V₁ τ) := by
      unfold gramAt
      rw [gram_hsum]; exact blkMat_map _ _ (map_zero _) _ _
    have e' : Formalism.REAL.Jm (Fin.append (A.ε τ) (B.ε τ)) =
        blkMat finSumFinEquiv (Formalism.REAL.Jm (A.ε τ)) (Formalism.REAL.Jm (B.ε τ)) := by
      refine submatrix_inj finSumFinEquiv ?_
      rw [submatrix_blkMat]
      ext (a | a) (b | b) <;> simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Fin.ext_iff] <;> omega
    have e'' : (blkMat finSumFinEquiv (A.fr τ) (B.fr τ))ᴴ = blkMat finSumFinEquiv (A.fr τ)ᴴ (B.fr τ)ᴴ := by
      simp [GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
    rw [e, e', e'', blkMat_mul, blkMat_mul, A.fr_gram, B.fr_gram]

section Vec

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)

def IsFinF (f : WO M X → ℂ) : Prop := IsVacF ψ θ (frSgn ε A) B f

def fockF (f : WO M X → ℂ) : PolF D X.rank M.rank →ₗ[ℂ] (WO M X → ℂ) :=
  pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart A.onb B.onb f

def algF : Submodule ℂ (WO M X → ℂ) := Submodule.span ℂ {Φ | ∃ f P, IsFinF ψ θ ε A B f ∧ Φ = fockF ψ θ ε A B f P}

end Vec

def IsHaarFD (M : HSp D) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ M) 𝓕 ν

def thetaInt {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) (h : GA D X) : ℂ :=
  ∫ g in 𝓕, thetaKO ω g h Φ ∂ν

def ModInt (θ : InfFam D) {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) : Prop :=
  ∃ (N : ℕ) (C : ℝ), ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν ∧
    ∫ g in 𝓕, ‖thetaKO ω g h Φ‖ ∂ν ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N

def finRel {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) : Submodule ℂ (WO M X → ℂ) :=
  Submodule.span ℂ {Φ | ∃ u ∈ GfC M, ∃ Ψ ∈ S, Φ = ω (u, 1) Ψ - Ψ}

structure IsTriple (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle) : Prop where

  hecA : IsHeckeChar D α

  hecB : IsHeckeChar D β

  resA : ResEta D α W₁.rank

  resB : ResEta D β W.rank

  rank : X.rank = W.rank + W₁.rank

  even : Even X.rank

  sig : ∃ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) ∧
    W₁.rank + 2 * (2 * (p + q) + 1) < W.rank ∧ 2 * (p + q) + 1 < W₁.rank

  gap : ∀ τ, ∃ a b : ℚ, HasInfExp D α τ a ∧ HasInfExp D β τ b ∧ 2 * (a - b) < -(X.rank : ℚ)

  ram : ∀ v e, IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e α ∧ GlobalTheory.WeilParts.UnramAt e β) ∨
    (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (α / β) ∧
      ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F))

structure IsMatch (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) : Prop where

  weilA : IsWeil ψ true W X β (β / α) ωA

  weilB : IsWeil ψ false W₁ X α (α / β) ωB

  irred : IsIrred X Pi rf rl

  mapA : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p

  mapB : IsCoinvMap θ ωB (algF ψ θ false A₁ B) Pi rf rl p'

end GlobalTheory.SquareComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardGLDivParabolicIndexFiniteField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.Twist.GLIndexLoc

theorem card_GL_real_eq (κ : Type) [Field κ] [Finite κ] (n : ℕ) :
    (Nat.card (GL (Fin n) κ) : ℝ) =
      (Nat.card κ : ℝ) ^ (n ^ 2) * ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  haveI := Fintype.ofFinite κ
  have hq1 : 1 ≤ Nat.card κ := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  rw [Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [hIoc, Finset.prod_map, sq, pow_mul,
    show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n := Nat.pow_le_pow_right hq1 (by omega)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
  congr 1
  have hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]

theorem index_loc : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ), n = r + t → (Nat.card (GL (Fin n) κ) : ℝ) / ((Nat.card (GL (Fin t) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * t)) * ((Nat.card κ : ℝ) ^ (r ^ 2 + r * t))⁻¹ = ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  intro κ _ _ n r t hn
  haveI := Fintype.ofFinite κ
  have hq2 : (2 : ℝ) ≤ Nat.card κ := by
    have := Fintype.one_lt_card (α := κ)
    rw [← Nat.card_eq_fintype_card] at this
    exact_mod_cast this
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  have hP : ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi1 : 1 ≤ i := (Finset.mem_Ioc.mp hi).1
    have : (2 : ℝ) ≤ (Nat.card κ : ℝ) ^ i :=
      le_trans hq2 (le_self_pow₀ (by linarith) (by omega))
    have : ((Nat.card κ : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  rw [card_GL_real_eq, card_GL_real_eq,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (show t ≤ n by omega)]
  have hpow : (Nat.card κ : ℝ) ^ (n ^ 2) =
      (Nat.card κ : ℝ) ^ (t ^ 2) * (Nat.card κ : ℝ) ^ (r * t) * (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) := by
    rw [← pow_add, ← pow_add]; congr 1; subst hn; ring
  rw [hpow]
  generalize ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = P at hP ⊢
  generalize ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = Q
  have h1 : (Nat.card κ : ℝ) ^ (t ^ 2) ≠ 0 := pow_ne_zero _ hq0
  have h2 : (Nat.card κ : ℝ) ^ (r * t) ≠ 0 := pow_ne_zero _ hq0
  have h3 : (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) ≠ 0 := pow_ne_zero _ hq0
  field_simp

end GlobalTheory.Twist.GLIndexLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalL
section
open MeasureTheory

namespace GlobalTheory

theorem contDiff_toCLM_of_continuous_oneParameter {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W)
    (hc : ∀ w, Continuous fun t => A t w) (hadd : ∀ s t, A (s + t) = (A s).comp (A t)) (h0 : A 0 = LinearMap.id) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  have hT : Continuous fun t => LinearMap.toContinuousLinearMap (A t) :=
    continuous_clm_apply.2 fun w => by simpa using hc w
  refine contDiff_of_continuous_oneParameter (W →L[ℝ] W) _ hT ?_ ?_
  · ext w; simp [h0]
  · intro s t; ext w; simp [hadd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSkewElementUnitAtFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v),
    (∀ a : AF F, π (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) →
    ∃ δ : E, σ δ = -δ ∧ ∃ u : (v.adicCompletionIntegers F)ˣ,
      ((u : v.adicCompletionIntegers F) : Fv F v) = π (inclR (F := F) (AF F) δ) := by
  first | exact @GlobalTheory.CMSkewUnit.exists_skew_unit_at | exact GlobalTheory.CMSkewUnit.exists_skew_unit_at | (intros; apply GlobalTheory.CMSkewUnit.exists_skew_unit_at <;> assumption)
end

