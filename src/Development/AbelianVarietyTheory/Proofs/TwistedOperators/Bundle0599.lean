module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelIndicatorTestFunctionFactorAtRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem coef_factor : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (q : NI V C), q ∈ GlobalTheory.FibreAtTau.offP θ V C τ → ∀ x y : GA D V, ∃ R : ℂ, ∀ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, coef θ M K v a (x * ((p * q : NI V C) : GA D V) * y) = ⟪v τ, M.rep τ (cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y) (a τ)⟫_ℂ * R := by
  intro D θ _ V S M K v a τ r C q hq x y
  classical
  rw [mem_offP] at hq
  have hcmp : ∀ τ' (g h : GA D V), cmp θ τ' (g * h) = cmp θ τ' g * cmp θ τ' h := fun τ' g h =>
    (GlobalTheory.RowReal.infMatHom V (θ τ')).map_mul g h
  refine ⟨if Lev.finE V (x * (q : GA D V) * y) ∈ K then
      ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' (x * (q : GA D V) * y)) (a τ')⟫_ℂ else 0, ?_⟩
  intro p hp
  rw [mem_atP] at hp
  have hfin : Lev.finE V (p : GA D V) = 1 := by
    have h1 : (p : GA D V) ∈ (⊥ : Subgroup (GL (Fin V.rank) (Lev.EAf D))).comap (Lev.finE V) := by
      rw [GlobalTheory.Mass.Levels.comap_finE]
      exact Subgroup.mem_sup_right hp.1
    simpa using h1
  have hF : Lev.finE V (x * ((p * q : NI V C) : GA D V) * y) = Lev.finE V (x * (q : GA D V) * y) := by
    simp only [Subgroup.coe_mul, map_mul, hfin, one_mul]
  simp only [coef, coefR, hF]
  split_ifs with h
  · have e1 : cmp θ τ (x * ((p * q : NI V C) : GA D V) * y) = cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y := by
      rw [Subgroup.coe_mul, hcmp, hcmp, hcmp, hq, mul_one]
    have e2 : ∀ τ' ∈ Finset.univ.erase τ,
        ⟪v τ', M.rep τ' (cmp θ τ' (x * ((p * q : NI V C) : GA D V) * y)) (a τ')⟫_ℂ =
          ⟪v τ', M.rep τ' (cmp θ τ' (x * (q : GA D V) * y)) (a τ')⟫_ℂ := by
      intro τ' hτ'
      have hp' := hp.2 τ' (Finset.ne_of_mem_erase hτ')
      rw [Subgroup.coe_mul, hcmp, hcmp, hcmp, hcmp, hcmp, hp', one_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), e1, Finset.prod_congr rfl e2]
  · simp

end GlobalTheory.FibreAtTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem movedVec_theta_fockVac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (p : Pair T), DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (movedVec t S d) ∧
      ∀ ρ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) (movedVec t S d) := by
  intro D T L sc G W U S t p hp d hd
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd
  have mem : (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).1 ∈ GfC (G.pS p) ∧
      (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | mu t i j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
    | core i => exact ⟨GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | top t j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
  exact GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ _ _ _ _ (W.om p) hom W.θ_is _ _ _ h1 h2 _ mem.1 _ mem.2

end GlobalTheory.RowReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowUnf

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem frameMat_isom (d : HermitianOrthogonalExtensionData A B c ε) : (frameMat B A d.ι)ᴴ * B.gram * frameMat B A d.ι = A.gram :=
  GlobalTheory.ChiGrid.SumDual.gram_isom A B d.ι d.isom

theorem perp_sub (d : HermitianOrthogonalExtensionData A B c ε) {k : ℕ} (f : Fin k → Fin c) :
    (frameMat B A d.ι)ᴴ * B.gram * d.a.submatrix id f = 0 := by
  refine Matrix.ext fun i j => ?_
  exact congrFun (congrFun d.perp i) (f j)

theorem gram_sub' (d : HermitianOrthogonalExtensionData A B c ε) {k l : ℕ} (f : Fin k → Fin c) (g : Fin l → Fin c) :
    (d.a.submatrix id f)ᴴ * B.gram * d.a.submatrix id g = (antiDiagonalSignGramMatrix c ε).submatrix f g :=
  d.gram_sub f g

def jacDec {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ) : HypDec B A σ where
  e := d.iso σ (by omega)
  e' := d.a.submatrix id fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev
  i₀ := frameMat B A d.ι
  ee := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e' := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hj : (j : ℕ) + 1 ≤ c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hsub : c - ((i : ℕ) + 1) + (i : ℕ) + 1 = c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  iso := frameMat_isom d
  i₀e := perp_sub d _
  i₀e' := perp_sub d _
  rank_add := by have := d.rank; omega

def midCol {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) : Matrix (Fin B.rank) (Fin 1) D.host.E :=
  d.a.submatrix id fun _ : Fin 1 => (⟨σ, by omega⟩ : Fin c)

def coreMat {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) :
    Matrix (Fin B.rank) (Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank) D.host.E :=
  (Matrix.fromCols (frameMat B A d.ι) (midCol d h)).submatrix id finSumFinEquiv.symm

theorem nLine_gram (i j : Fin 1) : (GlobalTheory.SeeSaw.Model.nLine D).gram i j = -1 := by
  show -((Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram i j) = -1
  rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
  simp [Examples₂.sgn]

theorem perp_sub' (d : HermitianOrthogonalExtensionData A B c ε) {k : ℕ} (f : Fin k → Fin c) :
    (d.a.submatrix id f)ᴴ * B.gram * frameMat B A d.ι = 0 := by
  have h := congrArg conjTranspose (perp_sub d f)
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
    ← Matrix.mul_assoc] at h

theorem coreMat_gram {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    (coreMat d h)ᴴ * B.gram * coreMat d h = (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).gram := by
  have hNN : (midCol d h)ᴴ * B.gram * midCol d h = (GlobalTheory.SeeSaw.Model.nLine D).gram := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => (?_ : _ = (-1 : D.host.E)).trans (nLine_gram i j).symm)
    simp only [submatrix_apply, antiDiagonalSignGramMatrix]
    rw [if_pos (by omega), if_true]
  have key : (Matrix.fromCols (frameMat B A d.ι) (midCol d h))ᴴ * B.gram * Matrix.fromCols (frameMat B A d.ι) (midCol d h) =
      Matrix.fromBlocks A.gram 0 0 (GlobalTheory.SeeSaw.Model.nLine D).gram := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, frameMat_isom,
      hNN]
    rw [show (frameMat B A d.ι)ᴴ * B.gram * midCol d h = 0 from perp_sub d _,
      show (midCol d h)ᴴ * B.gram * frameMat B A d.ι = 0 from perp_sub' d _]
    rfl
  refine Matrix.ext fun i j => ?_
  rw [GlobalTheory.Doubling.gram_hsum]
  exact congrFun (congrFun key _) _

theorem coreMat_perp {σ k : ℕ} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ + 1) (f : Fin k → Fin c) (hf : ∀ i, (f i).1 + σ + 1 ≠ c) :
    (coreMat d h)ᴴ * B.gram * d.a.submatrix id f = 0 := by
  have key : (Matrix.fromCols (frameMat B A d.ι) (midCol d h))ᴴ * B.gram * d.a.submatrix id f = 0 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul, perp_sub]
    rw [show (midCol d h)ᴴ * B.gram * d.a.submatrix id f = 0 from (gram_sub' d _ _).trans (Matrix.ext fun i j => by
      simp only [submatrix_apply, antiDiagonalSignGramMatrix, Matrix.zero_apply]
      rw [if_neg (by have := hf j; omega)])]
    exact fromRows_zero
  refine Matrix.ext fun i j => ?_
  exact congrFun (congrFun key _) j

def besDec {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) : HypDec B (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)) σ where
  e := d.iso σ (by omega)
  e' := d.a.submatrix id fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev
  i₀ := coreMat d h
  ee := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e' := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hj : (j : ℕ) + 1 ≤ c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.zero_apply]
    rw [if_neg (by omega)]
  e'e := by
    refine (gram_sub' d _ _).trans (Matrix.ext fun i j => ?_)
    have := i.2; have := j.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    have hsub : c - ((i : ℕ) + 1) + (i : ℕ) + 1 = c := by omega
    simp only [submatrix_apply, antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  iso := coreMat_gram d h
  i₀e := coreMat_perp d h _ fun i => by have := i.2; simp only [Fin.val_castLE]; omega
  i₀e' := coreMat_perp d h (fun i : Fin σ => (Fin.castLE (by omega : σ ≤ c) i).rev) fun i => by
    have := i.2
    have hi : (i : ℕ) + 1 ≤ c := by omega
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  rank_add := by have := d.rank; show A.rank + 1 + 2 * σ = B.rank; omega

section Grid

open GlobalTheory.FunObj

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem cocpt_top {j : ℕ} (hj : j ≤ D.R.m) : CoCpt (G.V (.top j)) := by
  have h := G.isV (X := .top j) hj fun i e => by cases e
  refine GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite h.sigOK fun τ => Or.inl ?_
  rw [h.sig τ, h.rank]
  simp [Node.neg]

def rowBes (j : ℕ) (hj : j < D.R.m) (σ : ℕ) (h : D.R.m - 1 - j = 2 * σ + 1) :
    HypDec (G.V (.grid D.R.m j)) (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ :=
  besDec (G.rowDec j hj) h

def rowJac (j : ℕ) (hj : j < D.R.m) (σ : ℕ) (h : D.R.m - 1 - j = 2 * σ) : HypDec (G.V (.grid D.R.m j)) (G.V (.top j)) σ :=
  jacDec (G.rowDec j hj) h

def topVolN (M : Vol G) (hM : M.IsRow) (hj : 0 < D.R.m) (h : D.R.m - 1 - 0 = 2 * ((D.R.m - 2) / 2) + 1) :
    VolN (rowBes G 0 hj ((D.R.m - 2) / 2) h) :=
  ⟨M.νN, M.fdN, hM.unip⟩

end Grid

end GlobalTheory.RowUnf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAdelicVolume
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.LineDerFunB

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  rw [algD, Submodule.mem_span_set'] at hΦ
  obtain ⟨m, c, g, rfl⟩ := hΦ
  choose f φ hf hφ hv hg using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem conjU_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

end GlobalTheory.SquareAgree.LineDerFunB


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSender
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.GridMeasDown

open GlobalTheory.GridJoin GlobalTheory.Grid

variable {D : D7}

theorem exch {V₁ V₂ : HSp D} (hV : SameSp V₂ V₁) (e : GA D V₁ = GA D V₂)
    {μ₁ : Measure (GA D V₁)} {F₁ : Set (GA D V₁)} {μ₂ : Measure (GA D V₂)} {F₂ : Set (GA D V₂)}
    (hμ : HEq μ₁ μ₂) (hH₂ : μ₂.IsHaarMeasure) (h1 : IsFundamentalDomain (GQ V₁) F₁ μ₁)
    (h2 : IsFundamentalDomain (GQ V₂) F₂ μ₂) (H : GA D V₂ → ℂ) (hH : ∀ γ ∈ GQ V₂, ∀ g, H (γ * g) = H g) :
    (IntegrableOn (fun g => H (cast e g)) F₁ μ₁ ↔ IntegrableOn H F₂ μ₂) ∧
      ∫ g in F₁, H (cast e g) ∂μ₁ = ∫ g in F₂, H g ∂μ₂ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl : μ₁ = μ₂ := eq_of_heq hμ
  exact GlobalTheory.FlipStart.Col.fund_exch (V := V₂) (μ := μ₁) h1 h2 H hH

theorem measFD_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : Lev.IsMeasFD V K μ F) (h₀ : Lev.IsMeasFD V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h.1 h₀.1)

theorem measDef_heq {V V₀ : HSp D} (hV : SameSp V₀ V) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : IsMeasDef V K μ F) (h₀ : IsMeasDef V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hV
  obtain rfl := eq_of_heq hK
  have h1 : Lev.IsMeasLevDef V₀ K μ := h.1
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (V := V₀) (fun _ _ e => e.1) h1 h₀.1)

theorem lev_heq {V V' : HSp D} (hsp : SameSp V V') {β : GL (Fin V'.rank) (Lev.EAf D)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hl : HEq Λ' Λ) (hf : Formalism.L2.DIV.IsFrame β Λ') :
    HEq (UA D.sp.cm V'.gram ⊓ St β) (GlobalTheory.ChiGrid.congLev D.sp.cm V.gram Λ ⊤) := by
  obtain ⟨L, hl1, hl2, rfl⟩ := hsp
  obtain rfl := eq_of_heq hl
  have hs := Formalism.L2.DIV.stabilizer_eq_stabilizer_lattice _ _ _ _ _ hf
  have h2 := GlobalTheory.ChiGrid.congLev_top (hc := D.sp.cm) (J := V.gram) (Λ := Λ')
  apply heq_of_eq
  rw [h2, hs]
  rfl

theorem cast_heq {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) :
    HEq (Node.MeasDat.cast h m).ν m.ν ∧ HEq (Node.MeasDat.cast h m).fd m.fd := by
  subst h; exact ⟨HEq.rfl, HEq.rfl⟩

theorem cast_fd {S S' : GlobalTheory.Grid.Node D} (h : S = S') (m : S.MeasDat) (hf : IsFundamentalDomain (GQ S.V) m.fd m.ν) :
    IsFundamentalDomain (GQ S'.V) (Node.MeasDat.cast h m).fd (Node.MeasDat.cast h m).ν := by
  subst h; exact hf

theorem meas_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {large₂ : SizeData₂ D}
    {F : Face D A}, GlobalTheory.RowClaim.HidaSetting large₂ R F → sc.cGap = 1 →
    ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (M : Vol G') (t : T), M.Is t → ∀ (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (e : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (H : GA D (G'.V (.grid i (j + 1))) → ℂ),
    (∀ γ ∈ GQ (G'.V (.grid i (j + 1))), ∀ g, H (γ * g) = H g) →
    (IntegrableOn (fun g => H (cast e g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ↔
      IntegrableOn H (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1)))) ∧
    ∫ g in (G.meas t i (j + 1)).fd, H (cast e g) ∂(G.meas t i (j + 1)).ν =
      ∫ g in M.fd (.grid i (j + 1)), H g ∂(M.ν (.grid i (j + 1))) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc large₂ F hS hc G' W hW G hG hJ M t hM i j hi hj e H hH
  have hAt := hM.vtx (.grid i (j + 1)) ⟨hi, by omega⟩
  obtain ⟨hHaar, hfd⟩ := hAt.haar_fund
  have hsp : SameSp (G'.V (.grid i (j + 1))) (G.V i (j + 1)).V := (hJ.1.vert i (j + 1) hi (by omega)).sp
  suffices key : HEq (G.meas t i (j + 1)).ν (M.ν (.grid i (j + 1))) ∧
      IsFundamentalDomain (GQ (G.V i (j + 1)).V) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν from
    exch hsp e key.1 hHaar key.2 hfd H hH
  unfold Vol.IsAt at hAt
  rcases i with _ | i
  · have hmod := hS.core.models
    by_cases h : j + 1 < D.R.m
    · have hT : G'.V (.grid 0 (j + 1)) = Yc D (j + 1) := congrArg LSp.sp (colY_lt R.toLevCh h)
      have hK : HEq (levJ G' t (.grid 0 (j + 1)))
          (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)) := levCol_lt R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeY_eq_chainVertexAtRowZero_of_lt R h) ⟨R.νY t (j + 1), R.fdY t (j + 1)⟩ := by
        show meas0 R t j = _
        rw [meas0, dite_eq_left h]
      rw [e0]
      rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h' | h'
      · have hc := hmod.νY t (j + 1) h'
        rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measFD_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
      · have e1 : j + 1 = D.R.m - 1 := by omega
        have hc := hmod.νY' t
        rw [← e1] at hc
        rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
        exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
    · have hj' : j + 1 = D.R.m := by omega
      have hT : G'.V (.grid 0 (j + 1)) = D.sp.X' := by
        show (columnBlock R.toLevCh (j + 1)).sp = _
        rw [hj', colY_m]
      have hK : HEq (levJ G' t (.grid 0 (j + 1))) (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) := levCol_top R.toLevCh t h
      have e0 : G.meas t 0 (j + 1) = Node.MeasDat.cast (nodeX_eq_chainVertexAtRowZero_of_ge R h) ⟨R.νX t, R.fdX t⟩ := by
        show meas0 R t j = _
        rw [meas0, dite_eq_right h]
      rw [e0]
      have hc := hmod.νX t
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨(cast_heq _ _).1.trans (GlobalTheory.FlipStart.Col.measDef_heq hT hK hAt hc).symm, cast_fd _ _ hc.2⟩
  · have hN := hJ.1.vert (i + 1) (j + 1) hi (by omega)
    have hm := hG.meas.vert i j hi (by omega)
    obtain ⟨c, hfr⟩ := (hG.spaces.vert i (j + 1) hi (by omega)).frame
    have hK : HEq ((G.nV i (j + 1)).princ ⊤) (levJ G' t (.grid (i + 1) (j + 1))) := by
      rw [GlobalTheory.Grid.Node.princ_top]
      exact lev_heq hN.sp hN.lat hfr.1
    show HEq (G.mV i (j + 1)).ν _ ∧ IsFundamentalDomain (GQ (G.nV i (j + 1)).V) (G.mV i (j + 1)).fd (G.mV i (j + 1)).ν
    by_cases hd : D.R.m - 1 ≤ j + 1
    · have h1 := hm.1 hd
      rw [if_pos (show (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measDef_heq hN.sp hK h1 hAt, h1.2⟩
    · have h1 := hm.2 hd
      rw [if_neg (show ¬ (GlobalTheory.ChiGrid.Node.grid (i + 1) (j + 1)).neg D.R.m = 0 by simp only [GlobalTheory.ChiGrid.Node.neg]; omega)] at hAt
      exact ⟨measFD_heq hN.sp hK h1 hAt, h1.2⟩

end GlobalTheory.GridMeasDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThThGAct
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LiftGroupEquiv.th_thG_act : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ t (g : G) (x : (A.fam.R t).S.Forms), R.Th t (R.jX t ((A.fam.R t).r g x)) = R.gE g (R.Th t (R.jX t x))) ∧ ∀ i t (g : G) (x : (A.fam.L i t).S.Forms), R.thG i t (R.jV i t ((A.fam.L i t).r g x)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t x)) := by
  intro hP D G _ _ Pl0 T0 A Ks _ _ _ R F hC
  have hRr : R.grp_red_R := hC.grp.red_R
  have hRl : R.grp_red_L := hC.grp.red_L
  have hMx : R.models_jX := hC.models.jX
  have hMv : R.models_jV := hC.models.jV
  refine ⟨fun t g x => ?_, fun i t g x => ?_⟩
  · have H1 := @GlobalTheory.FormAction.act_eq_translate D G _ _ Pl0 T0 A Ks _ _ _ R hRr hMx t g x
    exact H1.elim fun κ hh =>
      @_root_.GlobalTheory.ChainLiftEquiv.th_intertwines D G _ _ Pl0 T0 A Ks _ _ _ R F hC.lev hC.grp hC.fam hC.models hC.chain
        (fun t j _ => GlobalTheory.MultFinite.schurMult hP _ _) t g κ hh.1 _ _ hh.2
  · have H2 := @GlobalTheory.RationalFormsAction.act_eq_translate_lift_V D G _ _ Pl0 T0 A Ks _ _ _ R hRl hMv i t g x
    exact H2.elim fun κ hh => @_root_.GlobalTheory.ThetaProjEquiv.thG_intertwines_core D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t g κ hh.1 _ _ hh.2
end

