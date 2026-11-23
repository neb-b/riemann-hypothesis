module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceLinesRelatedAndVanishOffPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.ColsFB.cols_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dJ (σ + 1) h) (xFB F σ h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D _ T L μ0 _ sc G W M _ F hF σ h h' v hv i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ (σ + 1) h
  obtain ⟨hc', he', -⟩ := hF.hB σ h'
  have hz := hF.zB' σ h'
  have hζ := hF.ζ (σ + 1)
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  set t := a * incA D ((-D.host.xi0) ^ (i.1 + 1)) with ht
  have hL : FinPl.colMul (F.dJ (σ + 1) h).jX i a =
      fun k => t * incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k ⟨i.1, by omega⟩) := by
    funext k
    simp only [FinPl.colMul, HypDec.jX, GlobalTheory.MixModel.rat, he, colsOf, Matrix.map_apply, map_mul, ht]
    rw [← mul_assoc]
    rfl
  have hR : FinPl.colMul (xFB F σ h') i a =
      fun k => t * incA D ((G.colDec (2 * σ + 2) (by omega) h').a k ⟨i.1, by omega⟩) := by
    funext k
    induction i using Fin.lastCases with
    | last =>
      have e1 : (F.dB σ h').i₀ *ᵥ vecB (F.oB σ h') (F.ζ (σ + 1)) =
          (-D.host.xi0) ^ (σ + 1) • fun i => (G.colDec (2 * σ + 2) (by omega) h').a i ⟨σ, by omega⟩ := by
        rw [vecB, hζ, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hz]
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, e1, ratV, Pi.smul_apply,
        smul_eq_mul, map_mul, ht, Fin.val_last]
      rw [← mul_assoc]
    | cast j =>
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, he', colsOf,
        Matrix.map_apply, map_mul, ht, Fin.coe_castSucc]
      rw [← mul_assoc]
      rfl
  rw [hL, hR]
  have hΛ3 : G.Λ (.grid (2 * σ + 3) 0) = (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).lat
      (G.Λ (.core (2 * (σ + 1) + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)) :=
    G.sp.colLat _ _ _
  have hΛ2 : G.Λ (.grid (2 * σ + 2) 0) = (G.colDec (2 * σ + 2) (by omega) h').lat
      (G.Λ (.core (2 * σ + 2))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)) :=
    G.sp.colLat _ _ _
  rw [hΛ3, hΛ2, (_root_.GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).1,
    (_root_.GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2]
  have hst : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) ⟨i.1, by omega⟩ =
      D.host.AA * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) ⟨i.1, by omega⟩ *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    have e : 2 * (σ + 1) + 1 - 1 - i.1 = (2 * σ + 2 - 1 - i.1) + 1 := by have := i.2; omega
    simp only [stairId, e, Places.stA]
    ring
  rw [hst, _root_.GlobalTheory.ModBarOff.idV_mul_modulBar_inv G.pl sc hv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionMulModulusOffExceptiona
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.ModulUnit

variable {D : D7}

theorem exists_sep {v v' : GlobalTheory.FinPl.Pl D} (h : v' ≠ v) :
    ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hc))

theorem idV_eq_one_of_mem {v : GlobalTheory.FinPl.Pl D} {I : Ideal (𝓞 D.host.E)} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal)
    (hI : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ I) :
    GlobalTheory.SeeSaw.idV ((I : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 1 v := by
  refine le_antisymm (GlobalTheory.SeeSaw.idV_mono FractionalIdeal.coeIdeal_le_one v) ?_
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, h0, a, ha, rfl⟩
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  obtain ⟨h1, h2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht hα h0
  rw [GlobalTheory.IdVGen.tmul_eq ht α]
  refine AddSubgroup.subset_closure ⟨_, h1, h2, _, ?_, rfl⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, I.mul_mem_right o hI, ?_⟩
  rw [map_mul]
  rfl

theorem idV_mul_of_eq_one {𝔞 I : GlobalTheory.SeeSaw.FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : GlobalTheory.SeeSaw.idV I v = GlobalTheory.SeeSaw.idV 1 v) : GlobalTheory.SeeSaw.idV (𝔞 * I) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  rcases eq_or_ne 𝔞 0 with rfl | h0
  · rw [zero_mul]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h0
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 I x 1 hx0 one_ne_zero hx
    (GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 h)
  rw [mul_one] at this
  ext s
  rw [this, hx]

variable {T : Type} {L : LevCh D T}

theorem exists_mem_modul (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modul sc := by
  classical
  have hsep : ∀ v' ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ v'.asIdeal ∧ t ∉ v.asIdeal :=
    fun v' hv' => exists_sep fun e => hv (e ▸ hv')
  choose! t ht using hsep
  refine ⟨∏ v' ∈ P.S0, t v' ^ P.depth sc v', fun hm => ?_, ?_⟩
  · obtain ⟨v', hv', hm'⟩ := (haveI := v.isPrime; Ideal.IsPrime.prod_mem_iff.1 hm)
    exact (ht v' hv').2 (v.isPrime.mem_of_pow_mem _ hm')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' hv' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h : t v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hv']; exact (ht v' hv').1
    exact h
end GlobalTheory.ModulUnit

namespace GlobalTheory.ModulUnit

variable {D : D7} {T : Type} {L : LevCh D T}

theorem conj_smul_algebraMap (s : 𝓞 D.host.F) :
    D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
  apply RingOfIntegers.ext
  show D.host.conj ((s : D.host.F) : D.host.E) = ((s : D.host.F) : D.host.E)
  exact (D.host.conjE_mem_hostF_iff _).1 (s : D.host.F).2

theorem exists_mem_modulBar (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ s : 𝓞 D.host.F, s ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ P.modulBar sc := by
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  refine ⟨s, hs, ?_⟩
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  rwa [conj_smul_algebraMap] at this

end GlobalTheory.ModulUnit


open GlobalTheory.ModulUnit in
theorem GlobalTheory.ChiGrid.Places.idV_mul_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → ∀ 𝔞 : GlobalTheory.SeeSaw.FI D, GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v ∧ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞
  obtain ⟨s, hs, hm⟩ := exists_mem_modul P sc hv
  obtain ⟨s', hs', hm'⟩ := exists_mem_modulBar P sc hv
  exact ⟨idV_mul_of_eq_one (idV_eq_one_of_mem hs hm), idV_mul_of_eq_one (idV_eq_one_of_mem hs' hm')⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianVacuumHeisenbergDerivativeComplexStructu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
open scoped Classical

namespace GlobalTheory.GaussCancel

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem actsD_zero_of_neg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (r s r' s' : ℕ)
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W)
    (g : SInf F (Fin n × Fin d)) (ε' : InfinitePlace F → ℤˣ)
    (hε' : ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
      (∀ w, u'.map (piInf (B.emb w)) = (((ε' w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
      ∀ f f' : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) g f → ActsD (evI F) (M.heisLine B.ψ u') g f' →
        f' = Complex.I • f)
    (w : InfinitePlace F) (hw : ε' w = -1) (v : Matrix (Fin n) (Fin d) (AE F E)) (h : SInf F (Fin n × Fin d))
    (hD : ActsD (evI F) (M.heisLine B.ψ v) g h) : h = 0 := by
  by_cases hκ : n = 0 ∨ d = 0
  · refine GlobalTheory.T.heisenbergDerivative_zero_or_empty_eq_zero M B.ψ g h v hD (Or.inr ?_)
    rcases hκ with hκ | hκ
    · subst hκ; exact ⟨fun p => p.1.elim0⟩
    · subst hκ; exact ⟨fun p => p.2.elim0⟩
  push_neg at hκ
  obtain ⟨u, u', hu, hu', hrel, hneg⟩ :=
    GlobalTheory.T.exists_archimedean_pair_negative_symplectic_pairing B X W r s r' s' hB hX hW (Nat.pos_of_ne_zero hκ.1) (Nat.pos_of_ne_zero hκ.2) ε' w hw
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M B.ψ hB.std g u hu
  obtain ⟨f', hf'⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M B.ψ hB.std g u' hu'
  have hff := hε' u u' hu hu' hrel f f' hf hf'
  let ell : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    fun b =>
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ b)
      map_add' := fun x y => by simp only [add_dotProduct, map_add (f := _)]
      map_smul' := fun c x => by simp only [smul_dotProduct, map_smul, smul_eq_mul, RingHom.id_apply] }
  set a₁ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i)
  set a₂ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u').1 i)
  set b₁ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).2 i)
  set b₂ : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u').2 i)
  have hg0 : g = 0 := by
    refine _root_.GlobalTheory.WrongSignGauss.vanish g a₁ a₂ (ell b₁) (ell b₂) (fun y => ?_) ?_
    · have e1 := GlobalTheory.T.heisenbergLineDerivative_eq_directional_add_phase M B.ψ hB.std g f u hu hf y
      have e2 := GlobalTheory.T.heisenbergLineDerivative_eq_directional_add_phase M B.ψ hB.std g f' u' hu' hf' y
      have e3 : f' y = Complex.I * f y := by rw [hff]; rfl
      rw [e1, e2] at e3
      exact e3
    · have hform := M.co.form u u'
      have hev : evI F (GlobalTheory.WeilM.symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u') = a₁ ⬝ᵥ b₂ - a₂ ⬝ᵥ b₁ := by
        let evH : AF F →+* mixedEmbedding.mixedSpace F :=
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
            (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        have hevH : ∀ a : AF F, evI F a = evH a := fun a => rfl
        rw [hform, hevH]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [dotProduct, map_sub, map_sum, map_mul, a₁, a₂, b₁, b₂, hevH]
      change Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.WeilM.symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u')) < 0 at hneg
      rw [hev, map_sub] at hneg
      have c1 : (ell b₂) a₁ = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (a₁ ⬝ᵥ b₂) := rfl
      have c2 : (ell b₁) a₂ = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (a₂ ⬝ᵥ b₁) := rfl
      rw [c1, c2]
      exact hneg
  exact GlobalTheory.T.heisenbergDerivative_zero_or_empty_eq_zero M B.ψ g h v hD (Or.inl hg0)

end GlobalTheory.GaussCancel

theorem GlobalTheory.GaussCancel.heis_cancel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ g₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
            (M.heisLine Bs.ψ (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1))) g g₁' →
          g₁ + Complex.I • g₁' = 0 := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac τ z g₁ g₁' h₁ h₁'
  obtain ⟨ε', hε'⟩ := hg
  obtain ⟨w, hoff, hon⟩ :=
    _root_.GlobalTheory.PlaceLines.lines_at_place D θ hθ ε S X A B e Bs hBs Vs Ws r s r' s' hJ hJW hV hW hemb cS hcS τ z
  have hu := _root_.GlobalTheory.ArchLinePreimage.arch_symm_lineAt D θ hθ ε S X e cS hcS τ z
  have hu' := _root_.GlobalTheory.ArchLinePreimage.arch_symm_lineAt D θ hθ ε S X e cS hcS τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z)
  rcases Int.units_eq_one_or (ε' w) with h1 | h1
  · have key := hε' _ _ hu hu' (fun w' => by
      by_cases hw : w' = w
      · subst hw; rw [hon, h1]; simp
      · rw [(hoff w' hw).1, (hoff w' hw).2]; simp) g₁ g₁' h₁ h₁'
    rw [key, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel]
  · rw [GlobalTheory.GaussCancel.actsD_zero_of_neg Bs r s r' s' hBs hV hW M g ε' hε' w h1 _ g₁ h₁,
      GlobalTheory.GaussCancel.actsD_zero_of_neg Bs r s r' s' hBs hV hW M g ε' hε' w h1 _ g₁' h₁', smul_zero, add_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  first | exact @GlobalTheory.HoweRealSmall.howe_real_ker' | exact GlobalTheory.HoweRealSmall.howe_real_ker' | (intros; apply GlobalTheory.HoweRealSmall.howe_real_ker' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegral
section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKerLieV

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : (w : InfinitePlace F) → GlobalTheory.AdelicU.EmbOver E w)
    {Φ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → (v : Pl F) → (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        ∀ v ∉ T, φ i v = M.vac v) ∧
      Φ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  classical
  unfold GlobalTheory.SquareAgree.algD at hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    have hfin := Filter.eventually_cofinite.1 hv
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hvT => ?_⟩, by simp⟩
    by_contra h
    exact hvT (hfin.mem_toFinset.2 h)
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v (fun h => hv (Finset.mem_union_right _ h))⟩
    · rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.PolKerLieV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelSum
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem pure_sub {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

end GlobalTheory.PolKerCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSeventh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnCusp
variable {D : D7}


open GlobalTheory.Size in
theorem isCuspFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hU' : ∀ w, IsAutFun N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨(hx.aut w).toIsAutFun, hx.cusp w⟩
    | zero => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_zero _, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1 (hy w).1 (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.RowLift.isAutFun_smul (hx w).1 c, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  suffices H : IsAutFun N.V ((PiTensorProduct.lift U) v) ∧ IsCuspFun N.V ((PiTensorProduct.lift U) v) from H.2
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.RowLift.isAutFun_smul (hU' f).1 r, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

end GlobalTheory.DnCusp

namespace GlobalTheory.DnCusp

end GlobalTheory.DnCusp

end
end

