module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePoint
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBx

open GlobalTheory.Unf.FB (mul_mul_mul_of_gram selFirst lastE ell_succ_eq)

variable {D : D7} {σ : ℕ}

def xRat (B : BesL D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem zEll_eq_rat (B : BesL D σ) : zEll B.L (σ + 1) B.ζ = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_xRat (B : BesL D σ) : rat (xRat B) = xLast B.d (vecB B.o B.ζ) := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [xRat, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [xRat, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_xRat (B : BesL D σ) :
    (xRat B)ᴴ * B.V.gram * xRat B =
      (vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ) := by
  have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.ee
  have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.i₀e
  have hX0 : B.d.eᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
  have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.iso
  have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.o.isoB
  have hz : vecMulVec (vecB B.o B.ζ) (lastE D σ) = B.o.iB * vecMulVec B.ζ (lastE D σ) := by
    rw [vecB, mul_vecMulVec]
  rw [xRat, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_xRat (B : BesL D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (xRat B) : Mx D B.V.rank (σ + 1)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ) := by
  rw [zEll_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_xRat B), gram_rat B.L rfl]

theorem linearIndependent_xRat (B : BesL D σ) : LinearIndependent D.host.E (xRat B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : xRat B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * xRat B = selFirst D σ := by
    rw [xRat, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_xRat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec]
      at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 B.line.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem exists_rat_eq_xLast : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x ∈ {x : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E |
    LinearIndependent D.host.E x.transpose ∧ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zEll B.L (σ + 1) B.ζ)}, (rat x : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) :=
  fun _ _ B => ⟨xRat B, ⟨linearIndependent_xRat B, gramSkew_xRat B⟩, rat_xRat B⟩

end GlobalTheory.Asc.FBx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacUnip

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

def uni (Z : Matrix n n A) : Matrix (n ⊕ n) (n ⊕ n) A := Matrix.fromBlocks (1 + Z) (-Z) Z (1 - Z)

theorem uni_mul_uni_neg (Z : Matrix n n A) : uni Z * uni (-Z) = 1 := by
  rw [uni, uni, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> noncomm_ring

def uniGL (Z : Matrix n n A) : GL (n ⊕ n) A :=
  ⟨uni Z, uni (-Z), uni_mul_uni_neg Z, by simpa using uni_mul_uni_neg (-Z)⟩

theorem uni_unitary (c : A →ₐ[R] A) (J Z : Matrix n n A) (h : Zᵀ * J + J * Z.map c = 0) :
    (uni Z)ᵀ * dbl J * (uni Z).map c = dbl J := by
  have h1 : (1 + Z).map c = 1 + Z.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h2 : (1 - Z).map c = 1 - Z.map c := by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : (-Z).map c = - Z.map c := by
    ext i j; simp
  have h4 : J * Z.map c = - (Zᵀ * J) := eq_neg_of_add_eq_zero_right h
  rw [uni, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, h1, h2, h3, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_neg]
  generalize Z.map c = Zc at *
  generalize Zᵀ = Zt at *
  congr 1
  · calc _ = J + (Zt * J + J * Zc) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = - (Zt * J + J * Zc) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  · calc _ = -J + (Zt * J + J * Zc) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem uni_mul_diagCols (Z : Matrix n n A) : uni Z * (diagCols n : Matrix (n ⊕ n) n A) = diagCols n := by
  rw [uni, diagCols, Matrix.fromBlocks_mul_fromRows]
  congr 1 <;> simp

theorem smul_uni_sub_one (u : R) (Z : Matrix n n A) (h : u • Z = 0) : u • (uni Z - 1) = 0 := by
  have h' : ∀ i j, u • Z i j = 0 := fun i j => congrFun (congrFun h i) j
  ext (i | i) (j | j) <;> simp [uni, Matrix.one_apply, h']

theorem uni_mulVec_inl (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inl = z ∘ Sum.inl + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_sub]
  abel

theorem uni_mulVec_inr (Z : Matrix n n A) (z : n ⊕ n → A) :
    (uni Z *ᵥ z) ∘ Sum.inr = z ∘ Sum.inr + Z *ᵥ (z ∘ Sum.inl - z ∘ Sum.inr) := by
  rw [uni, Matrix.fromBlocks_mulVec, Sum.elim_comp_inr, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_sub]
  abel

theorem blocks_uni_mul (Z : Matrix n n A) (g : Matrix (n ⊕ n) (n ⊕ n) A) :
    (uni Z * g).toBlocks₁₁ + (uni Z * g).toBlocks₁₂ + (uni Z * g).toBlocks₂₁ + (uni Z * g).toBlocks₂₂ =
      g.toBlocks₁₁ + g.toBlocks₁₂ + g.toBlocks₂₁ + g.toBlocks₂₂ +
        (Z + Z) * (g.toBlocks₁₁ + g.toBlocks₁₂ - g.toBlocks₂₁ - g.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g, uni, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  noncomm_ring

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_invOf_two_mem {v : Pl (F := F)} (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h0 : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [h0, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [map_inv₀, h2]

theorem uni_mulVec_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (Z : Matrix (Fin d) (Fin d) (AE F E))
    (hZ : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ GlobalTheory.DblVac.latD W v, uni Z *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [uni_mulVec_inl]; exact add_mem hz.1 (hZ _ (sub_mem hz.1 hz.2))
  · rw [uni_mulVec_inr]; exact add_mem hz.2 (hZ _ (sub_mem hz.1 hz.2))

theorem mul_mem_KD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {p g : GlobalTheory.DblVac.UD σ W}
    (hp : p ∈ GlobalTheory.DblVac.KD σ W v) (hg : g ∈ GlobalTheory.DblVac.KD σ W v) : p * g ∈ GlobalTheory.DblVac.KD σ W v := by
  have hm : ∀ a b : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * b) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD b :=
    fun _ _ => rfl
  refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · have e : GlobalTheory.DblVac.matD (p * g) - 1 =
        (GlobalTheory.DblVac.matD p - 1) * GlobalTheory.DblVac.matD g + (GlobalTheory.DblVac.matD g - 1) := by
      rw [hm]; noncomm_ring
    rw [e, smul_add, ← Matrix.smul_mul, hp.1 u hu, hg.1 u hu, Matrix.zero_mul, add_zero]
  · rw [hm, ← Matrix.mulVec_mulVec]
    exact (hp.2 _ (hg.2 z hz).1).1
  · rw [mul_inv_rev, hm, ← Matrix.mulVec_mulVec]
    exact (hg.2 _ (hp.2 z hz).2).2

theorem exists_unip : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Y : Matrix (Fin d) (Fin d) (AE F E),
      At (evFin F v) Y → (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ ∀ g ∈ GlobalTheory.DblVac.KD σ W v, p * g ∈ GlobalTheory.DblVac.KD σ W v ∧
        GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂)) := by
  intro F E _ _ _ _ _ σ d W v h2 Y hAt hL hY
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin d) (Fin d) (AE F E), Z = ⅟(2 : AF F) • Y := ⟨_, rfl⟩
  have hZZ : Z + Z = Y := by
    rw [← two_smul (AF F) Z, hZ, smul_smul, mul_invOf_self, one_smul]
  have hZc : Z.map (cA σ) = ⅟(2 : AF F) • Y.map (cA σ) := by
    rw [hZ]; ext i j; simp
  have hZu : Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 := by
    rw [hZc, hZ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]
  have hZL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [hZ, Matrix.smul_mulVec]
    exact GlobalTheory.LatAlmostAll.smul_mem_latAt W v (evFin_invOf_two_mem h2) (hL z hz)
  have hZL' : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (-Z) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [Matrix.neg_mulVec]
    exact neg_mem (hZL z hz)
  let p : GlobalTheory.DblVac.UD σ W := ⟨uniGL Z, uni_unitary (cA σ) (incM F W.J) Z hZu⟩
  have hp : p ∈ GlobalTheory.DblVac.KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨uni_mulVec_mem W v Z hZL z hz, uni_mulVec_mem W v (-Z) hZL' z hz⟩⟩
    refine smul_uni_sub_one u Z ?_
    rw [hZ, smul_comm, hAt u hu, smul_zero]
  refine ⟨p, hp, ⟨1, ?_⟩, fun g hg => ⟨mul_mem_KD hp hg, ?_⟩⟩
  · exact (uni_mul_diagCols Z).trans (Matrix.mul_one _).symm
  · have e : GlobalTheory.DblVac.matD (p * g) = uni Z * GlobalTheory.DblVac.matD g := rfl
    rw [GlobalTheory.DblVac.diagonalBlockOfMatrix, GlobalTheory.DblVac.diagonalBlockOfMatrix, e, blocks_uni_mul, smul_add, hZZ, Matrix.mul_smul]

end GlobalTheory.DblVacUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProducts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.StairUnit

theorem exists_mem_modul_notMem {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) u ∈ P.modul sc := by
  have h : ∀ v' : GlobalTheory.FinPl.Pl D, ∃ x : 𝓞 D.host.F, x ∉ v.asIdeal ∧ (v' ∈ P.S0 → x ∈ v'.asIdeal) := by
    intro v'
    by_cases h' : v' ∈ P.S0
    · have hn : ¬ v'.asIdeal ≤ v.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle) ▸ h')
      obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
      exact ⟨x, hx', fun _ => hx⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h h'⟩
  choose x hx hx' using h
  refine ⟨∏ v' ∈ P.S0, x v' ^ P.depth sc v', fun hu => ?_, ?_⟩
  · haveI := v.isPrime
    obtain ⟨v', -, h'⟩ := Ideal.IsPrime.prod_mem_iff.1 hu
    exact hx v' (v.isPrime.mem_of_pow_mem _ h')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' h' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 : x v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w h']; exact hx' v' h'
    exact h1

theorem mem_span_of_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E] {A B A' B' C : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', star x ∈ A) (hB : ∀ x ∈ B', star x ∈ B) {t : E} (ht : t ∈ A' * B' * C) :
    t ∈ Submodule.span (𝓞 E) {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c} := by
  refine FractionalIdeal.mul_induction_on ht (fun x hx c hc => ?_) fun x y => Submodule.add_mem _
  refine FractionalIdeal.mul_induction_on (C := fun x => x * c ∈ Submodule.span (𝓞 E)
    {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c}) hx (fun a ha b hb => ?_) fun x y hx hy => ?_
  · exact Submodule.subset_span ⟨_, hA a ha, _, hB b hb, c, hc, by rw [star_mul', star_star, star_star]⟩
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

theorem exists_unit_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  intro D T L sc G ρ p q hpq v hv
  obtain ⟨u, hu, hum⟩ := exists_mem_modul_notMem G.pl sc v hv
  refine ⟨u, hu, ?_⟩
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨hAA, hAAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hne : ∀ {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}, I ≠ 0 → (∀ x, x ∈ J ↔ star x ∈ I) → J ≠ 0 := by
    intro I J hI hJ h0
    apply hI
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h2 := h0 _ ((hJ (star y)).2 (by rwa [star_star]))
    rwa [star_eq_zero] at h2
  have hAb := hne hA hconj
  have hAAb := hne hAA hAAc
  have hB : ∀ x ∈ (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹,
      star x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q := by
    intro x hx
    have h1 := (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ q.rev).2 (star x)
    rw [Fin.rev_rev, star_star] at h1
    exact h1.2 hx
  have key : D.host.AAbar * (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹ *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p =
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have hq := q.2
    have e1 : 2 * ρ + 1 - 1 - q.rev.1 = q.1 + 1 := by rw [Fin.val_rev]; omega
    have e2 : q.rev.1 + 1 = p.1 := by rw [Fin.val_rev]; omega
    have e3 : 2 * ρ + 2 - 1 - p.1 = q.1 + 1 := by omega
    have e4 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
        D.host.AAbar * (G.pl.stAbar sc)⁻¹ := by
      rw [Places.stAbar, mul_inv, inv_inv, mul_inv_cancel_left₀ hAAb]
    unfold stairId
    rw [e1, e2, e3, e4, pow_succ (G.pl.stAbar sc) p.1]
    have h1 : G.pl.stA sc ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hA
    have h2 : G.pl.stAbar sc ^ p.1 ≠ 0 := pow_ne_zero _ hAb
    field_simp
  have hmem : ((u : D.host.F) : D.host.E) ∈
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hum, rfl⟩
  rw [← key] at hmem
  have h := mem_span_of_mem_mul (fun x hx => (hAAc x).1 hx) hB hmem
  simp only [hs] at h
  exact h

end GlobalTheory.StairUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.PrincipalMove

open GlobalTheory.FinPlLoc

theorem exists_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k * x - mt W g⁻¹ * (x * u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  intro D W ρ x Q g k u hg hk hM
  set e : AE D := idem D Q with he_def
  have he : e * e = e := idem_mul_self Q
  have hr : g * k ∈ grpAt W Q := mul_mem hg hk
  set U : Matrix (Fin ρ) (Fin ρ) (AE D) := u.1.1 with hU
  have hu : ∀ i j : Fin ρ, (j < i → U i j = 0) ∧ U i i = 1 := fun i j => u.2 i j
  let u' : GL (Fin ρ) (AE D) := mixGL he u.1 1
  have hu'v : u'.val = e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := rfl
  have hu' : u' ∈ UX D ρ := by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · show u'.val i j = 0
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i j).1 hij, Matrix.one_apply_ne hij.ne']
    · show u'.val i i = 1
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i i).2]
  refine ⟨g * k, ⟨u', hu', ?_⟩, hr, by group⟩
  have heM : e • (mt W k * x - mt W g⁻¹ * (x * U)) = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact (mem_idOff_iff Q _).1 (hM i j)
  have hgg : mt W g * mt W g⁻¹ = 1 := by
    rw [← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one]
  have h1 : e • (mt W (g * k) * x) = e • (x * U) := by
    have : mt W (g * k) * x = x * U + mt W g * (mt W k * x - mt W g⁻¹ * (x * U)) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc (mt W g) (mt W g⁻¹), hgg, Matrix.one_mul, FinPlLoc.mt_mul, Matrix.mul_assoc]
      abel
    rw [this, smul_add, ← Matrix.mul_smul (mt W g), heM, Matrix.mul_zero, add_zero]
  have h2 : (1 - e) • (mt W (g * k) * x) = (1 - e) • x := by
    have hm := (mem_grpAt_iff Q (g * k)).1 hr
    have : (1 - e) • mt W (g * k) = (1 - e) • (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) := by
      conv_lhs => rw [← hm]
      simp only [mix, smul_add, smul_smul]
      have h3 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
      have h4 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
      rw [h3, h4, zero_smul, zero_add]
    rw [← Matrix.smul_mul, this, Matrix.smul_mul, Matrix.one_mul]
  show mt W (g * k) * x = x * u'.val
  rw [hu'v]
  calc mt W (g * k) * x = e • (mt W (g * k) * x) + (1 - e) • (mt W (g * k) * x) := by
        rw [← add_smul, add_sub_cancel, one_smul]
    _ = e • (x * U) + (1 - e) • x := by rw [h1, h2]
    _ = x * (e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D))) := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]

end GlobalTheory.PrincipalMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem partFixed_of_depFixed : DepFixed → DatumDep → PartFixed := by
  intro hD hd D q T L μ0 hL sc G W M hM ρ Φ u i h k hk g
  have hf := hd D q T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩
  have key := hD D q T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ hf 1 (one_mem _) k hk
  show liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ (g * k) = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ g
  rw [liftA_apply, liftA_apply]
  congr 1
  funext x
  congr 1
  show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0
  have e : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) =
      (negGA _ g, x) * G.toPair (.chi i 0) 1 k := by
    show _ = (negGA _ g, x) * (negGA _ k, 1)
    rw [map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_bound_real_unipotent_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (φ : GA D V → ℂ) (c : ℝ), 0 ≤ c → Lip θ A φ c → ∀ (u : (Formalism.IndefR.Eqv.UI.instV fr).Ginf) (Av Z : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ v, Formalism.REAL.inG (fr.ε v) (Av v) ∧ Formalism.REAL.inG (fr.ε v) (Z v)) → (∀ v, Formalism.MainNotions.S.uMat (u v) = NormedSpace.exp (Av v) * NormedSpace.exp (Z v)) → ∀ y : GA D V, ‖φ (y * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) - φ y‖ ≤ c * ∑ v, (Real.sqrt (Formalism.REAL.hs (Av v)) + Real.sqrt (Formalism.REAL.hs (Z v))) := by
  first | exact @GlobalTheory.RealMove.lip_move_real | exact GlobalTheory.RealMove.lip_move_real | (intros; apply GlobalTheory.RealMove.lip_move_real <;> assumption)
end

