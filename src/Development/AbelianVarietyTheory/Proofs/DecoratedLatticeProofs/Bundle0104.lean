module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPadicCoordinatesOfDegreeOneSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.SplitQT

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

def intEquiv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletionIntegers F ≃+* 𝒪[Fv F v] where
  toFun x := ⟨x.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v x.1).2 x.2⟩
  invFun y := ⟨y.1, (GlobalTheory.FinPl.SplitPoint.mem_integer_iff F v y.1).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem exists_coord_padic : ∀ (D : D7) (T : ℕ) [Fact T.Prime] (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ (v : Pl D) (pr : AE D →+* ℚ_[T]) (sec : ℚ_[T] →+ AE D), (∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a, pr (sec a) = a) ∧ (∀ x, sec (pr x) = e * x) ∧ Continuous pr ∧ Continuous sec ∧ ∀ a, ‖a‖ ≤ 1 ↔ finPart D (sec a) ∈ intAE D := by
  intro D T _ w e hw hs hT hT2
  obtain ⟨_, _, v, ε, hε, he⟩ := id hs
  have hsa : SplitAt D v e := GlobalTheory.FinPl.SplitPoint.splitAt_of hs hε he
  have hch : Chart e v (comp hsa) := chart_comp hsa
  have hTw : ((T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    have := Ideal.absNorm_mem w.asIdeal
    rwa [hT] at this
  have hTw2 : ((T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := fun h =>
    hT2 (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  obtain ⟨⟨p, hp, hirr⟩, hcard⟩ := GlobalTheory.SplitUnif.unif_chart e w v (comp hsa) hw hch _ hTw hTw2
  have hpT : p = (T : Ov D v) := by
    apply Subtype.ext
    rw [show ((p : Fv D.host.F v)) = algebraMap (Ov D v) (Fv D.host.F v) p from rfl, hp]
    simp
  subst hpT
  haveI : CharZero (Fv D.host.F v) :=
    charZero_of_injective_ringHom (algebraMap D.host.F (v.adicCompletion D.host.F)).injective
  have hc1 : Nat.card (IsLocalRing.ResidueField 𝒪[Fv D.host.F v]) = T := by
    rw [← hT, ← hcard]
    exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (intEquiv D.host.F v)).toEquiv).symm
  have hc2 : Irreducible (T : 𝒪[Fv D.host.F v]) := by
    rw [← map_natCast (intEquiv D.host.F v) T]
    exact (MulEquiv.irreducible_iff (intEquiv D.host.F v).toMulEquiv).2 hirr
  obtain ⟨φ, hφ, hφ', hφO⟩ := _root_.GlobalTheory.QpChar.exists_ringEquiv_padic (Fv D.host.F v) T hc1 hc2
  obtain ⟨sp, hse, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε hs hε he
  refine ⟨v, φ.symm.toRingHom.comp sp.pr, sp.sec.comp φ.toRingHom.toAddMonoidHom, ⟨ε, hε, he⟩,
    fun a => ?_, fun x => ?_, hφ'.comp sp.cont_pr, sp.cont_sec.comp hφ, fun a => ?_⟩
  · change φ.symm (sp.pr (sp.sec (φ a))) = a
    rw [sp.pr_sec, RingEquiv.symm_apply_apply]
  · change sp.sec (φ (φ.symm (sp.pr x))) = e * x
    rw [RingEquiv.apply_symm_apply, sp.sec_pr, hse]
  · exact (hφO a).symm.trans (sp.int_iff (φ a))

end GlobalTheory.FinPl.SplitQT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

theorem mul_mul_mul_of_gram {a b c e n : Type*} [Fintype b] [Fintype c] [Fintype e] {R : Type*} [Semiring R]
    {A : Matrix a b R} {G : Matrix b c R} {M : Matrix c e R} {C : Matrix a e R} (h : A * G * M = C)
    (N : Matrix e n R) : A * (G * (M * N)) = C * N := by
  rw [← h]; simp only [Matrix.mul_assoc]

def selFirst (D : D7) (σ : ℕ) : Matrix (Fin σ) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun i j => if j = i.castSucc then 1 else 0

def lastE (D : D7) (σ : ℕ) : Fin (σ + 1) → D.host.E := Pi.single (Fin.last σ) 1

def besselRationalBasePointMatrix (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem ell_succ_eq : ell D (σ + 1) = fun i => incA D (lastE D σ i) := by
  funext i
  by_cases h : i = Fin.last σ
  · subst h
    show (if (Fin.last σ).1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ (Fin.last σ))
    rw [if_pos (by rw [Fin.val_last]), lastE, Pi.single_eq_same, map_one]
  · have h' : ¬ (i.1 + 1 = σ + 1) := fun h' => h (Fin.ext (by rw [Fin.val_last]; omega))
    show (if i.1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ i)
    rw [if_neg h', lastE, Pi.single_eq_of_ne h, map_zero]

theorem zl_eq_rat (B : BesLev D σ) : zl B = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zl, zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_x0Rat (B : BesLev D σ) : rat (besselRationalBasePointMatrix B) = x0 B := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_x0Rat (B : BesLev D σ) :
    (besselRationalBasePointMatrix B)ᴴ * B.V.gram * besselRationalBasePointMatrix B =
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
  rw [besselRationalBasePointMatrix, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_x0Rat (B : BesLev D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (besselRationalBasePointMatrix B) : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B) := by
  rw [zl_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_x0Rat B), gram_rat B.L rfl]

theorem linearIndependent_x0Rat (B : BesLev D σ) : LinearIndependent D.host.E (besselRationalBasePointMatrix B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : besselRationalBasePointMatrix B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * besselRationalBasePointMatrix B = selFirst D σ := by
    rw [besselRationalBasePointMatrix, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_x0Rat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
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

theorem exists_rationalOrbit_point_eq_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B :=
  fun _ _ B => ⟨besselRationalBasePointMatrix B, ⟨linearIndependent_x0Rat B, gramSkew_x0Rat B⟩, rat_x0Rat B⟩

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalWittFlagCoordinatesOfMemUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatCoord


set_option maxHeartbeats 1000000 in
theorem coords_rat {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank)
    (u : GL (Fin ρ) (AE D)) (hQ : d.nC c' * (d.nB b' * d.levi u) ∈ GQ V) :
    c'.1 ∈ ratMx D ρ ρ ∧ b' ∈ ratMx D ρ V₀.rank ∧ u.1 ∈ ratMx D ρ ρ ∧ (u⁻¹).1 ∈ ratMx D ρ ρ := by
  generalize hg : d.nC c' * (d.nB b' * d.levi u) = g at hQ
  have hM : mt V g ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g).1 hQ
  have hM' : mt V g⁻¹ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g⁻¹).1 (inv_mem hQ)
  have hX : mt V g ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (d.nB_jX _), cancel₂ (d.nC_jX _)]
  have hX' : mt V g⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
    calc mt V g⁻¹ ⬝ d.jX = mt V g⁻¹ ⬝ (d.jX ⬝ u.1 ⬝ (u⁻¹).1) := by
          rw [Matrix.mul_assoc d.jX, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have h0 : mt V g ⬝ d.j0 = d.j0 + d.jX ⬝ b' := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.nB_j0, Matrix.mul_add, cancel₂ (d.nC_jX _), d.nC_j0]
  have hY : d.pX ⬝ (mt V g ⬝ d.jY) = (c'.1 - half D • (b' ⬝ plus V₀ b')) ⬝ adj (u⁻¹).1 := by
    rw [← hg, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, cancel₂ (d.nB_jY _)]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₂ (d.nC_jY _),
      cancel₂ (d.nC_j0 _), cancel₂ (d.nC_jX _), cancel₂ d.pX_jY, cancel₂ d.pX_jX, cancel₂ d.pX_j0,
      Matrix.one_mul, Matrix.zero_mul, zero_add, sub_zero]
  have hu1 : u.1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g ⬝ d.jX) = u.1 := by rw [hX, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hu2 : (u⁻¹).1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g⁻¹ ⬝ d.jX) = (u⁻¹).1 := by rw [hX', cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM' (rat_mem _))
  have hb : b' ∈ ratMx D ρ V₀.rank := by
    have e : d.pX ⬝ (mt V g ⬝ d.j0) = b' := by
      rw [h0, Matrix.mul_add, d.pX_j0, zero_add, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hc : c'.1 = d.pX ⬝ (mt V g ⬝ d.jY) ⬝ adj u.1 + half D • (b' ⬝ plus V₀ b') := by
    have e : adj (u⁻¹).1 ⬝ adj u.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
    rw [hY, Matrix.mul_assoc, e, Matrix.mul_one, sub_add_cancel]
  refine ⟨?_, hb, hu1, hu2⟩
  rw [hc]
  exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))) (ratMx_adj hu1))
    (ratMx_smul _ (ratMx_mul hb (ratMx_mul (rat_mem _) (ratMx_adj hb))))

theorem rat_coords_of_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ (c : skewA D ρ) (b : Mx D ρ V₀.rank) (u : UX D ρ), γ = d.nC c * (d.nB b * d.levi u.1) ∧ c.1 ∈ ratMx D ρ ρ ∧ b ∈ ratMx D ρ V₀.rank ∧ u ∈ UXQ D ρ := by
  intro D V V₀ ρ d γ hQ hN
  obtain ⟨T, b, hT, hX, h0⟩ := exists_blocks d hN
  obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit hT
  let g := d.nB b * d.levi u
  let n := g⁻¹ * γ
  have fixed {k : ℕ} {X : Mx D V.rank k} (h : mt V γ ⬝ X = mt V g ⬝ X) : mt V n ⬝ X = X := by
    rw [show n = g⁻¹ * γ from rfl, mt_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, mt_inv_mul,
      Matrix.one_mul]
  have fixX : mt V n ⬝ d.jX = d.jX := fixed (by
    rw [hX, show g = d.nB b * d.levi u from rfl, mt_mul, Matrix.mul_assoc, d.levi_jX,
      cancel₂ (d.nB_jX b), hu1, Matrix.mul_add, Matrix.mul_one])
  have fix0 : mt V n ⬝ d.j0 = d.j0 := fixed (by
    rw [h0, show g = d.nB b * d.levi u from rfl, mt_mul, Matrix.mul_assoc,
      d.wittDecomp_levi_inclAnisotropic, d.nB_j0])
  have gram {k l : ℕ} (X : Mx D V.rank k) (Y : Mx D V.rank l) :
      adj (mt V n ⬝ X) ⬝ (gA V ⬝ (mt V n ⬝ Y)) = adj X ⬝ (gA V ⬝ Y) := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V) _ Y, ← Matrix.mul_assoc (adj (mt V n)),
      GlobalTheory.MixModel.mt_unitary]
  let c := d.pX ⬝ (mt V n ⬝ d.jY)
  have imageY : mt V n ⬝ d.jY = d.jY + d.jX ⬝ c := by
    have projY : d.pY ⬝ (mt V n ⬝ d.jY) = 1 := by
      rw [d.pY_eq, Matrix.mul_assoc, ← fixX, gram, d.gram_XY]
    have proj0 : d.p0 ⬝ (mt V n ⬝ d.jY) = 0 := by
      rw [d.p0_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← fix0, gram, d.gram_0Y, Matrix.mul_zero]
    conv_lhs => rw [← Matrix.one_mul (mt V n ⬝ d.jY), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, proj0, projY, Matrix.mul_zero, Matrix.mul_one, add_zero]
    exact add_comm _ _
  have skew : c ∈ skewA D ρ := by
    have h := gram d.jY d.jY
    rw [imageY, d.gram_YY] at h
    simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, d.gram_YY, d.gram_XY,
      cancel₃ d.gram_XX, cancel₃ d.gram_YX, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
      Matrix.mul_one, add_zero, zero_add] at h
    exact eq_neg_of_add_eq_zero_left h
  let c₀ : skewA D ρ := ⟨c, skew⟩
  have hn : n = d.nC c₀ := d.ga_ext (fixX.trans (d.nC_jX c₀).symm) (fix0.trans (d.nC_j0 c₀).symm)
    (imageY.trans (d.nC_jY c₀).symm)
  have hγ : γ = d.nC (skewConj u.1 c₀) * (d.nB b * d.levi u) := by
    calc
      γ = g * n := (mul_inv_cancel_left g γ).symm
      _ = _ := by rw [hn, show g = d.nB b * d.levi u from rfl, mul_assoc, d.levi_mul_nC,
        ← mul_assoc, ← d.nC_mul_nB, mul_assoc]
  rw [hγ] at hQ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := coords_rat d _ _ u hQ
  exact ⟨skewConj u.1 c₀, b, ⟨u, hu⟩, rfl, h1, h2, h3, h4⟩

end GlobalTheory.RatCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTransvectionFixingFirstVectorsSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvMid

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec (S : HSp D) {n : ℕ} (y : VA S) (M : Mx D S.rank n) (c : Fin n → AE D) :
    form S y (M *ᵥ c) = (fun k => cA D (c k)) ⬝ᵥ ((adj M ⬝ gA S) *ᵥ y) := by
  have h : (fun i => cA D ((M *ᵥ c) i)) = M.map (cA D) *ᵥ fun k => cA D (c k) := by
    funext i; exact RingHom.map_mulVec (cA D) M c i
  rw [form, h, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, adj, Matrix.vecMul_transpose]

theorem mul_apply_col {m n k : ℕ} (g : Mx D m n) (M : Mx D n k) (r : Fin m) (c : Fin k) :
    (g ⬝ M) r c = (g *ᵥ (M *ᵥ Pi.single c 1)) r := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl

theorem col_apply {m n : ℕ} (M : Mx D m n) (c : Fin n) (r : Fin m) : (M *ᵥ Pi.single c 1) r = M r c := by
  rw [Matrix.mulVec_single_one]; rfl

theorem submatrix_col {m n : ℕ} (M : Mx D m n) (i : Fin n) (c : Fin 1) :
    (M.submatrix id fun _ : Fin 1 => i) *ᵥ Pi.single c 1 = M *ᵥ Pi.single i 1 := by
  funext r; rw [col_apply, col_apply]; rfl

theorem smul_vecMulVec_single {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (J k : Fin ρ) :
    (s • vecMulVec x (Pi.single J 1)) *ᵥ Pi.single k 1 = (s * (Pi.single k 1 : Fin ρ → AE D) J) • x := by
  funext l
  rw [col_apply]
  by_cases hk : k = J
  · subst hk; simp [Matrix.vecMulVec_apply]
  · simp [Matrix.vecMulVec_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne' hk]

theorem upSum_smul_vecMulVec {ρ : ℕ} (s : AE D) (x : Fin ρ → AE D) (j J : Fin ρ) (hJ : J.1 = j.1 + 1) :
    GlobalTheory.MixPer.upSum (s • vecMulVec x (Pi.single J 1)) = s * x j := by
  have hTe : ∀ i k : Fin ρ, (if k.1 = i.1 + 1 then (s • vecMulVec x (Pi.single J 1)) i k else 0) =
      if i = j then (if k = J then s * x j else 0) else 0 := by
    intro i k
    by_cases hk : k = J
    · subst hk
      by_cases hi : i = j
      · subst hi
        simp [hJ, Matrix.vecMulVec_apply, mul_comm]
      · have : ¬ (k.1 = i.1 + 1) := fun h => hi (Fin.ext (by omega))
        simp [hi, this]
    · simp [hk, Matrix.vecMulVec_apply]
  rw [GlobalTheory.MixPer.upSum]
  simp only [hTe]
  simp

section Mid

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem form_jY_single (y : VA V) (J : Fin ρ) (s : AE D) :
    form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J := by
  have h : (fun k => cA D ((Pi.single J (cA D s) : Fin ρ → AE D) k)) = (Pi.single J s : Fin ρ → AE D) := by
    funext k
    by_cases hk : k = J
    · subst hk; simp [cA_cA]
    · simp [Pi.single_apply, hk]
  rw [form_mulVec, h, ← d.pX_eq, single_dotProduct]

theorem form_jX (y : VA V) (b : Fin ρ → AE D) :
    form V y (d.jX *ᵥ b) = (fun k => cA D (b k)) ⬝ᵥ (d.pY *ᵥ y) := by
  rw [form_mulVec, ← d.pY_eq]

theorem transv_fix {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) {y : VA V} (hv : form V y v = 0)
    (hw : form V y w = 0) : mt V u *ᵥ y = y := by
  have := hu y
  rw [act, transv, hv, hw] at this
  rw [this]; simp

theorem pX_jX_single (k : Fin ρ) : d.pX *ᵥ (d.jX *ᵥ Pi.single k 1) = Pi.single k 1 := by
  rw [Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]

theorem pY_jX_vec (x : Fin ρ → AE D) : d.pY *ᵥ (d.jX *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_jX, Matrix.zero_mulVec]

theorem isotropicProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pX *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]

theorem dualProjection_anisotropic_vec_eq_zero (x : Fin V₀.rank → AE D) : d.pY *ᵥ (d.j0 *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]

theorem transv_apply {w v : VA V} {u : GA D V} (hu : IsTransv V w v u) (y : VA V) :
    mt V u *ᵥ y = transv V w v y := hu y

variable {w v : VA V} {u : GA D V} {J : Fin ρ} {s : AE D} {c : Fin ρ → AE D}

theorem mem_fixer_of_ne (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {i : Fin ρ} (hiJ : i ≠ J) :
    u ∈ GlobalTheory.MixPer.fixer V (d.jX.submatrix id fun _ : Fin 1 => i) := by
  rw [GlobalTheory.MixPer.mem_fixer]
  ext r k
  rw [mul_apply_col, submatrix_col, transv_fix hu, col_apply]
  · rfl
  · rw [fv, pX_jX_single d, Pi.single_eq_of_ne' hiJ, mul_zero]
  · rw [fw, pY_jX_vec d, dotProduct_zero]

theorem transv_jX (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) {x : Fin ρ → AE D} (hw : w = d.jX *ᵥ x) :
    mt V u ⬝ d.jX = d.jX + d.jX ⬝ (s • vecMulVec x (Pi.single J 1)) := by
  ext r k
  rw [mul_apply_col, transv_apply hu, transv, fv, fw, pX_jX_single d, pY_jX_vec d]
  simp only [dotProduct_zero, mul_zero, zero_smul, sub_zero]
  rw [Matrix.add_apply, mul_apply_col, smul_vecMulVec_single, Matrix.mulVec_smul, ← hw]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, col_apply]

theorem unitaryTransvection_on_anisotropic_part (hu : IsTransv V w v u) (fv : ∀ y : VA V, form V y v = s * (d.pX *ᵥ y) J)
    (fw : ∀ y : VA V, form V y w = c ⬝ᵥ (d.pY *ᵥ y)) : mt V u ⬝ d.j0 = d.j0 + d.jX ⬝ (0 : Mx D ρ V₀.rank) := by
  rw [Matrix.mul_zero, add_zero]
  ext r k
  rw [mul_apply_col, transv_fix hu, col_apply]
  · rw [fv, isotropicProjection_anisotropic_vec_eq_zero d, Pi.zero_apply, mul_zero]
  · rw [fw, dualProjection_anisotropic_vec_eq_zero d, dotProduct_zero]

end Mid

end GlobalTheory.TransvMid


open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction in
theorem GlobalTheory.TransvMid.exists_mid : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (z : Fin V₀.rank → D.host.E) (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → j.1 + 1 < ρ → ∀ s : AE D, ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum d z u = s := by
  intro D V V₀ ρ d z j a haj hai hj s
  set J : Fin ρ := ⟨j.1 + 1, hj⟩ with hJ
  have hjJ : j < J := by rw [Fin.lt_def]; simp [hJ]
  have haJ : ratVec a J = 0 := by simp [ratVec, hai J hjJ]
  have hw : vecX d (ratVec a) = d.jX *ᵥ ratVec a := rfl
  refine ⟨d.jY *ᵥ Pi.single J (cA D s), ?_, ?_, ?_⟩
  · rw [GlobalTheory.TransvMid.form_jY_single, hw, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec, haJ, mul_zero]
  · intro i k hki
    rw [GlobalTheory.TransvMid.form_jY_single, vecX, Matrix.mulVec_mulVec, d.pX_jX, Matrix.one_mulVec]
    by_cases hk : k = J
    · subst hk
      have : ratVec a i = 0 := by simp [ratVec, hai i (lt_of_lt_of_le hjJ hki)]
      rw [this, mul_zero]
    · rw [Pi.single_eq_of_ne' hk, mul_zero, zero_mul]
  · intro u hu
    have fv : ∀ y : VA V, form V y (d.jY *ᵥ Pi.single J (cA D s)) = s * (d.pX *ᵥ y) J :=
      fun y => GlobalTheory.TransvMid.form_jY_single d y J s
    have fw : ∀ y : VA V, form V y (vecX d (ratVec a)) = (fun k => cA D (ratVec a k)) ⬝ᵥ (d.pY *ᵥ y) :=
      fun y => GlobalTheory.TransvMid.form_jX d y _
    generalize d.jY *ᵥ Pi.single J (cA D s) = v at hu fv
    generalize hwv : vecX d (ratVec a) = w at hu fw
    rw [vecX] at hwv
    refine ⟨fun i => GlobalTheory.TransvMid.mem_fixer_of_ne d hu fv fw (ne_of_lt (lt_of_le_of_lt i.2 hjJ)), ?_⟩
    rw [GlobalTheory.MixPer.simpleSum_eq d z (GlobalTheory.TransvMid.transv_jX d hu fv fw hwv.symm)
      (GlobalTheory.TransvMid.unitaryTransvection_on_anisotropic_part d hu fv fw), GlobalTheory.MixPer.superSum_const]
    simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero, one_mul]
    rw [GlobalTheory.TransvMid.upSum_smul_vecMulVec s _ j J rfl]
    simp [ratVec, haj]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiActions_match_through_linkMap : ∀ (D : D7) (ρ σ : ℕ) (B : BesLev D σ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (W W₀ : HSp D) (d : HypDec W W₀ ρ), ∀ n ∈ flagN d, l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d B.L (yZero B.L ρ B.ζ) n ∧ cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  first | exact @GlobalTheory.Unf.LinkPoint.link_point | exact GlobalTheory.Unf.LinkPoint.link_point | (intros; apply GlobalTheory.Unf.LinkPoint.link_point <;> assumption)
end

