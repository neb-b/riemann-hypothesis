module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0158
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionOfBoundedHolomorphicForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfVanishIt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.StepUniq


open Classical in
theorem eq_zero_of_vanish_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ u : MMap (R.MY k), Formalism.IndefR.Eqv.ContAt (R.MY k) u → (∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0) → u = 0 := by
  intro hDS hHC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk u hc hv
  have hB := hP.char.base
  have hCh : R.toRealDat.IsChain := RealDat.chain_of_weak hB.chain hH.aux.ex
  have hok := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A3.A Ks R.toRealDat hB.lev hB.models.inf hCh.ωY hCh.ωX hCh.vY hCh.vX
  obtain ⟨hw, hvv⟩ := hok.1 t ⟨k, by omega⟩ hk
  have hIt := hCh.ItY t k hk
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ _ _
    (R.ωY t k) (R.vY t k) (R.ItY k) hB.models.inf hw hvv hIt
  have hx : ∀ x, (LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ PiTensorProduct.lift u = 0 := by
    intro x
    refine GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D _ _ (R.MY k) _ ?_ ?_
    · intro τ v
      obtain ⟨ℓ, hℓ, he⟩ := hc τ v x
      refine ⟨ℓ, hℓ, fun w => ?_⟩
      rw [he w]
      simp [PiTensorProduct.lift.tprod]
    · intro v hv'
      have hmem := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv' τ), rfl⟩)
      have hker : Submodule.span ℂ {w | ∃ P, ∃ y ∈ Submodule.span ℂ {w | ∃ v, (∀ τ, ((v τ : (R.MY (k + 1)).sm τ) :
          (R.MY (k + 1)).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin (R.MY (k + 1)) τ) ∧ w = PiTensorProduct.tprod ℂ v},
            w = (R.ItY k P) y} ≤ LinearMap.ker ((LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
              PiTensorProduct.lift u) := by
        rw [Submodule.span_le]
        rintro _ ⟨P, y, -, rfl⟩
        simp [hv P y]
      exact hker hmem
  have h0 : PiTensorProduct.lift u = 0 := by
    ext v x
    have := congrArg (fun Λ => Λ (PiTensorProduct.tprod ℂ v)) (hx x)
    simpa using this
  have : u = PiTensorProduct.lift.symm (PiTensorProduct.lift u) := by simp
  rw [this, h0, map_zero]

end GlobalTheory.Mem.R3.StepUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugatedChartDataLocalLevelAtQStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugated_chartData_localLevel_at_Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.chartQ_exists | exact GlobalTheory.Mem.Col2.ChEx.chartQ_exists | (intros; apply GlobalTheory.Mem.Col2.ChEx.chartQ_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivFormsTie
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder Matrix

namespace GlobalTheory.Mem.ColTie

section Mat

end Mat

section Gen

def StarCx {X : Fields} (σ : X.K →+* ℂ) : Prop := ∀ x, σ (star x) = starRingEnd ℂ (σ x)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev HPm : Matrix (Fin (dimP W Ch sel mu P hX)) (Fin (dimP W Ch sel mu P hX)) X.K :=
  (csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr

theorem ipK_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipK W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      (csdK W Ch sel mu hX).csum (formK W Ch sel mu P hX x).1 (formK W Ch sel mu P hX y).1 := by
  have e : ∀ x, (fun c => (zOf W Ch sel mu P hX x).1 ((mtildeKGSD W Ch sel mu).outSec.rep c)) =
      ((formK W Ch sel mu P hX x).1 : _ → _) := by
    intro x
    funext c
    rw [zOf_val, ← GSD.resOf_apply _ (mtildeKOk W Ch sel mu hX) (mtildeKGSD W Ch sel mu).outSec]
    show (((resK W Ch sel mu hX) ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x))).1 : _ → _) c = _
    rw [LinearEquiv.apply_symm_apply]
  unfold ipK GSD.ip GSD.ipOf
  rw [e, e]

theorem ipLev_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform (HPm W Ch sel mu P hX) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← _root_.GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev W Ch sel mu P hX, ipK_zOf]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px) (t : TupU I U)

end Fam

section TC

attribute [local instance] starE

theorem sig_starCx (B : Base) : StarCx (X := B.fields) (sig B) := fun x => B.starLL_cx x

variable {B : Base} {px : PreX B.toPre} (I : TC B px)

end TC

end GlobalTheory.Mem.ColTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLeOfAntilinear
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    ∀ τ k, 1 ≤ (κ i).aP τ k := by
  intro τ k
  rw [(h i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hk2 := k.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (D.R.k + i - 1 - k) k (by simp only [Ranks.r]; omega)
  have h4 : Formalism.L2.NTheta.lamAt (D.hc τ) (k + (D.R.k + i - 1 - k)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have h5 := (D.hc τ).gap_be i
  have h6 : ((D.R.k + i - 1 - k : ℕ) : ℚ) = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (k + 1) := by
    rw [show D.R.k + i - 1 - k = (D.R.sigW ((i : ℕ) + 1)).1 - (k + 1) by omega, Nat.cast_sub hk2]
    push_cast
    rfl
  rw [h4, h6] at h3
  simp only [aPl, if_pos k.2]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem finrank_le_of_antilinear {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [FiniteDimensional ℂ H'] (e : H ≃ₗ⋆[ℂ] H') : Module.finrank ℂ H ≤ Module.finrank ℂ H' := by
  have b := Module.finBasis ℂ H'
  have h : Submodule.span ℂ (Set.range fun k => e.symm.toLinearMap (b k)) = ⊤ := by
    rw [← span_range_eq_basis b e.symm.toLinearMap, show Set.range e.symm.toLinearMap = Set.univ from Set.range_eq_univ.2 e.symm.surjective, Submodule.span_univ]
  rw [← finrank_top, ← h]
  exact (finrank_range_le_card _).trans (Fintype.card_fin _).le

theorem adel_rdU_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      (rdU (T.U j σ) f) = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ)⁻¹ • phiC T hV a f := by
  subst hV
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  exact (inv_smul_smul₀ hl _).symm


set_option maxHeartbeats 1000000 in
theorem evAt_mem_span (hP : GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels)
    (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i)
    (x : (R.HW i σ).H) : evAt R i σ (v₀ i σ) x ∈
      Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) := by
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := _root_.GlobalTheory.HolDict.goodDict_core D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hM.HW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HolDict.holForm_zCusp_of_mem_mult hP D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hs hw (ht.hv₀ i σ).1 _ _ _ hx
  rw [show levChi _ (R.βW i) (R.datWp i R.triv) = fun _ => 1 from funext (GlobalTheory.ConjEval.levChi_principal R i)] at h1
  obtain ⟨P, hP0, hPb, hP⟩ := _root_.GlobalTheory.HolDict.IntoSec.exists_bddSec_adel_eq D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg _ h1
  have hc := _root_.GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg P hPb (hP.symm ▸ h2)
  have hτ : D.what₂.Tau := D.eTau.symm ⟨1, Subgroup.one_mem _⟩
  have hmem := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T ht.laws _ (inR i) (κ i) (fun τ k _ => lastPos_of_kapIs ht.kap i τ k)
    ((ht.kap i hτ).2.2.symm ▸ hn) _ hσ ⟨holCusp_mem_holSub _ _ hc, hP0⟩
  have h3 := Submodule.mem_map_of_mem (f := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))) hmem
  rw [hP, Submodule.map_span] at h3
  refine Submodule.span_le.2 ?_ h3
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  rw [adel_rdU_eq T hV (wtA (κ i)) f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)


set_option maxHeartbeats 1000000 in
theorem jUnif : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ → JEvBar T R κ → EvInj T R v₀ → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro hP D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp hJ hB hI hn
  refine jUnif_of T R κ v₀ ht.laws hJ hB hI (GlobalTheory.PhiIndep.phiC_indep D T κ ht.laws)
    (evAt_mem_span hP T R κ v₀ hL hM ht hp hn) fun i σ hσ => ?_
  obtain ⟨e⟩ := (_root_.GlobalTheory.ConjHilb.conj_hilbert D G Pl0 T0 A T R κ v₀ hM ht).1 i σ hσ
  exact finrank_le_of_antilinear e

end GlobalTheory.ReadingSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsXTupleChainOfLevelReading
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TwP.weightedInner_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ (o : Formalism.L2.Forms.FrP (I.rec7 l Z)), o.IsON → ∀ (z z' : (I.per l u a).Wrow) (Pc Qc : (I.fm l u a).clsP → MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ℂ), (∀ c, Pc c ∈ CSpan (I.fm l u a).sg) → (∀ c, Qc c ∈ CSpan (I.fm l u a).sg) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c)) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z' c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c)) → (I.fm l u a).ipP z z' = ∑ c, ((Nat.card ((I.fm l u a).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll (I.fm l u a).sg (Qc c) (Pc c) := by
  intro B X I hI hP l Z u a o ho z z' Pc Qc _ _ hz hz'
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hG : ∀ τ, gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) τ = 1 := fun τ => by
    rw [hgP, gramC_one]
  have hsh : shiftOf (sgTG (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  show (I.perIn u a).ipP B.fields.emb B.embLL (l.per u a) z z' = _
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : z c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz c
  have e2 : z' c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz' c
  show (I.perIn u a).wt c * ipVal B.fields.emb B.embLL (I.perIn u a).sgT (z c) (z' c) = _
  rw [e1, e2]
  exact congrArg₂ (· * ·) rfl (MetricTie.ipVal_step B.fields.emb B.embLL (I.perIn u a).sgT hl hsh hG id (fun _ => rfl) o ho (Pc c) (Qc c))

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TwP.norm_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (K : ClassesAtPrimes (I.fm l u a) bad) {okW : (I.rec7 l Z).what₂.places.Pl → Prop} (V : ValuationAtPrimes K okW), (∀ z, V.eW z = GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z) → NormPTieG V := by
  intro B X I hI hP l Z u a bad K okW V hV s x Pc hPc o ho
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  have h := @MetricTie.norm_step _ _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL (I.perIn u a).sgT (I.stX a) (base_fOk B)
    (l.per u a).step (l.fmL u a).famP ((I.perIn u a).clFin (l.per u a)) _ hl _ hsh _ _
    (fun τ => by rw [hgP, gramC_one]; rfl) (fun y => (y : Formalism.L2.Forms.FrP (I.rec7 l Z))) (fun _ => rfl) s x Pc
    (fun c z => by
      have e := (congrFun (hV ((I.fm l u a).ptEmb x)) c).symm.trans (hPc c)
      exact congrFun e z) o ho
  refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
  congr 2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  rfl


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TwP.forms_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∃ V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T), NormPTieG V ∧ ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → V.eW z c s = z c s' := by
  intro B X I hI hP l Z u a Q K hQ hQv hK
  let V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T) :=
    { sg := _root_.GlobalTheory.Mem.Col2.TC.fm_sg_eq I hI hP l Z u a
      eW := GlobalTheory.Mem.Col2.TwP.eWt I l Z u a
      ptC := _root_.GlobalTheory.Mem.Col2.TwP.ptC_tw I hI hP l Z u a Q K hQ hQv hK
      ipP := GlobalTheory.Mem.Col2.TwP.weightedInner_twisted I hI hP l Z u a
      rat := _root_.GlobalTheory.Mem.Col2.TwP.ptEmb_iff_rat I hI hP l Z u a
      lat := _root_.GlobalTheory.Mem.Col2.TC.tw_lat_at I hI hP l Z u a Q K hQ hQv hK }
  refine ⟨V, GlobalTheory.Mem.Col2.TwP.norm_tw I hI hP l Z u a K V fun _ => rfl, fun z c s s' h => ?_⟩
  exact GlobalTheory.Mem.Col2.TwP.eWt_apply I l Z u a z c s s' h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.IsotIndep

theorem gaL_finSum {D : D7} {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c0 : G → ℂ) :
    ∃ (s : Finset (GA D V)) (c : GA D V → ℂ), (∀ g ∈ s, g ∈ GfC V) ∧
      gaL V β L eG c0 = ∑ g ∈ s, c g • principalLevelFrame.rtA g := by
  classical
  let k : G → GA D V := fun g => if hx : ∃ κ, IsLevelLift V β L (eG g) κ then hx.choose else 1
  let a : G → ℂ := fun g =>
    if hx : ∃ κ, IsLevelLift V β L (eG g) κ then c0 g * (levChi V β (flagL L) hx.choose)⁻¹ else 0
  have hk : ∀ g, c0 g • actL V β L (eG g) = a g • principalLevelFrame.rtA (k g) := by
    intro g
    apply LinearMap.ext
    intro F
    funext h
    by_cases hx : ∃ κ, IsLevelLift V β L (eG g) κ
    · have e1 : a g = c0 g * (levChi V β (flagL L) hx.choose)⁻¹ := dif_pos hx
      have e2 : k g = hx.choose := dif_pos hx
      rw [e1, e2]
      show c0 g * actG0 V β L (eG g) F h = c0 g * (levChi V β (flagL L) hx.choose)⁻¹ * F (h * hx.choose)
      unfold actG0
      rw [dif_pos hx, mul_assoc]
    · have e1 : a g = 0 := dif_neg hx
      rw [e1, zero_smul]
      show c0 g * actG0 V β L (eG g) F h = 0
      unfold actG0
      rw [dif_neg hx]
      simp
  refine ⟨Finset.univ.image k, fun x => ∑ g ∈ Finset.univ.filter (fun g => k g = x), a g, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    by_cases h : ∃ κ, IsLevelLift V β L (eG g) κ
    · have e2 : k g = h.choose := dif_pos h
      rw [e2]
      exact h.choose_spec.1
    · have e2 : k g = 1 := dif_neg h
      rw [e2]
      exact one_mem _
  · have e0 : gaL V β L eG c0 = ∑ g, a g • principalLevelFrame.rtA (k g) := by
      unfold gaL
      exact Finset.sum_congr rfl fun g _ => hk g
    rw [e0]
    symm
    calc ∑ x ∈ Finset.univ.image k, (∑ g ∈ Finset.univ.filter (fun g => k g = x), a g) • principalLevelFrame.rtA x
        = ∑ x ∈ Finset.univ.image k, ∑ g ∈ Finset.univ.filter (fun g => k g = x), a g • principalLevelFrame.rtA (k g) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [(Finset.mem_filter.1 hg).2]
      _ = ∑ g, a g • principalLevelFrame.rtA (k g) :=
          Finset.sum_fiberwise_of_maps_to (fun g _ => Finset.mem_image_of_mem k (Finset.mem_univ g)) _


set_option maxHeartbeats 2000000 in
theorem isot_iSupIndep : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ i : Fin D.R.m, iSupIndep (fun σ : D.what₂.FT => D.what₂.isot ((i : ℕ) + 1) σ) := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost i
  have hI : Inputs D := _root_.GlobalTheory.LinksInputs.inputs_of_hypotheses hW hDS hHC hCR D
  have hB := hP.char.base
  have hT := Y.tied.lift
  have h0 := hB.models.νW i
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 false)) h0.1.1 h0.2
  have hO := (_root_.GlobalTheory.FinTypesRows.isotL_span_orth D (Wc D i) _ R.θ (R.MW i (sg0 D A3.A)) (Y.PW i) Y.hF (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) (R.eWf i (sg0 D A3.A)) _ (R.fdW i) hI (D.sp.W_sig _)
    hB.models.inf (Y.stdPsi.2 i) hs.1 hs.2 (gaL_finSum _ _ _ _ _)).2
  apply OrthogonalFamily.independent
  rw [orthogonalFamily_iff_pairwise]
  intro σ σ' hne
  rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hu' := (hT.isot i σ u).1 hu
  have hv' := (hT.isot i σ' v).1 hv
  rw [Y.prtWE] at hu' hv'
  obtain ⟨a, ha, hau⟩ := hu'
  obtain ⟨b, hb, hbv⟩ := hv'
  have hni : ¬ (principalLevelFrame.rowRepR R.θ (Y.eFT σ)).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ')) := fun h =>
    hne (Y.eFT.injective (principalLevelFrame.rowRepR_inj R.θ _ _ h))
  have key := hO _ _ hni a ha b hb
  rw [hT.mj i u v]
  unfold LiftReal.ipWc ipMT
  rw [← hau, ← hbv]
  refine mul_eq_zero_of_right _ ?_
  refine Eq.trans ?_ key
  congr 1
  · exact LinearEquiv.symm_apply_apply _ a
  · exact LinearEquiv.symm_apply_apply _ b

end GlobalTheory.Mem.R3.IsotIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertNeighbours_lifts_doubleCoset_translates : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ q : ↑((famR X I hX U Xg tr).okI t) × List ℕ, Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 →
    ∃ (x : Bridge.Gf (Vc X.toD7 i)) (R : Finset (Bridge.Gf (Vc X.toD7 i))),
      IsLabElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank q.2) x ∧
      (∀ a ∈ R, IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 a) ∧
      Bridge.IsDC (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J x R ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet (E := X.toD7.host.E) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e := by
  first | exact @GlobalTheory.InertNbr.inert_neighbours | exact GlobalTheory.InertNbr.inert_neighbours | (intros; apply GlobalTheory.InertNbr.inert_neighbours <;> assumption)
end

