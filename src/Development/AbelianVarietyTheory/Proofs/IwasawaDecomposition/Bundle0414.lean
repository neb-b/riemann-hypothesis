module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelCharacterTranslationEqFlagCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.ClassSK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormPeriodRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.ClassScalar

open GlobalTheory.Ker

variable {D : D7}

theorem fmt_mul_inv (V : HSp D) (g : GA D V) : fmt V g * fmt V g⁻¹ = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt]
  rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isMov_hLat (V : HSp D) (hL : Bridge.hLat V 1 = stdL D.host.E V.rank) (g : GA D V) :
    IsMov (fmt V g) (stdL D.host.E V.rank) (Bridge.hLat V (fin V g)) := by
  have hs : Submodule.span D.host.E (stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, (Pi.basisFun_apply _ _ i).symm⟩
  obtain ⟨⟨L, hL', hm⟩, h2⟩ := (isMov_laws D V.rank _ ⟨Submodule.fg_span (Set.finite_range _), hs⟩).2.2.2 _ _
    (fmt_mul_inv V g)
  have h3 := (isMov_laws D V.rank L hL').1
  have h4 : fmt V g⁻¹ * fmt V g = 1 := mul_eq_one_comm.1 (fmt_mul_inv V g)
  have key : Bridge.hLat V (fin V g) = L := by
    rw [Bridge.hLat, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hL, ← Submodule.span_eq L]
    congr 1
    ext x
    change fmt V g⁻¹ *ᵥ toAf x ∈ hatV (stdL D.host.E V.rank) ↔ x ∈ L
    rw [← h3, hm]
    constructor
    · intro hx
      exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, fmt_mul_inv, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, e⟩
      rwa [e, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  rwa [key]

noncomputable abbrev cf (D : D7) : AfE D →+* AfE D := sigR (Af D.host.F) D.sp.cm.sig

theorem cf_cf (x : AfE D) : cf D (cf D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = cf D (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem conj_mem_hatV {k : ℕ} {L L' : Lt D.host.E k} (h : ∀ v ∈ L, (fun j => cc (v j)) ∈ L') {u : Fin k → AfE D}
    (hu : u ∈ hatV L) : cf D ∘ u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h x hx, rfl⟩
  | zero => convert (hatV L').zero_mem; funext i; exact RingHom.map_zero _
  | add a b _ _ ha hb => convert add_mem ha hb; funext i; exact RingHom.map_add _ _ _
  | neg a _ ha => convert neg_mem ha; funext i; exact RingHom.map_neg _ _

theorem isMov_conj {V : HSp D} {g : GA D V} {L L' : Lt D.host.E V.rank} (h : IsMov (fmt V g) (stdL D.host.E V.rank) L)
    (hc : ∀ v, v ∈ L' ↔ (fun j => cc (v j)) ∈ L) : IsMov (fmtC V g) (stdL D.host.E V.rank) L' := by
  have c4 : fmtC V g = (fmt V g).map (cf D) := by ext i j; exact finPart_cA _
  have c5 : ∀ v ∈ stdL D.host.E V.rank, (fun j => cc (v j)) ∈ stdL D.host.E V.rank := fun v hv => by
    rw [← GenLatCmp.std_eq, GenLatCmp.mem_std] at hv ⊢
    exact fun i => Base.isIntegral_cc (hv i)
  have c6 (u : Fin V.rank → AfE D) : cf D ∘ cf D ∘ u = u := funext fun i => cf_cf _
  have c7 (u : Fin V.rank → AfE D) : fmtC V g *ᵥ (cf D ∘ u) = cf D ∘ (fmt V g *ᵥ u) := by
    rw [c4]; funext i; exact (RingHom.map_mulVec (cf D) _ _ i).symm
  intro u
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h _).1 (conj_mem_hatV (fun v hv => (hc v).1 hv) hu)
    exact ⟨_, conj_mem_hatV c5 h0, by rw [c7, ← e, c6]⟩
  · rintro ⟨u₀, h0, rfl⟩
    rw [← c6 u₀, c7]
    refine conj_mem_hatV (fun v hv => (hc _).2 ?_) ((h _).2 ⟨_, conj_mem_hatV c5 h0, rfl⟩)
    simpa [cc] using hv

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩


end GlobalTheory.OneMapRef.ClassScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenLevelCutByCosetStabiliserStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openLevel_cutByCosetStabiliser : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q), ThetaOpen Θ → ∀ (C : ∀ P : Q, Set (Sp E n)), (∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) → ThetaOpen (GlobalTheory.Mem.Col2.ChEx.cutQ Θ C) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | exact GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | (intros; apply GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelCharacterTranslationEqFlagCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
      (hu : (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp),
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr ⟨_, hu⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.Mem.R3.RowChr.chr_eq_ch | exact GlobalTheory.Mem.R3.RowChr.chr_eq_ch | (intros; apply GlobalTheory.Mem.R3.RowChr.chr_eq_ch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPointDeterminedByLatticeInvariantsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepPoint_determined_by_latticeInvariants : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf | exact GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceDatum

theorem stepVecExists : ∀ D : D7, StepVecExists D := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf
  have hinf := infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT) βS βT
  obtain ⟨f, h⟩ := exists_isThetaAt hf.1 hS hT (idemSum_mul_self he) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS ΛT hS hT _ e he f₀ hf.2.theta hf.2.lat).1
    (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ (LS.Pg ∪ Q)
      (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
        rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
          omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
  exact ⟨f, hf, e, he, h⟩

end GlobalTheory.PlaceDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  first | exact @GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | exact GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | (intros; apply GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKOfStd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.KerSK

theorem rowSG_heq {ι : Type} {X X' : Fields} (hX : X = X') {Pr : Primes X} {Pr' : Primes X'} (hPr : HEq Pr Pr')
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)}
    (hsel : HEq sel sel') {S S' : Set ℕ} (hS : S = S') {tup : ι → Tup X.F X.E X.K S} {tup' : ι → Tup X'.F X'.E X'.K S'}
    (htup : HEq tup tup') :
    HEq (fun μ => rowSG Pr sel (tup μ)) (fun μ => rowSG Pr' sel' (tup' μ)) := by
  subst hX; subst hS; cases hPr; cases hsel; cases htup; rfl

theorem sharp_heq {ι : Type} {X X' : Fields} (hX : X = X') {P : ι → Finset (HeightOneSpectrum (𝓞 X.E))}
    {P' : ι → Finset (HeightOneSpectrum (𝓞 X'.E))} (hP : HEq P P') {c : ∀ μ, LocCst X (P μ)} {c' : ∀ μ, LocCst X' (P' μ)}
    (h : HEq c c') (μ : ι) : (c μ).sharp = (c' μ).sharp := by
  subst hX; cases hP; cases h; rfl

theorem ch_cast {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
    {Tw Tw' : TwForms D} (h : Tw = Tw') (x : SymmetricTwistedColumnsAtPrimes tp C Tw) : (h ▸ x).ch = x.ch := by
  subst h; rfl

end GlobalTheory.Mem.Col2.TC.KerSK

end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeLatticeComparisonRational
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HLatStd

variable {D : D7} {V : HSp D}

def invM (h : Bridge.Gf V) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D)

def iv (x : Fin V.rank → D.host.E) : Fin V.rank → EAf D := fun i => x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)

theorem mem_set_iff (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) (x : Fin V.rank → D.host.E) :
    (Units.val ((h⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).mulVec
          (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D := by
  rw [GlobalTheory.StdFrameExist.latHat_iff hV]
  refine forall_congr' fun i => ?_
  rw [RingHom.map_mulVec]
  rfl

theorem iv_natCast_smul (N : ℕ) (x : Fin V.rank → D.host.E) : iv ((N : D.host.E) • x) = (N : EAf D) • iv x := by
  funext i
  simp only [iv, Pi.smul_apply, smul_eq_mul]
  rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
    (B := Formalism.L2.Herm.Af D.host.F)) N]
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem iv_mem_of_int {x : Fin V.rank → D.host.E} (hx : ∀ i, IsIntegral ℤ (x i)) (i : Fin V.rank) :
    iv x i ∈ GlobalTheory.StdFrameExist.SI D := by
  obtain ⟨o, ho⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hx i)
  show x i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ _
  rw [← ho]
  exact GlobalTheory.StdFrameExist.tmul_one_mem o

theorem int_of_iv_mem {e : D.host.E} (he : (e ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) ∈ GlobalTheory.StdFrameExist.SI D) :
    IsIntegral ℤ e := by
  rw [← GlobalTheory.StdFrameExist.mem_ALint_iff] at he
  exact GlobalTheory.StabFin.isIntegral_of_mem e he

theorem mulVec_natCast_smul (M : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) (N : ℕ) (z : Fin V.rank → EAf D) :
    M *ᵥ ((N : EAf D) • z) = ((N : EAf D) • M) *ᵥ z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem invM_mul (h : Bridge.Gf V) :
    (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D) * invM h = 1 := by
  rw [invM, ← Matrix.map_mul, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem invM_hmul (h x : Bridge.Gf V) : invM (h * x) = invM x * invM h := by
  rw [invM, invM, invM, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem mem_hLat_of (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) {x : Fin V.rank → D.host.E}
    (hx : ∀ i, (invM h *ᵥ iv x) i ∈ GlobalTheory.StdFrameExist.SI D) : x ∈ Bridge.hLat V h :=
  Submodule.subset_span ((mem_set_iff hV h x).2 hx)

theorem isLattice (hV : Seed.FrmC.StdLat V) (h : Bridge.Gf V) : Submodule.IsLattice D.host.E (Bridge.hLat V h) := by
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    ((Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
  obtain ⟨N₁, hN₁, hN₁m⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (invM h)
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  apply Submodule.IsLattice.of_fg D.host.E
  ·
    let T : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
      Submodule.span (𝓞 D.host.E) (Set.range fun j : Fin V.rank => (N : D.host.E)⁻¹ • (Pi.single j (1 : D.host.E)))
    refine fg_of_le_fg (Q := T) (Submodule.fg_span (Set.finite_range _)) (Submodule.span_le.2 fun x hx => ?_)
    have hx' := (mem_set_iff hV h x).1 hx
    have hint : ∀ i, IsIntegral ℤ ((N : D.host.E) * x i) := by
      intro i
      refine int_of_iv_mem ?_
      have e1 : ((N : D.host.E) * x i) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) =
          (((N : EAf D) • (Units.val ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))).map (swapAE D))
            *ᵥ (invM h *ᵥ iv x)) i := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, invM_mul, Matrix.one_mulVec, ← iv_natCast_smul]
        rfl
      rw [e1]
      exact GlobalTheory.StdFrameExist.intV (fun a b => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNm a b) hx' i
    choose c hc using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1 (hint i)
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 D.host.E)).2 ⟨c, ?_⟩
    funext l
    rw [Finset.sum_apply, Finset.sum_eq_single l]
    · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, smul_eq_mul, mul_one, hc]
      field_simp
    · intro b _ hb
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, smul_zero]
    · simp

theorem smul_mem_hLat_mul (hV : Seed.FrmC.StdLat V) (h x : Bridge.Gf V) (p : ℕ)
    (hp : ∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
  have hA : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) ((p : EAf D) • invM x) := fun a b => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hp a b
  have key : ∀ y, (∀ i, (invM h *ᵥ iv y) i ∈ GlobalTheory.StdFrameExist.SI D) → (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x) := by
    intro y hy
    refine mem_hLat_of hV _ fun i => ?_
    have e : (p : 𝓞 D.host.E) • y = (p : D.host.E) • y := by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e, iv_natCast_smul, mulVec_natCast_smul, invM_hmul, ← Matrix.smul_mul, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.StdFrameExist.intV hA hy i
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (h * x)).comap ((p : 𝓞 D.host.E) • LinearMap.id) :=
    Submodule.span_le.2 fun y hy => key y ((mem_set_iff hV h y).1 hy)
  exact hle hy

theorem ratF_val (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) =
      γE.val.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E) := by
  show Units.val (finHom V (γ : GA D V)) = _
  rw [finHom, MonoidHom.comp_apply, hγ]
  ext i j
  simp only [Formalism.UG.bc, incA]
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ[D.host.F] (γE.val i j)) =
    (1 : Af D.host.F) ⊗ₜ[D.host.F] γE.val i j
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem gl_cancel {R : Type} [CommRing R] {n : ℕ} (a b : GL (Fin n) R) (v : Fin n → R) :
    Units.val (b * a)⁻¹ *ᵥ (b.val *ᵥ v) = Units.val a⁻¹ *ᵥ v := by
  rw [Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem vec_move (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    (Units.val ((Bridge.ratF V γ * h)⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      (Units.val (h⁻¹ : Bridge.Gf V).1) *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
  have hv : (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] (γE.val *ᵥ y) i) =
      Units.val ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
        (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] y i) := by
    rw [ratF_val γ γE hγ]
    funext i
    exact RingHom.map_mulVec (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E).toRingHom γE.val y i
  rw [hv]
  exact gl_cancel ((h : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    ((Bridge.ratF V γ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) _

theorem mulVec_mem_hLat (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) : ∀ y ∈ Bridge.hLat V h, γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  intro y hy
  have hle : Bridge.hLat V h ≤ (Bridge.hLat V (Bridge.ratF V γ * h)).comap
      ((Matrix.mulVecLin γE.val).restrictScalars (𝓞 D.host.E)) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (show _ ∈ latHat D.host.F D.host.E (L0c D V) by
      rw [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, vec_move γ γE hγ h y]
      exact hy)
  exact hle hy

theorem isRatMat_inv (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    Bridge.IsRatMat V γ⁻¹ γE⁻¹ := by
  unfold Bridge.IsRatMat at *
  rw [Subgroup.coe_inv, map_inv, map_inv, hγ]

theorem mem_hLat_iff (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE)
    (h : Bridge.Gf V) (y : Fin V.rank → D.host.E) :
    y ∈ Bridge.hLat V h ↔ γE.val *ᵥ y ∈ Bridge.hLat V (Bridge.ratF V γ * h) := by
  refine ⟨mulVec_mem_hLat γ γE hγ h y, fun hy => ?_⟩
  have := mulVec_mem_hLat γ⁻¹ γE⁻¹ (isRatMat_inv γ γE hγ) _ _ hy
  have e1 : Units.val γE⁻¹ *ᵥ (γE.val *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have e2 : Bridge.ratF V γ⁻¹ * (Bridge.ratF V γ * h) = h := by rw [map_inv, inv_mul_cancel_left]
  rw [e1, e2] at this
  exact this

theorem hLat_props : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → (∀ h, Submodule.IsLattice D.host.E (Bridge.hLat V h)) ∧ (∀ (h x : Bridge.Gf V) (p : ℕ), (∀ a b, (p : EAf D) * swapAE D ((x⁻¹ : Bridge.Gf V).1.val a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ y ∈ Bridge.hLat V h, (p : 𝓞 D.host.E) • y ∈ Bridge.hLat V (h * x)) ∧ ∀ (γ : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → ∀ h y, y ∈ Bridge.hLat V h ↔ γE.val.mulVec y ∈ Bridge.hLat V (Bridge.ratF V γ * h) :=
  fun _ _ hV => ⟨isLattice hV, smul_mem_hLat_mul hV, mem_hLat_iff⟩

end GlobalTheory.HLatStd
end
end

