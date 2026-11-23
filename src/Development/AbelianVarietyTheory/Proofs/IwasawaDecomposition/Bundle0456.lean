module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChain
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberChartMatchingAwayFromTwist
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw


set_option maxHeartbeats 8000000 in
theorem match_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → ∀ (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ ∀ β, ∃ c, chartOf I u a i c = β ∧ ∃ c0, chOf0 c0 = g β ∧ ∀ x : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) x = 1) → (∀ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ → ∃ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧ (∀ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 → ∃ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ) := by
  intro B X I hI hP l u a Q i hi Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 h1 h2 hQ hR0
  obtain ⟨c0f, t, ht1, ht2, ht3, hM⟩ := GlobalTheory.T.match_tupleChart_memberChart I hI hP l u a Q i hi h1 h2 hQ
  refine ⟨fun β => chOf0 (c0f β), fun β => k0 (chOf0 (c0f β)) * t β,
    GlobalTheory.T.admissibleBasePoint_chart_mul_twist_alt I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR0 _ t ht1 ht2 ht3, ?_⟩
  intro β
  obtain ⟨c, hc, hs⟩ := hM β
  refine ⟨c, hc, c0f β, rfl, ?_⟩
  intro x hx
  have e : (k0 (chOf0 (c0f β)) * t β)⁻¹ * x * (k0 (chOf0 (c0f β)) * t β) =
      (t β)⁻¹ * ((k0 (chOf0 (c0f β)))⁻¹ * x * k0 (chOf0 (c0f β))) * t β := by group
  rw [e]
  refine hs _ fun v hv => ?_
  rw [map_mul, map_mul, hx v hv, mul_one, map_inv, inv_mul_cancel]


set_option maxHeartbeats 8000000 in
theorem charts_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k ∧ ∀ (K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI hP l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR0
  obtain ⟨k0, hk0⟩ := hR0
  obtain ⟨g, k, hk, hM⟩ := match_base I hI hP l u a Q i hi Ch0 chOf0 _ _ _ _ _ k0 h1 h2 hQ hk0
  refine ⟨g, k, hk, ?_⟩
  intro K hK β
  obtain ⟨c, hc, c0, hc0, hx⟩ := hM β
  subst hc
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have huni : ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (B.T u) (I.rec7 l Z).R.f bad) (x : GA B (B.R.N i)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) := by
    intro bad S x hx
    have h := ((S.U_eq x).1 hx).1
    rw [hgram] at h
    exact h
  have hnQ0 : ∀ v, ¬ I.UnderQ I.mu0 v := by
    rintro v ⟨P, hP, -⟩
    rw [ColIn.twistPrimes_reference_tuple_eq_empty] at hP
    exact absurd hP (Finset.notMem_empty _)
  refine ⟨fun κ hκ => ?_, fun κ' hκ' => ?_⟩
  · obtain ⟨κ1, hl1⟩ := GlobalTheory.T.chartLevel_twistTrivial_localMove I hI l u a i hi _ _ _ _ _ _ k hK c κ.1 (huni _ κ.1 κ.2)
      (fun v hv => hκ v ((hQ v).2 hv)) κ.2
    obtain ⟨κ0, hl0, hchr⟩ := (hx κ.1 hκ).1 κ1 hl1
    obtain ⟨hm0, hc0'⟩ := reads_of_locMv I hI hk0 c0 κ.1 κ0 (by rw [hc0]; exact hl0)
    obtain ⟨hm, hcc⟩ := reads_of_locMv I hI hK c κ.1 κ1 hl1
    have key : ∀ β0 (e : chOf0 c0 = β0), ∃ h' : κ.1 ∈ (K0 β0).lev.U,
        (((K0 β0).lev.chi ⟨κ.1, h'⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 i).chr c0.1 κ0 : B.LLˣ) : B.LL) := by
      intro β0 e
      subst e
      exact ⟨hm0, hc0'⟩
    obtain ⟨h', e'⟩ := key _ hc0
    refine ⟨h', Units.ext ?_⟩
    rw [e', ← hchr]
    exact hcc
  · have hm0 : κ'.1 ∈ (K0 (chOf0 c0)).lev.U := by rw [hc0]; exact κ'.2
    obtain ⟨κ0, hl0⟩ := GlobalTheory.T.chartLevel_twistTrivial_localMove I hI l u I.mu0 i hi _ _ _ _ _ _ k0 hk0 c0 κ'.1 (huni _ κ'.1 hm0)
      (fun v hv => absurd hv (hnQ0 v)) hm0
    rw [hc0] at hl0
    obtain ⟨κ, hl⟩ := (hx κ'.1 hκ').2 κ0 hl0
    exact (reads_of_locMv I hI hK c κ'.1 κ hl).1

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMidLevOfMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem nearAt_congr' {n : ℕ} {x x' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g g' : GL (Fin N) E}
    (h : GlobalTheory.TwU.NearAt P n x g) (hx : x = x') (hg : g = g') : GlobalTheory.TwU.NearAt P n x' g' := hx ▸ hg ▸ h

theorem nearAt_inv_int {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g h : GL (Fin N) E}
    (hx : GlobalTheory.TwU.NearAt P n x g) (hh : h = g⁻¹)
    (hint : ∀ a b, IntAt P ((h : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((h⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    GlobalTheory.TwU.NearAt P n x⁻¹ h := by
  subst hh
  unfold GlobalTheory.TwU.NearAt at *
  have := GlobalTheory.CplPt.congAt_conj n (GlobalTheory.LevFrame.congAt_inv F E N n P _ hn hx) hint
  convert this using 1
  rw [map_inv]
  group

end Gen

section Near

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
  (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))

theorem prCat_last_le_int (hI : I.Ok) (P : SBof I a) :
    prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1 ≤ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 := by
  have hL := hI.idx_ok a
  have e : B.R.m - 1 = B.R.m - 2 + 1 := by have := hL.hm; omega
  obtain ⟨b, -⟩ := hL.last_uniq
  have h := hL.int _ b P
  rw [hL.last_h] at h
  rw [e]
  exact h

theorem nearV_one (P : SBof I a) : NearV I l Z a v P 1 1 := by
  unfold NearV
  exact nearAt_congr' (GlobalTheory.TwU.nearAt_self (F := (I.rec7 l Z).host.F) _ _ 1) ((map_one _).trans (map_one _).symm) (map_one _).symm

theorem nearV_mul (P : SBof I a) {x y} {g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (hx : NearV I l Z a v P x g) (hy : NearV I l Z a v P y g') (hg' : g' ∈ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1) :
    NearV I l Z a v P (x * y) (g * g') := by
  unfold NearV at *
  exact nearAt_congr' (GlobalTheory.CplPt.nearAt_mul_int _ hx hy (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g', hg'⟩))
    (map_mul _ _ _).symm (map_mul _ _ _).symm

theorem nearV_inv (P : SBof I a) (hD : 1 ≤ (I.cst a).D P) {x}
    {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (hx : NearV I l Z a v P x g) (hg : g⁻¹ ∈ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1) :
    NearV I l Z a v P x⁻¹ g⁻¹ := by
  unfold NearV at *
  exact nearAt_congr' (nearAt_inv_int hD hx (map_inv _ _) (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g⁻¹, hg⟩))
    (map_inv _ _).symm rfl

theorem mem_of_midLev (P : SBof I a) {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))} {z : B.fields.K}
    (h : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z) :
    g ∈ prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1 :=
  (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g).1 ⟨z, h⟩

theorem exists_midLev_of_mem (P : SBof I a) {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (h : g ∈ prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1) :
    ∃ z, GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z :=
  (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g).2 h

end Near

theorem nearSet_closed : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), 1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v ∧
      (∀ x y, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → x * y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v) ∧
      ∀ x, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → x⁻¹ ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  intro B X I hI l Z a v
  refine ⟨fun P _ => ?_, fun x y hx hy P hP => ?_, fun x hx P hP => ?_⟩
  · obtain ⟨z, hz⟩ := exists_midLev_of_mem I a P (one_mem _)
    exact ⟨1, z, hz, nearV_one I l Z a v P⟩
  · obtain ⟨g, z, hgz, hxg⟩ := hx P hP
    obtain ⟨g', z', hgz', hyg'⟩ := hy P hP
    have hg := mem_of_midLev I a P hgz
    have hg' := mem_of_midLev I a P hgz'
    obtain ⟨z'', hz''⟩ := exists_midLev_of_mem I a P (mul_mem hg hg')
    exact ⟨g * g', z'', hz'', nearV_mul I l Z a v P hxg hyg' (prCat_last_le_int I a hI P hg')⟩
  · obtain ⟨g, z, hgz, hxg⟩ := hx P hP
    have hgi := inv_mem (mem_of_midLev I a P hgz)
    obtain ⟨z', hz'⟩ := exists_midLev_of_mem I a P hgi
    exact ⟨g⁻¹, z', hz', nearV_inv I l Z a v P ((hI.idx_ok a).cst_ok.D_pos P) hxg (prCat_last_le_int I a hI P hgi)⟩

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.PkRead


set_option maxHeartbeats 4000000 in
theorem exists_pkT : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G) (mL : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G), (∀ b μ, (mA b μ).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ μ j, (mL μ j).Laws D.what₂.embLL (idemOf A3.A.X)) → (∀ b t, mA b (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) → (∀ (i : Fin D.R.m) t, mL (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t) → ∃ p : PkD D G, p.mL = mL ∧ Nonempty (PkT F y mA p) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hO hI hP hH y mA mL hA hL hAe hLe
  obtain ⟨Φ, rep, hrep⟩ := _root_.GlobalTheory.RowTypeReps.reps_exist D G Pl0 I0 T A3 Ks R F cG hI hP hH y
  have hstar : ∀ x, D.what₂.embLL (star x) = starRingEnd ℂ (D.what₂.embLL x) := D.starLL_cx
  have hint : ∀ z, IsIntegral ℤ (D.what₂.OtoLL z) := D.O_int
  choose sA tA using fun b μ =>
    GlobalTheory.T.exists_complexification_of_definiteGroupForms' D.what₂.LL D.what₂.O D.what₂.OtoLL D.what₂.embLL G (mA b μ) (idemOf A3.A.X) hstar hint (hA b μ)
  choose sL tL using fun μ j =>
    GlobalTheory.T.exists_complexification_of_definiteGroupForms' D.what₂.LL D.what₂.O D.what₂.OtoLL D.what₂.embLL G (mL μ j) (idemOf A3.A.X) hstar hint (hL μ j)
  let tA' : ∀ b μ, Tie1 D.what₂.embLL (mA b μ) (sA b μ) := fun b μ => (tA b μ).some
  let tL' : ∀ μ j, Tie1 D.what₂.embLL (mL μ j) (sL μ j) := fun μ j => (tL μ j).some
  choose c hc using fun b =>
    GlobalTheory.T.exists_levelChain_over_top_spaces D G Pl0 I0 T A3 Ks R F cG hI hP hH y Φ rep hrep b (mA b) (sA b) (tA' b) (hAe b)
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_lift_spaces_over_definite_forms D G Pl0 I0 T A3 Ks R F cG hO hI hP hH y Φ rep hrep mL sL tL' hLe
  let chT := fun b => (hc b).some
  obtain ⟨nR, cR, Xo, hrr⟩ := _root_.GlobalTheory.Mem.R3.Rw.rrT_exists D G Pl0 I0 T A3 Ks R F cG hP hH y true (c true).EE (chT true).jE
    (chT true).jE_inj (chT true).jE_range
  haveI : Finite Φ := hrep.fin
  letI : Fintype Φ := Fintype.ofFinite Φ
  classical

  have hθ : IsInfFam R.θ := hP.char.base.models.inf
  have hfin : FiniteDimensional ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))) :=
    hI.hc (Yc D 0) (D.sp.Y_sig _) _ R.θ (R.MY 0) _ _ hθ (hI.lev (Yc D 0) (R.βY 0) _).2
  set Dall := Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))) with hDall
  have hn : Dall = 0 → (c true).n = 0 := by
    intro h0
    have hM : Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) = ⊥ :=
      Submodule.finrank_eq_zero.1 h0
    have hE : (y.C F.lv2).EEc true = ⊥ := by
      show (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0).map _ = ⊥
      rw [eq_bot_iff.2 ((Mult.goodPart_le _ _ _ _ _).trans hM.le)]
      exact Submodule.map_bot _
    have hr := (chT true).jE_range
    rw [hE] at hr
    have h1 := LinearMap.finrank_range_of_inj (chT true).jE_inj
    rw [hr, finrank_bot] at h1
    have h2 := Module.finrank_eq_card_basis (c true).bs.toBasis
    rw [← h1, Fintype.card_fin] at h2
    exact h2.symm
  let dp : ℝ := if Dall = 0 then 0 else 1 - ((c true).n : ℝ) / Dall
  have hdelp : dp ≤ 1 := by
    simp only [dp]
    split_ifs
    · norm_num
    · have : (0 : ℝ) ≤ ((c true).n : ℝ) / Dall := by positivity
      linarith
  have hD : (((c true).n : ℕ) : ℝ) = (1 - dp) * Dall := by
    simp only [dp]
    split_ifs with h
    · rw [hn h, h]; simp
    · have : (Dall : ℝ) ≠ 0 := by exact_mod_cast h
      field_simp
      ring
  refine ⟨{ Φ := Φ, sA := sA, mL := mL, sL := sL, tL := tL', ch := c, lf := l, Dall := Dall, delp := dp, delp_le_one := hdelp, D_eq := hD, nR := nR, cR := cR, Xo := Xo }, rfl, ⟨?_⟩⟩
  exact { rep := rep, reps := hrep, tA := tA', lawsA := hA, lawsL := hL, hA := hAe, hL := hLe, ch := chT, lf := hl.some, dall := rfl, rr := hrr }

end GlobalTheory.Mem.R3.Rw.PkRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaDataTrueRowsColumnsAllCompatible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaRecordTrue

theorem recFun_of_rows (hR : GlobalTheory.Published.CuspRapidDecay) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (what₂ : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch)
    (hio : ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) :
    ∀ θ : InfF (w.D Z), IsInfFam θ → ∀ ψ, IsStdChar (w.D Z) ψ (-1) → ∀ Wf : WeilFun (w.D Z) ψ,
      ∃ Rc : RecFun (w.D Z) θ ψ, Rc.ChrIs (TC.cf w.I w.l Z) n.tp.xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ}, ∀ j, j ≤ (w.D Z).R.m → ∀ x y : (w.D Z).what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt ((w.D Z).sp.Y j) (Rc.mY μ j * Rc.petC ((w.D Z).sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y) := by
  intro θ hθ ψ hψ Wf
  letI : Algebra what₂.r.z.core.Q.c.F (w.D Z).what₂.LL := what₂.r.z.alg
  have h3 := Formalism.IndefR.Links.RealDat3.characterisation_of_weak what₂.r.z.pins.char what₂.exAt
  have hC : what₂.r.z.R.toRealDat.C = TC.cf w.I w.l Z := what₂.r.z.lev.C
  obtain ⟨Rc, h1, h2, h4⟩ := _root_.GlobalTheory.Mem.RowsTies.rows_of_ties hR (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat h3.lev h3.models h3.chain n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} what₂.r.Y.tupT n.tp.xi_fin n.tp.xi_triv
    (fun μ hμ => ⟨by
        rw [what₂.r.z.lev.xiH, ← what₂.r.tup_ix, what₂.r.Y.tupTie μ hμ, ← n.xi]; rfl,
      _root_.GlobalTheory.RowTieRead.weak_tie (w.D Z) _ _ _ _ _ what₂.r.z.R.toRealDat what₂.r.z.F.lv2 what₂.r.Y.tupT what₂.r.Y.hm what₂.r.Y.hTop what₂.r.Y.Ish _
        (w.D Z).what₂.onb (w.D Z).what₂.ft h3.models h3.chain what₂.r.Y.tied.sharp μ hμ⟩)
    (fun μ hμ => hio μ hμ) θ hθ ψ hψ Wf
  rw [hC] at h1
  exact ⟨Rc, h1, h2, h4⟩


set_option maxHeartbeats 1000000 in
theorem thEx_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) → ∀ 𝒮 : Slots, (∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0) → ThEx 𝒮 := by
  intro hW hR _ _ hDS hDSu hDSR 𝒮 hio
  refine StepW.of_all fun K B f T w _ _ _ Z l => ?_
  obtain ⟨X, hio', -, A, a, heq, hchr⟩ := GlobalTheory.Mem.Th.exists_allTied_eqTied_on hW hR hDS hDSu hDSR (w.D Z) (TC.cf w.I w.l Z) l.n.tp.xi
    {μ | Formalism.IndefR.RecTie.Used0 (w.D Z) μ} l.real (recFun_of_rows hR l.what₂ l.n (hio K B f T w Z l.Wt l.p0 l.what₂ l.rx))
  obtain ⟨H, hH⟩ := hchr l.nch l.n.tp rfl
  exact ⟨X, ⟨⟨A, a, GlobalTheory.Mem.Th.weilTiedEq_of_eqTied _ _ _ _ heq, H,
    GlobalTheory.SameChrFin.sameChr_of_chrEq _ _ _ _ _ _ _ hH, a.W.ψ_std, hio'⟩⟩⟩

end GlobalTheory.ThetaRecordTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_linearMap_cuspFormMultiplicity : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta → R.thP_ioP → ∃ th, ({ R with thF := th } : RealDat D A Ks).thP_thF_mem ∧ ({ R with thF := th } : RealDat D A Ks).thP_thF := by
  first | exact @GlobalTheory.DefLift.ThetaMap.exists_thetaMap | exact GlobalTheory.DefLift.ThetaMap.exists_thetaMap | (intros; apply GlobalTheory.DefLift.ThetaMap.exists_thetaMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqClosedContentNumericalDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.Bl

theorem forcedContent_eq_closedContent_numericalDatum : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), DV.KapDef D →
    ∀ (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m),
      GlobalTheory.Mem.Top.Bl.F0K L.sc D y j = (ofRecord D L Del h0).Fj (j.1 + 1) y :=
  fun D L Del h0 hK y j => (ofRecord_Fj_succ D L Del h0 hK y j).symm

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentSupportPrimes
section
noncomputable section

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def forcedContentSupportPrimes (K : Ctx) (P : Pre) : Finset ℕ :=
  {P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1)

end GlobalTheory.Mem.NonzeroPlacesOverPrimes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralAlgebraicConstantsMemRangeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) [GeometricallyIntegral p] (b : Y.functionField), (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) → b ∈ (GlobalTheory.Cartier.constFn p).range := by
  first | exact @GlobalTheory.GeomIntConst.mem_range_constFn | exact GlobalTheory.GeomIntConst.mem_range_constFn | (intros; apply GlobalTheory.GeomIntConst.mem_range_constFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.GoodDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare Formalism.L2.DIV GlobalTheory.BI

theorem isChar_inv {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem goodIdempotent_coeff_inv_eq_coeff {D : D7} {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (h : G0g D.nd) :
    D.ntypes.e0.coeff h⁻¹ = D.ntypes.e0.coeff h := by
  obtain ⟨x, rfl⟩ := pull_bijective.2 h
  have e : (pull x)⁻¹ = pull x⁻¹ := rfl
  rw [e, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ x x⁻¹
    (fun v _ => by rw [Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)

theorem goodStable_of_coeff {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hirr : ∀ χ ∈ X, IsAbsIrrChar χ)
    (hsym : ∀ g, (idemOf X).coeff g⁻¹ = (idemOf X).coeff g) : GoodStable X := by
  classical
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf emb X hirr X
    (fun ψ g => emb (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar emb (hirr ψ hψ)
      exact isChar_inv ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
        map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply emb.injective
  simpa using hψe g⁻¹

end GlobalTheory.Mem.R3.GoodDual

end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLiftsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_step_character_inverse_type_at_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal | exact GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal | (intros; apply GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal <;> assumption)
end

