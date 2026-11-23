module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadFromLocalization
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0946
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIteratedQuotientIntegralFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_local {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O]
    (t : SAB H (Sp O)) (hprop : IsProper t.G.hom) (hpol : GlobalTheory.LN.PolAt t (Out.jK O)) :
    Out.RelAmple t.G t.PP.L := by
  by_cases hf : _root_.IsField O
  · obtain ⟨u, ⟨mu⟩⟩ := GlobalTheory.PolLocal.exists_pull (Out.jK O) t
    obtain ⟨hA, hK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mu hpol
    haveI : IsIso (Out.jK O) := GlobalTheory.PolLocal.isIso_spMap _ (GlobalTheory.PolLocal.algebraMap_fractionRing_bijective O hf)
    exact (GlobalTheory.PolLocal.ample_kTriv_of_iso mu hA hK).1
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap ρ) t
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap V (FractionRing V))) tV
  have hpV : GlobalTheory.LN.PolAt tV (Out.jK V) := GlobalTheory.PolNormal.polAt_generic_pull ρ hρ mV hpol
  obtain ⟨hAK, hKK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mK hpV
  obtain ⟨hAV, hKV⟩ := GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre GlobalTheory.HomExtExamples.homExtSt_holds GlobalTheory.allSixLaws.1
    GlobalTheory.allSixLaws.2.1 E H V (FractionRing V) tV tK mK (GlobalTheory.PolLocal.isProper_of_map mV hprop) hAK hKK
  obtain ⟨uk, ⟨mk⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (IsLocalRing.residue V)) tV
  obtain ⟨hAk, hKk⟩ := GlobalTheory.PolLocal.pull_ample_kTriv mk hAV hKV
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mV mk
  let β : O →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp ρ
  have hpβ : GlobalTheory.LN.PolAt t (spMap β) := by
    rw [GlobalTheory.PolLocal.spMap_comp]
    exact GlobalTheory.LocM.PolFibre.polAt_of_map n (by haveI := hprop; infer_instance) hAk hKk
  obtain ⟨r, hr, hA⟩ := GlobalTheory.PolNearAmple.relAmple_near_of_polAt E H O t hprop (IsLocalRing.ResidueField V) β hpβ
  have hu : IsUnit r := isUnit_of_map_unit ρ r ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hr)
  obtain ⟨m₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  have e : spMap (RingHom.id O) = 𝟙 (Sp O) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact hA O (RingHom.id O) hu t (e ▸ m₀)

theorem relAmple_kTriv_of_generic {S : Type} [CommRing S] [IsDomain S] [CharZero S] [IsNoetherianRing S]
    (t : SAB H (Sp S)) (hp : IsProper t.G.hom) (hg : GlobalTheory.LN.PolAt t (Out.jK S)) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  have hA : Out.RelAmple t.G t.PP.L := by
    have := t.semi.quasiCompact
    have := t.semi.separated
    refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun q => ?_
    have : q.asIdeal.IsPrime := q.isPrime
    let O := Localization.AtPrime q.asIdeal
    obtain ⟨tO, ⟨m⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap S O)) t
    have hi : Function.Injective (algebraMap S O) :=
      IsLocalization.injective O q.asIdeal.primeCompl_le_nonZeroDivisors
    have : CharZero O := charZero_of_injective_algebraMap hi
    have hA := relAmple_local tO (GlobalTheory.PolLocal.isProper_of_map m hp) (GlobalTheory.PolNormal.polAt_generic_pull _ hi m hg)
    obtain ⟨w, hw, -⟩ := m.lin
    exact GlobalTheory.AmpleSpreadAt.relAmple_spread_at S q t.G t.PP.L hp t.PP.isLB tO.G m.φ tO.PP.L m.cart.1 tO.PP.isLB
      ⟨w, hw⟩ hA
  exact ⟨hA, GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic E H S t hp hA hg⟩

theorem isProper_relAmple_kTriv_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (S : Scheme.{0}) (x : S ⟶ Sp R) (t' : SAB H S), (∀ s : S, ∏ i, tt i ∉ (x s).asIdeal) → Nonempty (SABMap t' t x) → IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab S x t' hx ⟨mx⟩
  have : CharZero R := algebraRat.charZero R
  have hf : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  generalize ∏ i, tt i = f at hf hab hx
  let Rf := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hi : Function.Injective (algebraMap R Rf) := IsLocalization.injective Rf hle
  have : IsDomain Rf := IsLocalization.isDomain_localization hle
  have : CharZero Rf := charZero_of_injective_algebraMap hi
  obtain ⟨tf, ⟨mf⟩⟩ := GlobalTheory.PolLocal.exists_pull (spMap (algebraMap R Rf)) t
  have hrange : Set.range (spMap (algebraMap R Rf)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range Rf f
  have habf : abLocus tf.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi mf.cart.1 z).1 ((hab _).2 (hrange.le ⟨z, rfl⟩))
  have hg : GlobalTheory.LN.PolAt tf (Out.jK Rf) := GlobalTheory.PolNormal.polAt_generic_pull _ hi mf (GlobalTheory.DatUniq.polAt_of_unif P)
  have hpf : IsProper tf.G.hom := GlobalTheory.ProperOfAbelianFibres.isProper_of_polAt_of_abLocus E H Rf tf hg habf
  obtain ⟨hA, hK⟩ := relAmple_kTriv_of_generic tf hpf hg
  have : IsOpenImmersion (spMap (algebraMap R Rf)) := by
    unfold spMap
    exact IsOpenImmersion.of_isLocalization f
  have hr : Set.range x ⊆ Set.range (spMap (algebraMap R Rf)) := by
    rintro _ ⟨s, rfl⟩
    exact hrange.ge (hx s)
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac mf mx (g := IsOpenImmersion.lift _ x hr)
    (IsOpenImmersion.lift_fac _ _ hr).symm
  obtain ⟨w, hw, -⟩ := m'.lin
  exact ⟨GlobalTheory.PolLocal.isProper_of_map m' hpf,
    GlobalTheory.AmpleLocalBase.relAmple_baseChange m'.cart.1 tf.PP.isLB t'.PP.isLB ⟨w, hw⟩ hA,
    kTriv_pull m'.cart tf.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.AbLocusPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlipVacB

open GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall GlobalTheory.PairLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_rd (hψ : IsStdChar D ψ (-1)) (S V : HSp D) (w : WO S V) (g : WO (negSp V) S → ℂ) :
    heisO ψ S V w (rd S V g) = rd S V (heisO ψ (negSp V) S (adjO (negSp V) S w) g) := by
  rw [rd_eq, GlobalTheory.CjNeg.heis_negT' hψ, GlobalTheory.AdjLawPf.adj_heis ψ hψ.1.2.1, ← rd_eq]

theorem heisenbergOperator_externalProductOnHermitianSum (S A B : HSp D) (u : WO S (GlobalTheory.Doubling.hsum A B)) (f : WO S A → ℂ) (g : WO S B → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 f g) =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) f) (heisO ψ S B (botR (A := A) (B := B) u) g) := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply, GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem externalProduct_latticeVacua_adjoint_isLatticeVacuum (hψ : IsStdChar D ψ (-1)) {S A B : HSp D} {Λ : AddSubgroup (WO S (GlobalTheory.Doubling.hsum A B))}
    {ΛA : AddSubgroup (WO S A)} {ΛB : AddSubgroup (WO (negSp B) S)}
    (h : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ adjO (negSp B) S (botR (A := A) (B := B) u) ∈ ΛB)
    {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : IsLatVac (heisO ψ S A) ΛA f)
    (hg : IsLatVac (heisO ψ (negSp B) S) ΛB g) :
    IsLatVac (heisO ψ S (GlobalTheory.Doubling.hsum A B)) Λ (box2 f (rd S B g)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : adjO (negSp B) S (botR (A := A) (B := B) (2 • u)) = 2 • adjO (negSp B) S (botR (A := A) (B := B) u) := by
      have e3 : botR (A := A) (B := B) (2 • u) = botR (A := A) (B := B) u + botR (A := A) (B := B) u := by
        rw [two_nsmul]; rfl
      rw [e3, two_nsmul]
      exact GlobalTheory.AdjLawPf.adj_add (negSp B) S _ _
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, e1, e2, hf.1 _ (h u hu).1, hg.1 _ (h u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, hf.2 e he _ (h u hu).1 h1,
      hg.2 _ he' _ (h u hu).2 (GlobalTheory.AdjLawPf.adj_half (negSp B) S e _ h2)]

theorem vac_ne_zero {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 (0 : WO S T → ℂ) = 1 := hn p hp
  simp [nrm2] at n1

theorem externalProduct_readThroughAdjoint_ne_zero {S A B : HSp D} {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    box2 f (rd S B g) ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  intro h0
  have := congrFun h0 (((GlobalTheory.BiTransfer.sumDec A B).resT S).symm (x, adjO S (negSp B) y))
  simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, rd] at this
  erw [GlobalTheory.AdjLawPf.adj_invol] at this
  exact mul_ne_zero hx hy this

theorem vac_eq_smul_vacB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  obtain ⟨A₁, h₁⟩ := exists_isGridFr W (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩
  have v1 := ρ.vT_is μ₀ i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have w1 : IsVacF W.ψ W.θ A₁ AV (ρ.vT i j) := ⟨v1.2.theta, fun s => by rw [c₁, cV]; exact v1.2.fock s⟩
  have w2 : IsVacF W.ψ W.θ (negFr AV₁) A₁ (ρ.vX i j) := ⟨v2.2.theta, fun s => by rw [c₁, cV₁]; exact v2.2.fock s⟩
  have w2' := rd_vac W.ψ_std W.θ_is A₁ AV₁ w2
  have key : IsVacF W.ψ W.θ A₁ (frSum AV AV₁) (box2 (ρ.vT i j) (rd _ _ (ρ.vX i j))) := by
    rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
    let o := GlobalTheory.BiTransfer.sumDec (spV G i j) (spV₁ G i j)
    refine ⟨o.isThetaFunO_boxT w1.1 w2'.1, fun τ z => ?_⟩
    have h1 := w1.2 τ (o.qA.map (tauE D τ) * z)
    have h2 := w2'.2 τ (o.qB.map (tauE D τ) * z)
    have e1 : o.qA.map (tauE D τ) = prL (spV G i j).rank (spV₁ G i j).rank := by
      rw [GlobalTheory.SeesawSumTarget.qA_sumDec]
      ext a b
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective b
      rcases s with s | s <;> simp [prL, Matrix.one_apply, apply_ite (tauE D τ)]
    have e2 : o.qB.map (tauE D τ) = prR (spV G i j).rank (spV₁ G i j).rank := by
      rw [GlobalTheory.SeesawSumTarget.qB_sumDec]
      ext a b
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective b
      rcases s with s | s <;> simp [prR, Matrix.one_apply, apply_ite (tauE D τ)]
    unfold annih at h1 h2 ⊢
    rw [GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o W.θ_is W.ψ_std τ _ w1.1 w2'.1,
      GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o W.θ_is W.ψ_std τ _ w1.1 w2'.1,
      GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (by rw [e1]; exact prL_cart AV AV₁ τ),
      GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (by rw [e2]; exact prR_cart AV AV₁ τ)]
    funext x
    have k1 := congrFun h1 (o.resT _ x).1
    have k2 := congrFun h2 (o.resT _ x).2
    simp only [GlobalTheory.MixModel.OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at k1 k2 ⊢
    linear_combination (rd _ _ (ρ.vX i j)) (o.resT _ x).2 * k1 + (ρ.vT i j) (o.resT _ x).1 * k2
  have e : vacB ρ i j = box2 (ρ.vT i j) (rd (spW₁ G i j) (spV₁ G i j) (ρ.vX i j)) := rfl
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have hl : IsLatVac (heisO W.ψ (spW₁ G i j) (spX G i j))
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ fun _ => True) (vacB ρ i j) := by
    rw [e]
    refine externalProduct_latticeVacua_adjoint_isLatticeVacuum W.ψ_std (fun u hu => ?_) v1.2.lat v2.2.lat
    have hu' : u ∈ orderingsOnSpWOne G i j := by rw [← hlat]; exact hu
    exact hu'
  obtain ⟨a, ha⟩ := GlobalTheory.LevelSeries.eq_smul_vacuum W.ψ_std W.θ_is (W.cart_is (.grid i j) ⟨i.2.le, j.2.le⟩)
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv (frSum AV AV₁)) s0 hΛ hf (f' := vacB ρ i j) key.1 hl
    (fun s => by have := key.2 s; rw [c₁] at this; exact this)
  have hne : vacB ρ i j ≠ 0 := by rw [e]; exact externalProduct_readThroughAdjoint_ne_zero (vac_ne_zero v1) (vac_ne_zero v2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlipVacB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepKeepsSphericalOfLatticeStabilizer
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.SphMove

theorem isSphOff_om : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GlobalTheory.Core.Rk.IP.WRep A B),
  IsWeilDatumO ψ A B χA χB om → ∀ (LA : Lat A) (LB : Lat B), IsSelfDualC A LA → IsSelfDualC B LB →
  ∀ (Sf : Finset (FinPl D)) (g : GA D A), g ∈ openOff A LA Sf → ∀ f, IsThetaFunO ψ A B f → IsSphOff ψ A B LA LB Sf f →
    IsSphOff ψ A B LA LB Sf (om (g, 1) f) := by
  intro D ψ A B χA χB om hW LA LB hA hB Sf g hg f hf hsph
  have hmv : GlobalTheory.FinPl.Moves A g LA LA (fun v => v ∉ Sf) :=
    (GlobalTheory.QLawPf.moves_iff_forall hA _ g).2 fun v hv =>
      (GlobalTheory.StMoves.moves_iff_stabLoc A LA hA.1.fg v g).2 (hg v hv)
  have hmi : GlobalTheory.FinPl.Moves A g⁻¹ LA LA (fun v => v ∉ Sf) := GlobalTheory.StMoves.moves_inv hmv
  have hm1 : GlobalTheory.FinPl.Moves B (1 : GA D B)⁻¹ LB LB (fun v => v ∉ Sf) := by
    intro y _
    rw [inv_one, show mt B (1 : GA D B) = 1 from rfl, Matrix.one_mulVec]
  have key : ∀ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf),
      actO A B g⁻¹ (1 : GA D B)⁻¹ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf) :=
    fun u hu => GlobalTheory.MidVacLat.actO_mem_latO hA hA hB hB hmi hm1 hu
  have step : ∀ w, heisO ψ A B (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f = f →
      heisO ψ A B w (om (g, 1) f) = om (g, 1) f := by
    intro w hw
    have h := hW.om_heis g 1 (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f hf
    rw [hw, GlobalTheory.MidVacLat.actO_actO_inv] at h
    exact h.symm
  refine ⟨fun u hu => step _ ?_, fun e he u hu hh => step _ ?_⟩
  · rw [GlobalTheory.MidVacLat.actO_two_nsmul]
    exact hsph.1 _ (key u hu)
  · exact hsph.2 e he _ (key u hu) (GlobalTheory.MidVacLat.isHalf_actO _ _ hh)

end GlobalTheory.SphMove
end

