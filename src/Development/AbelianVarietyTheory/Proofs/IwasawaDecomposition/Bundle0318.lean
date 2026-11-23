module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseFrobSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.OSplitBig

def sysPol (D : D7) (c : PlE D.host → ℕ → ℂ) (w : PlE D.host) : ℂ[X] :=
  X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
    C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c w k) * X ^ (D.R.nV - k)

def frobSet (D : D7) (F : Finset (PlE D.host)) : Set (G D.host.E D.nd.Om) :=
  {σ | ∃ w : PlE D.host, w ∉ F ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem dense_frobSet (D : D7) (h : GlobalTheory.RowTie.ChebSplit D.nd) (F : Finset (PlE D.host)) :
    Dense (frobSet D F) := h F

theorem heckePol_map (D : D7) (L : LocAll (lay0 D)) (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i) (v : PlE D.host)
    (hv : SplitOut (withLoc L).nd i v) :
    (heckePol (withLoc L).nd i x v).map (iotaOC (withLoc L) i) =
      sysPol D (GlobalTheory.CoefDuty.ptSys (withLoc L) i x) v := by
  have hS := hv
  obtain ⟨hsp, hl, hSi, hQ⟩ := hv
  have hgen : ∀ k ∈ Finset.Icc 1 D.R.nV,
      GenAt (withLoc L) ((withLoc L).nd.l i) ((withLoc L).nd.Q i) v k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    refine ⟨hsp, hl, ?_, hQ, hk1, hk2⟩
    intro hmem
    exact hSi (((withLoc L).nd.S_def i v).2 hmem)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [heckePol, sysPol, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [GlobalTheory.CoefDuty.ptSys, if_pos (hgen k hk), map_mul, map_pow, map_neg, map_one, map_natCast]
  rfl

end GlobalTheory.OSplitBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt.Disc

section Gen

variable {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def quotMapEquiv (e : V ≃ₗ[R] W) (A L : Submodule R V) (A' L' : Submodule R W) (hA : A.map (e : V →ₗ[R] W) = A')
    (hL : L.map (e : V →ₗ[R] W) = L') : (A ⧸ L.comap A.subtype) ≃ₗ[R] (A' ⧸ L'.comap A'.subtype) := by
  subst hA hL
  refine Submodule.Quotient.equiv _ _ (e.submoduleMap A) ?_
  ext ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨z, hz, hze⟩
    have : (z : V) = x := e.injective (congrArg Subtype.val hze)
    exact ⟨x, this ▸ hz, rfl⟩
  · rintro ⟨x', hx', hxe⟩
    have : x' = x := e.injective hxe
    subst this
    exact ⟨⟨x', hx⟩, hx', rfl⟩

end Gen

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {Pr.piT u} = ⨅ P : Pr.vT u, P.1.asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact decoFin_mem_of_mem_divs P.2
  · exact Ideal.mem_span_singleton.2 (piT_dvd_of_mem hX hPr u r fun P => Ideal.mem_iInf.1 hr P)

theorem span_conj_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {X.conjO (Pr.piT u)} = ⨅ P : Pr.vT u, (conjPrime₂ P.1).asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show cO X.E (X.conjO (Pr.piT u)) ∈ P.1.asIdeal
    rw [show cO X.E (X.conjO (Pr.piT u)) = Pr.piT u from cO_cO _]
    exact decoFin_mem_of_mem_divs P.2
  · obtain ⟨s, hs⟩ := piT_dvd_of_mem hX hPr u (cO X.E r) fun P => Ideal.mem_iInf.1 hr P
    refine Ideal.mem_span_singleton.2 ⟨cO X.E s, ?_⟩
    have := congrArg (cO X.E) hs
    rw [cO_cO, map_mul] at this
    exact this

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_T_eq {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)} = Ideal.span {Pr.piT u} ⊓ Ideal.span {X.conjO (Pr.piT u)} := by
  rw [← hPr.piT_norm u, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.mul_eq_inf_of_coprime ((Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)).sup_eq

theorem quotT_equiv {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Nonempty ((𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃ₗ[𝓞 X.E]
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal))) := by
  have hco : IsCoprime (Ideal.span {Pr.piT u}) (Ideal.span {X.conjO (Pr.piT u)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)
  have hp1 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => P.1.asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne P.1.isMaximal Q.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hp2 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => (conjPrime₂ P.1).asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (conjPrime₂ P.1).isMaximal (conjPrime₂ Q.1).isMaximal fun h => hne (Subtype.ext ?_)
    ext x
    have h2 := congrArg (fun J : Ideal (𝓞 X.E) => cO X.E x ∈ J) h
    simp only [conjPrime₂, Ideal.mem_comap, cO_cO] at h2
    exact Iff.of_eq h2
  let φ : (𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃+*
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal)) :=
    (Ideal.quotEquivOfEq (span_T_eq hPr u)).trans ((Ideal.quotientInfEquivQuotientProd _ _ hco).trans
      (RingEquiv.prodCongr
        ((Ideal.quotEquivOfEq (span_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp1))
        ((Ideal.quotEquivOfEq (span_conj_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp2))))
  exact ⟨(AlgEquiv.ofRingEquiv (f := φ) fun a => rfl).toLinearEquiv⟩

end GlobalTheory.Mem.Col2.HAt.Disc


open GlobalTheory.Mem.Col2.HAt.Disc in
theorem GlobalTheory.Mem.Col2.TC.disc_cl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  intro B X I hI hP l Z H F _ _ u i hi c
  obtain ⟨hG, -, hc⟩ := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hL : latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c) = ((I.stp u I.mu0 i).rep c).1.1.deco.1.L := (hc u I.mu0).1 c
  have hD : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i c) =
      ((I.stp u I.mu0 i).rep c).1.1.deco.1.Lsh := by
    refine (dual_co (I.rec7 l Z).sp.cm _ (rankN (I.rec7 l Z) i hi) _).trans ?_
    have h1 := BwLat.dualL_std (E := B.host.E) (sigD (I.rec7 l Z)).toRingHom (fun x => rfl) ((I.stp u I.mu0 i).rep c).1.1.deco.1.L
    exact (congrArg₂ (dualL _) hG hL).trans h1
  have hc' : ∀ P Q : (B.primes X).vT u, Q.1 ≠ conjPrime₂ P.1 := fun P Q => (moveHyp_of_ok l.pr u P).st Q
  obtain ⟨e1⟩ := ((I.stp u I.mu0 i).rep c).1.1.deco.2.Lsh_quot_L hc'
  obtain ⟨e2⟩ := quotT_equiv (FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u
  exact ⟨(quotMapEquiv ((crdN (I.rec7 l Z) i hi).restrictScalars (𝓞 (I.rec7 l Z).host.E)) _ _ _ _ hD hL) ≪≫ₗ e1 ≪≫ₗ e2.symm⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem coeFn_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type} [Fintype ι] (c : ι → ℂ)
    (u : ι → Lp ℂ 2 μ) :
    ((∑ i, c i • u i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i, c i * (u i : α → ℂ) x := by
  first
  | exact @_root_.GlobalTheory.FinsetSumSmulCoe.main
  | exact _root_.GlobalTheory.FinsetSumSmulCoe.main
  | (apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetSumSmulCoe.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetSumSmulCoe.main ..)

theorem sum_smul_apply {ι α : Type} [Fintype ι] (L : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (c : ι → ℂ) (φ : α → ℂ) (y : α) :
    (∑ i, c i • L i) φ y = ∑ i, c i * L i φ y := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp

theorem iotaX_symm_rat {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : X.B.I.GA)
    (hz : z ∈ X.B.I.GFset) : (iotaX X h).symm z ∈ GQ (D.sp.Y 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (z : I.GA), z ∈ I.GFset →
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm z ∈ GQ (D.sp.Y 0) := by
    intro I hI z hz
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm z =
        (Formalism.IndefR.RationalEmbedding.iota D).symm z := rfl
    rw [e, Formalism.IndefR.RationalEmbedding.iota_rat, ContinuousMulEquiv.apply_symm_apply]
    exact hz
  exact aux X.B.I h z hz

theorem ev_translate {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G')
    (red : X.B.I.Gf → G0g D.nd) (hB : LevelMatchB R F X h t σ red) (S : MMap (MP R)) (hS : S ∈ MultR R F)
    (k : X.B.I.Gf) (hk : k ∈ X.B.I.Kset) (x : X.B.I.GA) :
    ev (MP R) v₀ S ((iotaX X h).symm (x * (1, k)) * t) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
  have hk' := hB.2 k hk S hS v₀ ((iotaX X h).symm x * t)
  refine Eq.trans ?_ hk'
  have e : (iotaX X h).symm (x * (1, k)) * t = (iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k) := by
    unfold kap
    rw [map_mul]
    group
  show S v₀ _ = S v₀ _
  rw [e]
  rfl

theorem evalAct_intertwines : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) [Fintype (G0g D.nd)] (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G') (red : X.B.I.Gf → G0g D.nd), LevelMatchB R F X h t σ red → ∀ S ∈ MultR R F, ∀ f : L2X X, (f =ᵐ[muX X] fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g) → ∀ (a : G0g D.nd → ℂ) (s : G0g D.nd → X.B.I.Gf), (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star f)) : L2X X) =ᵐ[muX X] fun x => gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (a (σ.symm g))) (S v₀) ((iotaX X h).symm x * t) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F _ X h t v₀ σ red hB S hS f hf hinv a s hs
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec

  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      ev (MP R) v₀ S ((iotaX X h).symm (γ * y) * t) = ev (MP R) v₀ S ((iotaX X h).symm y * t) := by
    intro γ hγ y
    show S v₀ _ = S v₀ _
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have key : ∀ k ∈ X.B.I.Kset, ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
    intro k hk
    have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
      Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
    have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
      have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
      rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
    obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
    have e1 := X.B.R_spec (1, k) f
    have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
        ev (MP R) v₀ S ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
      refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = ev (MP R) v₀ S ((iotaX X h).symm y * t)) h1 ?_
      rw [h2]
      exact hf
    filter_upwards [e1, e3] with x a1 a3
    rw [a1]
    show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
    rw [a3]
    obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
    rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
      hφinv γ hγ]
    exact ev_translate R F X h t v₀ σ red hB S hS k hk x
  have hall : ∀ᵐ x ∂(muX X), ∀ γ, ((X.B.R (1, s γ) f : L2X X) : X.B.I.GA → ℂ) x =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red (s γ)))) (S v₀) ((iotaX X h).symm x * t) :=
    ae_all_iff.2 fun γ => key (s γ) (hs γ).1
  have hsum := coeFn_sum_smul (μ := muX X) (fun γ => star (a γ)) (fun γ => star (X.B.R (1, s γ) (star f)))
  filter_upwards [hsum, hall] with x b1 b2
  rw [b1]
  simp only [Formalism.L2.SG.Pf.RowDictPf.R_star, star_star]
  simp only [b2, (hs _).2]
  unfold gaL
  refine Eq.trans ?_ (sum_smul_apply _ _ _ _).symm
  refine Fintype.sum_equiv σ.toEquiv _ _ (fun γ => ?_)
  show _ = star (a (σ.symm (σ γ))) * _
  rw [MulEquiv.symm_apply_apply]
  rfl

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldLowerBoundsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientField_lower_bounds : ∀ (D : D7), ∃ c0 : Big D, ∀ (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l), (∀ x, j x ∈ (c0 l j).1) ∧ muK l 1 ≤ (c0 l j).1 ∧ ∀ K0 : Loc.FinExt l, (c0 l j).1 ≤ K0.1 → ∀ w ∈ placesOver D.host.E l, ∃ Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL K0), ∀ x, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1 := by
  first | exact @GlobalTheory.CoeffFieldLower.exists_low | exact GlobalTheory.CoeffFieldLower.exists_low | (intros; apply GlobalTheory.CoeffFieldLower.exists_low <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypePartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ p, HasLab Y σ p := by
  first | exact @GlobalTheory.Mem.R3.LabProof.hasLab_exists | exact GlobalTheory.Mem.R3.LabProof.hasLab_exists | (intros; apply GlobalTheory.Mem.R3.LabProof.hasLab_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteSplittingSetFrobeniusPolynomials
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.OSplitCore

theorem mem_mul_of_mem {A : Type} [CommRing A] (R : Subring A) {m n q : ℕ} (X : Matrix (Fin m) (Fin n) A)
    (Y : Matrix (Fin n) (Fin q) A) (hX : ∀ i j, X i j ∈ R) (hY : ∀ i j, Y i j ∈ R) :
    ∀ i j, (X * Y) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => R.mul_mem (hX _ _) (hY _ _)

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f :=
  rfl

theorem mapped_props (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (U : Set Γ) (p : Γ → ℂ[X]) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hadic : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (r : Γ →* GL (Fin a) O) (hr : Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)))
    (hss : IsSSRep (mapRep (algebraMap O (FractionRing O)) r))
    (hp : ∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map
      (ι.toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) :
    IsSSRep (mapRep iq (mapRep (algebraMap O (FractionRing O)) r)) ∧
    Continuous (fun g => ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l))) ∧
    (∀ σ ∈ U, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) σ : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
      (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j,
      ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R := by
  have hcz : CharZero (FractionRing O) := ⟨fun m n h => by
    have := congrArg iq h
    simpa using this⟩
  have hcoe : ∀ g, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)) =
      ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (iq.comp (algebraMap O (FractionRing O))) := by
    intro g
    rw [coe_mapRep, coe_mapRep, Matrix.map_map]
    rfl
  refine ⟨GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ iq a _ hss, ?_, ?_, ?_⟩
  · simp only [hcoe]
    exact hr.matrix_map (GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure l O hadic iq hiq)
  · intro σ hσ
    rw [hcoe, Matrix.charpoly_map, Polynomial.map_map]
    exact hp σ hσ
  · obtain ⟨T, hT⟩ := GlobalTheory.T.exists_finset_image_mem_subring l O iq hiq
    refine ⟨T, fun R hR hTR g i j => ?_⟩
    rw [hcoe]
    exact hT R hR hTR _

theorem exists_splitting_set : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (G E Ω)) (p : G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ (l' : ℕ) [Fact l'.Prime] (h : l = l') (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l'] O] [Module.Finite ℤ_[l'] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l', (∀ z : ℤ_[l'], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l'] O z)) = algebraMap ℚ_[l'] (Qbar l') (z : ℚ_[l'])) → (∀ z ∈ S, ∃ x, qCast h ι (iq x) = z) → ∀ r : G E Ω →* GL (Fin a) O, Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) → IsSSRep (mapRep (algebraMap O (FractionRing O)) r) → (∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map ((qCast h ι).toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) → GlobalTheory.SplitCoef.SplitRep (mapRep (algebraMap O (FractionRing O)) r) := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ (ρ₀ : G E Ω →* GL (Fin a) (Qbar l)) (T : Finset (Qbar l)), IsSSRep ρ₀ ∧
      Continuous (fun g => ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
      ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
        (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j, ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R
  swap
  · refine ⟨∅, ?_⟩
    intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq _ r hr hss hp
    subst h
    exfalso
    obtain ⟨h1, h2, h3, T, h4⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
    exact hex ⟨_, T, h1, h2, h3, h4⟩
  obtain ⟨ρ₀, T, hss₀, hc₀, hp₀, hT⟩ := hex
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.semisimple_matrix_rep_decomp ρ₀ hss₀
  choose b E D σ₀ hDE hran hσ₀ using fun j => GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep ρ₀ (Vs j) (hirr j).2.1
  let T' : Finset (Qbar l) := T ∪ Finset.univ.biUnion (fun j : Fin n =>
    Finset.univ.image (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) ∪
      Finset.univ.image (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2))
  refine ⟨T'.image ι, ?_⟩
  intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq hS r hr hss hp
  subst h
  obtain ⟨hss', hc', hp', -⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
  have hT'R : ∀ t ∈ T', t ∈ iq.range := by
    intro t ht
    obtain ⟨x, hx⟩ := hS (ι t) (Finset.mem_image_of_mem _ ht)
    exact ⟨x, ι.injective hx⟩
  have hRz : ∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ iq.range := fun z => ⟨_, hiq z⟩
  have hTR : (↑T : Set (Qbar l)) ⊆ (iq.range : Set (Qbar l)) := fun t ht => hT'R t (Finset.mem_union_left _ ht)
  have hER : ∀ j i s, E j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hDR : ∀ j i s, D j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hρ₀R := hT iq.range hRz hTR
  set ρ := mapRep (algebraMap O (FractionRing O)) r with hρ
  have hcp : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
    _root_.GlobalTheory.charpoly_eq_of_eqOn_dense _ _ hc' hc₀ U hU fun x hx =>
      Polynomial.map_injective _ ι.injective (by rw [hp' x hx, hp₀ x hx])
  obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (mapRep iq ρ) ρ₀ hss' hss₀ hcp
  have hint' : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) =
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) * ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g
    rw [hPm g]
    simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  apply _root_.GlobalTheory.SplitCrit.splitRep_of_models iq ρ
  intro V hV
  obtain ⟨j, M, hM, hMV, hMd⟩ := _root_.GlobalTheory.ConstituentImage.exists_constituent_image (mapRep iq ρ) ρ₀ Pm hint' hss' Vs
    hint.submodule_iSup_eq_top hirr V hV
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.lift_rep_of_entries_in_image iq (σ₀ j) fun g i s => by
    have : ((σ₀ j g : GL (Fin (b j)) (Qbar l)) : Matrix (Fin (b j)) (Fin (b j)) (Qbar l)) i s ∈ iq.range := by
      rw [(hσ₀ j g).1]
      exact mem_mul_of_mem _ _ _ (mem_mul_of_mem _ _ _ (hDR j) (hρ₀R g)) (hER j) i s
    exact this
  refine ⟨b j, σ, M * E j, ?_, ?_, ?_⟩
  · intro v w hvw
    simp only [← Matrix.mulVec_mulVec] at hvw
    have hv : (E j).mulVec v ∈ Vs j := hran j ▸ ⟨v, rfl⟩
    have hw : (E j).mulVec w ∈ Vs j := hran j ▸ ⟨w, rfl⟩
    have hsub : (E j).mulVec v - (E j).mulVec w ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 hvw
    have h0 := hMd.le_bot ⟨hsub, Submodule.sub_mem _ hv hw⟩
    have hEq : (E j).mulVec v = (E j).mulVec w := sub_eq_zero.1 h0
    have := congrArg (D j).mulVec hEq
    simpa [Matrix.mulVec_mulVec, hDE j] using this
  · rw [Matrix.mulVecLin_mul, LinearMap.range_comp, hran j, hMV]
  · intro g
    rw [hσ, ← Matrix.mul_assoc, hM g, Matrix.mul_assoc, (hσ₀ j g).2, Matrix.mul_assoc]

end GlobalTheory.OSplitCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelJ_character_eq_member_off_places : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | exact GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | (intros; apply GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_lift_from_residueField : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m → ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  first | exact @GlobalTheory.TameLift.exists_lift | exact GlobalTheory.TameLift.exists_lift | (intros; apply GlobalTheory.TameLift.exists_lift <;> assumption)
end

