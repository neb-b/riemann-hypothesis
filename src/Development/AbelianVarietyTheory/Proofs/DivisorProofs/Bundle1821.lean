module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem continuous_mapLoc (w : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))

omit [IsCMField E] in
theorem entry_mem_of_mem_KGL {w : Pl E} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    g.val i j ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  obtain ⟨k, rfl⟩ := hg
  exact (k.val i j).2


omit [IsCMField E] in
theorem isCompact_box (D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E))) (hD : ∀ w, IsCompact (D w))
    (hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w (n := n)) :
    IsCompact {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
  let Q : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) '' D w
  let Q' : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => (g⁻¹).val i j) '' D w
  have hQ : ∀ i j w, IsCompact (Q i j w) := fun i j w =>
    (hD w).image (Units.continuous_val.matrix_elem i j)
  have hQ' : ∀ i j w, IsCompact (Q' i j w) := fun i j w =>
    (hD w).image (Units.continuous_coe_inv.matrix_elem i j)
  have hQK : ∀ i j, ∀ᶠ w in cofinite, Q i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL (hw hg) i j
  have hQK' : ∀ i j, ∀ᶠ w in cofinite, Q' i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL w (n := n)).inv_mem (hw hg)) i j
  let P : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q i j w}
  let P' : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q' i j w}
  have hP : IsCompact P := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q i j) (hQ i j) (hQK i j)
  have hP' : IsCompact P' := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q' i j) (hQ' i j) (hQK' i j)
  have hC : IsClosed {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun w => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact (hD w).isClosed.preimage (continuous_mapLoc w)
  refine IsCompact.of_isClosed_subset (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hP.prod (hP'.image MulOpposite.continuous_op))) hC ?_
  intro g hg
  refine ⟨fun i _ j _ w => ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, rfl⟩, ⟨(g⁻¹ : GL (Fin n) (Af E)).val, fun i _ j _ w => ?_, rfl⟩⟩
  refine ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, ?_⟩
  show ((GeneralLinearGroup.map (pLoc E w) g)⁻¹ : GL (Fin n) (w.adicCompletion E)).val i j = _
  rw [← map_inv]
  rfl

end GlobalTheory.BCT.LocCpt

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries' {K : Type} [Field K] (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_or_conj_mem {S : Set (Pl E)} (hS : IsSection S) (w : Pl E) :
    w ∈ S ∨ conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S := by
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases hw : IsSplitAt w
  · rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
    · exact Or.inl huS
    · exact Or.inr huS
  · left
    by_contra hwS
    exact hw ⟨u, fun h => hwS (h ▸ huS), hu⟩

theorem cLoc_eq_invT (x : UA E n) (w : Pl E) :
    cLoc w x = invT n _ (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)) := by
  set Y := GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)
  have h : (Y.val)ᵀ * (cLoc w x).val = 1 := GlobalTheory.SplitPts.comp_eq x w
  apply Units.ext
  show (cLoc w x).val = ((Y⁻¹).val)ᵀ
  calc (cLoc w x).val = ((Y⁻¹).val)ᵀ * ((Y.val)ᵀ * (cLoc w x).val) := by
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
    _ = ((Y⁻¹).val)ᵀ := by rw [h, Matrix.mul_one]

end GlobalTheory.BCT.LocCpt


open GlobalTheory.BCT.LocCpt in
theorem GlobalTheory.BCT.LocCpt.loc_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E),
    IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) →
    IsCompact {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  intro E _ _ _ hU n S hS C hC hCK
  set c := GlobalTheory.SplitPts.conjE E
  let φ : ∀ w : Pl E, GL (Fin n) ((conjSrc c w).adicCompletion E) → GL (Fin n) (w.adicCompletion E) :=
    fun w g => invT n _ (GeneralLinearGroup.map (conjLoc c w) g)
  have hφ : ∀ w, Continuous (φ w) := fun w => (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec c w).1))
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w ∈ S then Subtype.val '' C w else φ w '' (Subtype.val '' C (conjSrc c w))
  have hD : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ S
    · simp only [D, if_pos hw]; exact (hC w).image continuous_subtype_val
    · simp only [D, if_neg hw]; exact ((hC _).image continuous_subtype_val).image (hφ w)
  have hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w (n := n) := by
    have h1 : ∀ᶠ w in cofinite, C (conjSrc c w) = KL n (conjSrc c w) :=
      (conjSrc_injective c).tendsto_cofinite.eventually hCK
    filter_upwards [hCK, h1] with w hw hw'
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS, hw]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hk
    · simp only [D, if_neg hwS, hw']
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hk' : (k : GL (Fin n) _) ∈ GlobalTheory.LFun.KGL (conjSrc c w) (n := n) := Subgroup.mem_subgroupOf.1 hk
      have hO : ∀ y, y ∈ ((conjSrc c w).adicCompletionIntegers E : Set _) →
          conjLoc c w y ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := fun y hy => by
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec c w).2.2 y]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
      apply mem_GLint_of_entries'
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL _ (n := n)).inv_mem hk') b a)
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL hk' b a)
  have hB := isCompact_box D hD hDK

  have hmem : ∀ (x : finU (E := E) (n := n)) (w : Pl E), toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w ↔
      cLoc w (x : UA E n) ∈ Subtype.val '' C w := by
    intro x w
    have hx := GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (x : UA E n)
    rw [toSub, dite_eq_left hx]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨k, hk, e⟩
      have : k = ⟨_, hx⟩ := Subtype.ext e
      rwa [← this]
  have hclosed : IsClosed {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
    simp only [hmem, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact ((hC w).image continuous_subtype_val).isClosed.preimage
      ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)

  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine IsCompact.of_isClosed_subset (hι.isCompact_preimage (hB.image GlobalTheory.DefU.LocAdm.continuous_finGL)) hclosed ?_
  intro x hx
  refine ⟨GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n), fun w => ?_, ?_⟩
  · have e : ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n)) =
        cLoc u (x : UA E n) := fun u => Units.ext rfl
    rw [e]
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS]
      exact (hmem x w).1 (hx w hwS)
    · simp only [D, if_neg hwS]
      have hw' := (mem_or_conj_mem hS w).resolve_left hwS
      refine ⟨cLoc (conjSrc c w) (x : UA E n), (hmem x _).1 (hx _ hw'), ?_⟩
      exact (cLoc_eq_invT (x : UA E n) w).symm
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def MovesAt (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E)
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom) : Prop :=
  ∃ (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _),
    FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩) (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩))

def ReadsInv (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k)
    (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
    (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) : Prop :=
  ∀ w : lattice₂ D ((uAt r v i).X k).Λ,
    ∃ hw : Matrix.mulVec (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (w : Fin D.R.r → D.host.E) ∈
        lattice₂ D ((uAt r v i).X k').Λ,
      Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (lattice₂ D ((uAt r v i).X k').Λ))) ⟨_, hw⟩ =
        ψ k' (γ.symm ((ψ k).symm (Submodule.Quotient.mk w)))

theorem isTransp_of_movesAt {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} {i : Fin D.R.m}
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k}
    {γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l}
    {k k' : (uAt r v i).Comp} {a : GL (Fin D.R.r) D.host.E}
    (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a)
    (h₁ : ∀ x hx, MovesAt p r i v γ k k' a hm x hx) (h₂ : ReadsInv p r i v ψ γ k k' a) :
    IsTransp p r i v ψ γ k k' a :=
  ⟨hm, h₁, h₂⟩

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hlam Gm _ _ _ _ _ hH hS hSQ mu hmu hemb m _ θ0 h0e h0b h0o hns
  obtain ⟨θ, hθe, hθo⟩ := GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor l ι P.Nr F W.lam mu jK ϖ hF hJ hϖ Gm hH hemb m hns
  obtain ⟨θ', hθ'e, -, hc⟩ := _root_.GlobalTheory.ExpFrame.Conj.exists_eig_congr l ι P.Nr F mu hF θ θ0 m hθe hθo h0o
  have hB : BlockFor Ω inc P W mu :=
    _root_.GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr hCheb E Ω l ι inc P W F Bk hG mu θ' θ0 (fun τ => (hmu τ).1) hθ'e h0e h0b hc
  have hnt : Nontrivial Gm := IsSimpleModule.nontrivial (alg F.O P.Nr W.lam) Gm
  have hlnk := _root_.GlobalTheory.CapelliLink.linkage F.O P.Nr ι W.lam mu l ϖ (Fact.out) hϖ hϖl hlam (fun τ => (hmu τ).1) Gm hnt hSQ hemb
  exact hlink mu (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2, hlnk τ⟩) hB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem coefLat_le_span {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
    {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hC : GlobalTheory.Hk3.Core R F) (hFW : Nonempty (FWTie T R κw v₀))
    (hio : IoExt R) (i : Fin D.R.m) (hO : OMPins T R κw v₀ O i) (B : Base (Vc D i) (Wc D i)) (hB : B.Good)
    (hBo : BaseOf R i B) {Oc Oc' : Subring ℂ} (hc : IsCoefRing (embLL0 D) (labLL0 D) Oc)
    (hc' : IsCoefRing (embLL0 D) (labLL0 D) Oc') (h : Bridge.Gf (Vc D i)) {P : PolF D (Wc D i).rank (Vc D i).rank}
    (hP : P ∈ B.coefLat (embLL0 D) (labLL0 D) Oc h) :
    P ∈ Submodule.span Oc (B.coefLat (embLL0 D) (labLL0 D) Oc' h : Set (PolF D (Wc D i).rank (Vc D i).rank)) := by
  obtain ⟨c, hcE, -, -⟩ := GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κw v₀ hC hFW i Unit _ (O i) hO.2
  obtain ⟨u, w₀, hu, -, -⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  obtain ⟨κ, -, -, -, hL⟩ := GlobalTheory.CoefLatConj.coefLat_conj D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hcE u hu B hB hBo
  have e1 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc hc).1 h
  have e2 := (hL ↥D.LL0 (embLL0 D) (labLL0 D) Oc' hc').1 h
  rw [e1] at hP
  refine Submodule.span_mono ?_ hP
  intro Q hQ
  rw [SetLike.mem_coe, e2]
  exact Submodule.subset_span hQ

theorem baseOf_of_realPin_at {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

theorem smallInt_isCoefRing (D : D7) : IsCoefRing (embLL0 D) (labLL0 D) (smallInt D) :=
  ⟨embLL0_labLL0, fun a => ⟨a, rfl⟩⟩

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionEquivariantAtFrameConstantsOfClauses
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameConstMoveCore

open GlobalTheory.FrameConstMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem om_lift_vac_core {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (hV : VStd D i) (H : Geo.Tor.Host D.host.E)
    {mu : GA D (Wc D i) → ℂ} (hmu : MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) mu) {g : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    R.ωP i A.μ0 (1, k) (R.vacP i) = mu k • R.vacP i := by
  obtain ⟨hP, hV0, -, -, sV, sW, -⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i A.μ0 hV
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = R.mu0 ((i : ℕ) + 1) := MonoidHom.ext fun x => by
    show R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = _
    rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x, mul_one]
  have hl : Formalism.L2.Pj.latHat (Wc D i) = GlobalTheory.AdLat.hat D.host.F (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC (hR.lev.βW i)]
    exact (GlobalTheory.Member.latHat_eq_hat_and_gram D _).1
  have mv : ∀ {g k}, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g k → ∀ u, u ∈ _ → actO (Vc D i) (Wc D i) 1 k u ∈ _ :=
    fun hk => GlobalTheory.MovedLat.actO_mem (Vc D i) (Wc D i) 1 _ (R.ΛV i) (R.ΛV i) (R.ΛW i) (R.ΛW i)
      (fun z hz => by rw [map_one, Units.val_one, Matrix.one_mulVec]; exact hz)
      (fun z hz => by rw [← hl] at hz ⊢; exact GlobalTheory.DictMove.mulVec_mem_latHat (hR.lev.βW i) hk hz)
  refine _root_.GlobalTheory.VacStab.om_vacuum_eq_smul D _ _ _ _ _ _ _ hP mu (hχ ▸ hmu) H _ _ hV0 sV sW _
    (GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i (sg0 D A))) _ (hR.thP.vP i A.μ0).1 k hk.1 fun u => ⟨mv hk u, fun hu => ?_⟩
  have h := mv (GlobalTheory.ProjComm.isLift_inv hk) _ hu
  rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc] at h
  unfold Formalism.L2.Theta.mt at h
  rwa [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at h


set_option maxHeartbeats 1000000 in
theorem equivAt_of_ccIs_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, O.EquivAt (κ i) (u • cc) := by
  intro _ D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht i Tp tup O hO cc hcc u g k hk f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  have hact := hO.act.1
  refine ⟨GlobalTheory.GeoLevel.actLev_mem_cuspA h.toLawsM hj hact (κ i) g hf, fun p => ?_⟩
  have hσ : GoodEmb T.Q.c O.s0 := T.good_σ₀
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj _ hσ
  obtain ⟨hr, g₀, e, F₀, ik, φ, th, -, -, hth, hL⟩ := h.adPin _ hj _ hσ
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hU := h.unf _ hj _ hσ
  have hpq := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  have hmod := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR ht i O.s0 rfl
  have hn : (κ i).n = (Vc D i).rank := (hmod (O.dict p).1).2.2.2.2.2.2.2.2.2.2.2.1
  have hmu : MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) O.mu := by
    rw [← chiTie_of_chiR T R ht.alg h.pins.2.2.1 ht.chiR i]
    exact muVal_cast O.hV (h.muVal _ hj _ hσ)
  have hmul : ∀ a b, O.mu (a * b) = O.mu a * O.mu b := GlobalTheory.GeoLevel.castDict_mu_mul (h.muUnit _ hj _ hσ).1 O.hV
  have hag := GlobalTheory.LiftAgrees.levAgrees_of_isLift R i hR.lev _ (iotaW T i) (Mfr T.Q.l) O.lev
    (GlobalTheory.LevelAction.latEmb_iotaW T h i) (h.pins.2.1.1 ▸ hO.lift.lev) g k hk
  have hs : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (Vc D i).rank := hn ▸ ((mem_cusp _ _ _ _ _ _).1 hf).1
  have key := value_move O.hV hr (rank_Wc i) (T.iota _) hσ hU hpq hA (fun c => (hmod c).1) hL hth hd.2.2.2.1
    (h.muUnit _ hj _ hσ).2.2.2 (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hO.lift.std).1
    (hR.thP.vP i A.μ0).1.2.theta hmul (fun a => norm_ne_zero_iff.1 ((hmu.norm a).trans_ne one_ne_zero)) hcc
    (s := O.lev g) (s' := LinearMap.id) (κ := k)
    ⟨hk.1, GlobalTheory.DictMove.latGHat_eq (hR.lev.βW i) hk, fun a ha => by
      obtain ⟨w, hw, ew⟩ := hag a ha
      refine ⟨-w, neg_mem hw, ?_⟩
      rw [h.pins.2.1.1]
      exact eq_add_nsmul_neg ew⟩
    (om_lift_vac_core hR i hO.lift.std T.Q.H hmu hk) (f' := actLev T.Q.c O.lev2 g f) hs (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hact.total g y
      exact ⟨ρ, ν, _, hν, hm, evalAt_actL hact (h.evalWD _ hj) frMap_trans_id g hs.1 y⟩) p
  have h1 := chi_mul_mu hR.lev i hmu hk
  change u * cc (O.dict p).1 * O.mu p * rdU (T.U ((i : ℕ) + 1) O.s0) _ (O.dict p).1 (O.dict p).2 =
    _ * (u * cc (O.dict (p * k)).1 * O.mu (p * k) * rdU (T.U ((i : ℕ) + 1) O.s0) f (O.dict (p * k)).1 (O.dict (p * k)).2)
  rw [hmul]
  linear_combination u * O.mu p * key - u * O.mu p * cc (O.dict (p * k)).1 *
    rdU (T.U ((i : ℕ) + 1) O.s0) f (O.dict (p * k)).1 (O.dict (p * k)).2 * h1

end GlobalTheory.FrameConstMoveCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinear
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SurjAtPlaceV

open GlobalTheory.LeviAtPlace

theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)), ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t g'
  have h := hTr.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨leviHom h t G.V.J hJ hTr.geo.hV.herm g', lift_sub_one_at v _, ?_⟩
  rw [leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]

end GlobalTheory.SurjAtPlaceV
end

