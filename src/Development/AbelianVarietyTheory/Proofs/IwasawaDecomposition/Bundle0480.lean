module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0463
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HeckeFieldSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteNonzeroIndexPlacesReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

variable {B : Base}

@[reducible] def preX {P : Pre} (X Y : PreX P) : PreX P := { X with a := Y.a, T_gt := Y.T_gt, a_gt := Y.a_gt, spread_le := Y.spread_le }

theorem preX_eq {P : Pre} {X Y : PreX P} (h : X.piG = Y.piG) (h' : X.piT = Y.piT) : preX X Y = Y := by
  cases X; cases Y; cases h; cases h'; rfl

@[reducible] def colIn {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) : ColIn B (preX X Y) :=
  @ColIn.mk B (preX X Y) I.C I.Ch I.sel I.S I.ι I.finι I.tup I.tup_inj I.mu0 I.muStar I.muStar' I.trueColumn_tuple_trivial_eq_one I.xi I.cst I.idx I.J


set_option maxHeartbeats 2000000 in
theorem laws {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) (l : TC.Laws I) : TC.Laws (colIn I Y) :=
  ⟨l.pr, l.ch, l.lev, l.per, l.ovr, l.atL, l.fmL, l.xi0, l.idx0, l.bij0, l.lat⟩

variable {f : Top.Fr B.toPre} {T : TwDat B}


set_option maxHeartbeats 4000000 in
@[reducible] def colW (w : ColW B f T) (Y : PreX B.toPre) : ColW B f T where
  px := preX w.px Y
  I := colIn w.I Y
  ok := ⟨w.ok.spaces, w.ok.ch_ok, w.ok.ch_tied, w.ok.weil, w.ok.pibar, w.ok.sel_ok, w.ok.T_mem, w.ok.g_mem, w.ok.ram_mem, w.ok.xi_reads,
    w.ok.xi_star, w.ok.xi_star', w.ok.sharp, w.ok.idx_ok, w.ok.amb_ok, w.ok.duStar⟩
  C_eq := w.C_eq
  S_eq := w.S_eq
  xi_range := w.xi_range
  pins := ⟨w.pins.iX, w.pins.cof⟩
  l := laws w.I Y w.l
  l0 := w.l0
  δ := w.δ
  exact := w.exact
  fld := w.fld
  val := w.val


set_option maxHeartbeats 4000000 in
@[reducible] def dat (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    R3.Dat (w.st Z) (colIn w.I Y) hX T Wt :=
  @R3.Dat.mk (w.st Z) (preX w.px Y) (colIn w.I Y) hX T Wt z.Xg z.tr z.core z.alg z.alg_eq z.R z.cG z.geo z.pins
    ⟨z.lev.is, z.lev.C, z.lev.xiH, z.lev.Pg, z.lev.Q, z.lev.beta⟩ z.idG z.good z.mu z.fieldValues_mem_fixedField z.Ks_le


set_option maxHeartbeats 4000000 in
theorem pinned {K : Ctx} (w : ColW B f T) (Y : PreX B.toPre) (h : Pinned K B f T w) : Pinned K B f T (colW w Y) := by
  obtain ⟨p⟩ := h
  exact ⟨⟨p.isTw, p.jets, p.hX, p.above, p.half, p.d3b, p.selectedPlacesAgree, p.vals, p.roots⟩⟩


set_option maxHeartbeats 4000000 in
theorem grpAt (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (h : GrpAt (w.st Z) w.I) : GrpAt (w.st Z) (colIn w.I Y) :=
  ⟨h.pl, h.idem, h.cen⟩


set_option maxHeartbeats 4000000 in
theorem fine (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : Fine z) : Fine (w := colW w Y) (Z := Z) (dat w Y Z hX Wt z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.1 :))
  · exact (by with_unfolding_all exact (h.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.2 :))


set_option maxHeartbeats 4000000 in
theorem holdsL (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : HoldsL z.R z.F) : HoldsL (dat w Y Z hX Wt z).R (dat w Y Z hX Wt z).F := (by with_unfolding_all exact (h :))


set_option maxHeartbeats 4000000 in
theorem nonzeroIndexPlaces_adelicDataResized_eq (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) : (dat w Y Z hX Wt z).W1 (fun _ _ => 0) = z.W1 (fun _ _ => 0) := rfl


set_option maxHeartbeats 4000000 in
theorem seedW {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X Y : PreX P} {S : Set ℕ}
    {L : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ X S L) (hG : X.piG = Y.piG) (hT : X.piT = Y.piT) : SeedW K P f F F₀ Y S L := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  subst a1
  have e : w₀.px = X := eq_of_heq a5
  subst e
  refine ⟨B₀, f₀, T₀, colW w₀ Y, Z₀, hX₀, Wt₀, dat w₀ Y Z₀ hX₀ Wt₀ z₀, rfl, a2, a3, a4, heq_of_eq (preX_eq hG hT),
    pinned w₀ Y a6, a7, grpAt w₀ Y Z₀ a8, fine w₀ Y Z₀ hX₀ Wt₀ z₀ a9, holdsL w₀ Y Z₀ hX₀ Wt₀ z₀ a10, ?_, a12⟩
  intro v hv
  exact a11 v ((nonzeroIndexPlaces_adelicDataResized_eq w₀ Y Z₀ hX₀ Wt₀ z₀).le hv)

theorem finite_norm_eq {R : Ranks} (H : Formalism.BasicNotions.Host R) (n : ℕ) :
    {x : 𝓞 H.E | (x : H.E) * H.conj (x : H.E) = (n : H.E)}.Finite := by
  have hF := NumberField.Embeddings.finite_of_norm_le H.E ℂ (n + 1 : ℝ)
  refine (hF.preimage (f := fun x : 𝓞 H.E => (x : H.E)) RingOfIntegers.coe_injective.injOn).subset ?_
  intro x hx
  refine ⟨x.isIntegral_coe, fun φ => ?_⟩
  have h1 : φ (H.conj (x : H.E)) = starRingEnd ℂ (φ (x : H.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
  have h2 := congrArg φ hx
  rw [map_mul, h1, map_natCast, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖φ (x : H.E)‖ ^ 2 = (n : ℝ) := by exact_mod_cast h2
  have h4 := norm_nonneg (φ (x : H.E))
  show ‖φ (x : H.E)‖ ≤ (n + 1 : ℝ)
  nlinarith

theorem finite_gens (P : Pre) : (Set.range fun X : PreX P => (X.piG, X.piT)).Finite := by
  have h1 := Set.Finite.pi' fun i : Fin 2 => finite_norm_eq P.host (P.host.g i)
  have h2 := Set.Finite.pi' fun u : P.Word => finite_norm_eq P.host (P.T u)
  refine (h1.prod h2).subset ?_
  rintro _ ⟨X, rfl⟩
  exact ⟨fun i => X.piG_norm i, fun u => X.piT_norm u⟩

theorem exists_gens_LLC (B : Base) : ∃ S₂ : Finset ℂ, (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
    B.LLC ≤ IntermediateField.adjoin ℚ (S₂ : Set ℂ) := by
  classical
  let b := Module.finBasis ℚ B.LL
  refine ⟨Finset.univ.image fun i => B.embLL (b i), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom B.embLL.toRatAlgHom
  · intro z hz
    obtain ⟨x, rfl⟩ := B.mem_LLC.1 hz
    have e : B.embLL x = ∑ i, (b.repr x i) • B.embLL (b i) := by
      conv_lhs => rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact map_rat_smul B.embLL _ _
    rw [e]
    refine sum_mem fun i _ => IntermediateField.smul_mem _ (IntermediateField.subset_adjoin _ _ ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)


set_option maxHeartbeats 1000000 in
theorem finite_nonzeroIndexPlaces_referenceTuple (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (hH : HoldsL z.R z.F) : (z.W1 fun _ _ => 0).Finite := by
  have hok := hH.ok.ok2
  have hIw : ∀ j, {w' | (R3.s0Of z.R z.F).Iw j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.idx_finite_of_fg _ _ _ (hH.mLat j).fg
      (Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr).fg
  have hjw : ∀ j, {w' | Formalism.DivisionValues.jw (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0
      (R3.zsOf z.R z.F)).HT j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) w'
      (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (R3.zsOf z.R z.F)).Tl j
        (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.jw_finite_of_lat _ (Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr) _
      (Formalism.L2.DIV.BlockDat.Tl_full hok.conj (hok.lifts j _) hok.irr)
  have hF := Set.finite_iUnion fun j => (hIw j).union (hjw j)
  refine ((hF.preimage (w.st Z).toD7.plEq.injective.injOn).union
    ((hF.preimage GlobalTheory.Mem.NonzeroPlacesOverPrimes.conjPl_injective.injOn).preimage (w.st Z).toD7.plEq.injective.injOn)).subset ?_
  rintro v ⟨j, w', hw', h | h | h⟩
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
  · exact absurd rfl h

theorem seedW_bound {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X : PreX P}
    (h : SeedW K P f F F₀ X Set.univ ⊤) : ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
      SeedW K P f F F₀ X (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, -⟩ := h
  obtain ⟨S₂, hS₂, hL⟩ := exists_gens_LLC B₀
  have hfin := (finite_nonzeroIndexPlaces_referenceTuple w₀ Z₀ hX₀ Wt₀ z₀ a10).image B₀.places.resChar
  refine ⟨hfin.toFinset, S₂, hS₂, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => ?_, hL⟩
  rw [Set.Finite.coe_toFinset]
  exact ⟨v, hv, rfl⟩

end GlobalTheory.Mem.R3.Rw.Resize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValues
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
namespace GlobalTheory.Mem.R3.DefLatBC

theorem gsdbc_round_reidx (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    ∃ b : Formalism.L2.Col.GSDBC ι (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁)
      (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
        (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
          fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂),
      ∀ (ψ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun) d₁ d₂,
        HEq d₂ d₁ → HEq (MvPolynomial.map c₂ ((b.lift ψ).1 d₂).1) (MvPolynomial.map c₁ (ψ.1 d₁).1) := by
  subst hS
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  obtain ⟨F⟩ := Formalism.L2.Col.CoefFrame.nonempty ι
  refine ⟨Formalism.L2.Col.hfsFormBC ι F (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := _) => d.1.N)
    ((Formalism.L2.DIV.rhoVr (X.coefExt L ι).emb lam).comp (Formalism.L2.Col.ufGL X.E n)) (Formalism.L2.DIV.pairVr (X.coefExt L ι).emb lam 1)
    (fun d => Formalism.L2.DIV.nabAtr (X.coefExt L ι).emb lam d.1.N) (fun d => Formalism.L2.DIV.delAtr (X.coefExt L ι).emb lam d.1.N)
    (fun γ v => Formalism.L2.Col.hfs_rhoVr ι lam X.emb (Formalism.L2.Col.ufGL X.E n γ) v) Λ₁, fun ψ d₁ d₂ hd => ?_⟩
  obtain rfl : d₂ = d₁ := eq_of_heq hd
  have hc' : c₂.comp ι = c₁ := RingHom.ext hc
  exact heq_of_eq ((MvPolynomial.map_map ι c₂ _).trans (by rw [hc']; rfl))

end GlobalTheory.Mem.R3.DefLatBC

namespace GlobalTheory.Mem.R3.DefLatBC


set_option maxHeartbeats 4000000 in
theorem gsdbc_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)), ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((b.lift ψ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ => ?_
  generalize hk : (j : ℕ) + 1 = k
  generalize hk' : (j' : ℕ) + 1 = k'
  obtain rfl : k' = k := by rw [← hk, ← hk', hj]
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hv : (Base.primes (baseOfColW w') w'.px).vGs = (Base.primes (baseOfColW w) w.px).vGs := by
    rw [hpx']
    rfl
  have hφ' : ∀ x, (baseOfColW w').embLL (φ x) = (baseOfColW w).embLL x := hφ
  have hC : w'.I.C = w.I.C := w'.C_eq.trans ((eq_of_heq hf).trans w.C_eq.symm)
  refine gsdbc_round_reidx (baseOfColW w).fields φ (baseOfColW w').tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hφ
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hφ' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' _).trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w Wt).symm)
  · refine glue_inv_coefMap_of_empty φ (twistRamifiedPrimes_empty_colTuples w Wt) (twistRamifiedPrimes_empty_colTuples w' _) _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of φ p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    rw [hφ']
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    rw [hC] at e1
    exact e1.trans e2.symm

end GlobalTheory.Mem.R3.DefLatBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataCarriesClassSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem csum_res_symm {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (h : S.Ok)
    (f : (S.toCSD h).Forms) (c : S.Cl) :
    (((S.res h).symm f : S.EqFun) : S.D → S.V) (Quotient.out c) = (f.1 : S.Cl → S.V) c :=
  congrArg (fun u : (S.toCSD h).Forms => (u.1 : S.Cl → S.V) c) ((S.res h).apply_symm_apply f)

theorem csum_round_bc (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (hstar : ∀ x, ι (star x) = star (ι x))
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hH : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (Λ₂ ⟨w.1, hw⟩).H = (Λ₁ w).H)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x)
    (h₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).Ok)
    (h₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map c₁ (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hS
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  obtain ⟨H₂, l₂, rfl⟩ : ∃ (H₂ : ∀ w : ↥SG₂, Subgroup (GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))) (l₂ : ∀ w, ↥(H₂ w) →* Lˣ),
      Λ₂ = fun w => ⟨H₂ w, l₂ w⟩ := ⟨fun w => (Λ₂ w).H, fun w => (Λ₂ w).lam, rfl⟩
  have hH' : H₂ = fun w => (Λ₁ w).H := funext fun w => hH w w.2
  subst hH'
  have key : ∀ (p : Pol X.K X.Tau n) (q : Pol L X.Tau n), HEq (MvPolynomial.map c₂ q) (MvPolynomial.map c₁ p) →
      q = MvPolynomial.map ι p := by
    intro p q h
    apply MvPolynomial.map_injective c₂ c₂.injective
    rw [eq_of_heq h, MvPolynomial.map_map, show c₂.comp ι = c₁ from RingHom.ext hc]
  unfold CSD.csum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  have a1 := key _ _ (hf (Quotient.out c) (Quotient.out c) HEq.rfl)
  have a2 := key _ _ (hg (Quotient.out c) (Quotient.out c) HEq.rfl)
  have b1 := csum_res_symm _ h₁ f c
  have b2 := csum_res_symm _ h₁ g c
  have b3 := csum_res_symm _ h₂ f' c
  have b4 := csum_res_symm _ h₂ g' c
  have a1' : (f'.1 c).1 = MvPolynomial.map ι (f.1 c).1 :=
    (congrArg Subtype.val b3).symm.trans (a1.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b1))
  have a2' : (g'.1 c).1 = MvPolynomial.map ι (g.1 c).1 :=
    (congrArg Subtype.val b4).symm.trans (a2.trans (congrArg (fun v => MvPolynomial.map ι (Subtype.val v)) b2))
  have hp := (baseChangePairingV_holds X.E X.K L ι hstar X.Tau n X.emb lam 1 (f.1 c) (g.1 c) (f'.1 c) (g'.1 c) a1' a2').2
  exact congrArg₂ (· * ·) rfl hp

theorem glue_inv_H_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), (A₂ ⟨w.1, hw⟩).H = (A₁ w).H) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      ((A₂.glue B₂).inv ⟨w.1, hw⟩).H = ((A₁.glue B₁).inv w).H := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).H = ((A₁.glue B₁) w).H
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1]
  exact hA ⟨w.1, h1⟩ h2


set_option maxHeartbeats 1000000 in
theorem csum_refTuple {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂}
    (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl)
    (hpre : B₂.toPre = B₁.toPre) (hp : HEq w₂.px w₁.px) (j₁ j₂ : ℕ) (hj : j₁ = j₂)
    (ι : B₁.LL →+* B₂.LL) (hι : ∀ x, B₂.embLL (ι x) = B₁.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).Ok)
    (f g : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms) (f' g' : (Formalism.L2.Col.GSD.toCSD _ h₂).Forms)
    (hf : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm f').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm f).1 d₁).1))
    (hg : ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm g').1 d₂).1)
      (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm g).1 d₁).1)) :
    (Formalism.L2.Col.GSD.toCSD _ h₂).csum f'.1 g'.1 = ι ((Formalism.L2.Col.GSD.toCSD _ h₁).csum f.1 g.1) := by
  subst hj
  have hstar : ∀ x, ι (star x) = star (ι x) := by
    intro x
    apply B₂.embLL.injective
    rw [hι, B₂.starLL_cx, hι, B₁.starLL_cx]
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have hpx : w₂.px = w₁.px := eq_of_heq hp
  refine csum_round_bc (baseOfColW w₁).fields ι hstar (baseOfColW w₂).tauLL ?_ ((baseOfColW w₁).wts.lamV j₁) ?_
    (Formalism.L2.Col.mtTyKK w₁.I.Ch w₁.I.sel (mu0F (X := (baseOfColW w₁).fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).inv
    (Formalism.L2.Col.mtTyKK w₂.I.Ch w₂.I.sel (mu0F (X := (baseOfColW w₂).fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₁).inv
    ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι h₁ h₂ f g f' g' hf hg
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · refine (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans (Eq.trans ?_ (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
    rw [hpx]
    rfl
  · exact glue_inv_H_of_empty (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ fun w hw => rfl


set_option maxHeartbeats 1000000 in
theorem csum_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f g : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms, ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.csum (L f : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) (L g) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.csum f g)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ L _ hL a b => ?_
  exact csum_refTuple w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hp ((j : ℕ) + 1) ((j' : ℕ) + 1) (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
    a b (L a) (L b) (hL a) (hL b)

end GlobalTheory.Mem.R3.DefLatBC
end

