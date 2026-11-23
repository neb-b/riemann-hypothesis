module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataIntertwinesFiniteGroupStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsLift_extendedData_intertwines_finiteGroup : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ (g : Gc B w.px) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).r (e g) (L f) = L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).r g f)) := by
  exact GlobalTheory.Mem.R3.DefLatBC.act_ext
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffsCorrespondFieldEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.GoodIdemBC

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : Function.Injective (Formalism.UG.bc (n := n) ψ) := by
  intro x y h
  apply Units.ext
  have h' := congrArg Units.val h
  ext i j
  exact hψ (congrFun (congrFun h' i) j)

theorem eq_of_bc_heq {E : Type} [Field E] [NumberField E] {q r : ℕ} {P1 P2 : Pl E} (h : P1 = P2)
    (ψ1 : ZMod q ≃+* kP P1) (ψ2 : ZMod q ≃+* kP P2) (x y : GL (Fin r) (ZMod q))
    (hxy : HEq (Formalism.UG.bc (ψ1 : ZMod q →+* kP P1) x) (Formalism.UG.bc (ψ2 : ZMod q →+* kP P2) y)) : x = y := by
  subst h
  have e : (ψ1 : ZMod q →+* kP P1) = ψ2 := Subsingleton.elim _ _
  rw [e] at hxy
  exact bc_injective _ ψ2.injective (eq_of_heq hxy)

theorem eG_app_heq {E1 E2 : Type} [Field E1] [Field E2] [NumberField E2] {r : ℕ} {S S' : Finset (HeightOneSpectrum (𝓞 E1))}
    {Pg Pg' : Finset (Pl E2)} (hS : S' = S) (hPg : Pg' = Pg) (eG : Formalism.L2.Col.G0 E1 S r ≃* G0 Pg r)
    (eG' : Formalism.L2.Col.G0 E1 S' r ≃* G0 Pg' r) (he : HEq eG' eG) (g : Formalism.L2.Col.G0 E1 S r) (g' : Formalism.L2.Col.G0 E1 S' r)
    (hg : HEq g' g) (p : Pg) (p' : Pg') (hp : (p' : Pl E2) = p) : HEq (eG' g' p') (eG g p) := by
  subst hS hPg
  cases he
  cases hg
  rw [Subtype.ext hp]


set_option maxHeartbeats 1000000 in
theorem idemOf_coeff_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (idemOf z'.Xg).coeff g' = φ ((idemOf z.Xg).coeff g)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all ?_
  intro K B' f' T' w' hO hFo hP' B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ g g' hg
  have k1 := z.good.2 g
  have k2 := z'.good.2 g'
  obtain ⟨plg, iso, hplg, -, -, hiso⟩ := z.pins.keep.grp
  obtain ⟨plg', iso', hplg', -, -, hiso'⟩ := z'.pins.keep.grp
  apply (w'.st Z').B.embLL.injective
  refine k2.trans (Eq.trans ?_ ((hφ _).trans k1).symm)
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  obtain ⟨h1, -⟩ := hE
  dsimp only at h1
  subst h1
  cases hf
  have hp := eq_of_heq hpx
  have hPg := eq_of_heq hEx.Pg
  have key : (z'.R.eG.trans z'.cG) g' = grpEquiv Z.N.naut Z'.N.naut ((z.R.eG.trans z.cG) g) := by
    funext kv'
    obtain ⟨k, v'⟩ := kv'
    obtain ⟨v, rfl⟩ := (plEquiv Z.N.naut Z'.N.naut k).surjective v'
    refine Eq.trans ?_ (grpEquiv_apply' _ _ _ k v).symm
    have hpl : (plg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
      rw [hplg' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩, hplg ⟨k, v⟩]
      exact TypesTrue.plGw_plEquiv hG hG' k v
    refine eq_of_bc_heq hpl (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) (iso ⟨k, v⟩) _ _ ?_
    refine (heq_of_eq (hiso' g' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)).symm.trans
      ((eG_app_heq ?_ hPg _ _ hEx.eG g g' hg _ _ hpl).trans (heq_of_eq (hiso g ⟨k, v⟩)))
    exact hp ▸ rfl
  rw [key]
  exact TypesTrue.typeIdempotent_coeff_across_layers hG hG' _

end GlobalTheory.Mem.R3.GoodIdemBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Branches

variable {X X' : Scheme.{0}}

def pre (π : X' ⟶ X) (Z : Closeds X) : Closeds X' := Z.preimage π.continuous

abbrev van (Z : Closeds X) (x : X) : Ideal (X.presheaf.stalk x) :=
  FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x

def tr {x y : X} (h : x = y) : X.presheaf.stalk x →+* X.presheaf.stalk y :=
  (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom

def IsRsp {A : Type} [CommRing A] [IsLocalRing A] {ι : Type} [Fintype ι] (f : ι → A) : Prop :=
  IsRegularLocalRing A ∧ Ideal.span (Set.range f) = maximalIdeal A ∧ (Fintype.card ι : WithBot ℕ∞) = ringKrullDim A

def BrAt (B : Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x) : Prop :=
  IsRsp f ∧ van B x = Ideal.span {∏ j, f (Sum.inl j)}

def ColAt (B : Closeds X) {ι : Type} (E : ι → Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x)
    (c : Fin m → ι) : Prop :=
  BrAt B x f ∧ ∀ i, van (E i) x = Ideal.span {∏ j ∈ Finset.univ.filter (fun j => c j = i), f (Sum.inl j)}

def IsStrict (B : Closeds X) {ι : Type} (E : ι → Closeds X) : Prop :=
  ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → ι), ColAt B E x f c ∧ Function.Injective c

end Branches

section Pairs

variable {K F : Type} [Field K] [Field F] {XK X X'K X' : Scheme.{0}}

end Pairs

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsCN (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ CharZero R

abbrev toBase {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp R)) :=
  Over.homMk (spMap φ) (Category.comp_id _)

end Sections

section Steps

def HomExtNormalSt : Prop :=
  ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
    ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f

def PullSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsCN R' → Function.Injective φ → IsLocalHom φ → P.TorsionIso →
    ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap φ)) (P' : PELUnif (maximalIdeal R') t')
      (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X), P'.TorsionIso ∧
      ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)

end Steps

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaFix

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] gtGroup

theorem sigma_fixes_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  intro R _ _ D hB F _ _ O φ hφ k hk σ hσ p
  have memO : ∀ x : O, σ (x : F) ∈ O := fun x => by
    have h1 : σ (x : F) - x ∈ O := (O.valuation_le_one_iff _).1 (hσ x x.2).le
    have := O.add_mem _ _ h1 x.2
    simpa using this
  let σO : O →+* O := (σ.toRingHom.comp O.subtype).codRestrict O.toSubring memO
  have hσO : ∀ x : O, ((σO x : O) : F) = σ x := fun _ => rfl
  have hσφ : σO.comp φ = φ := RingHom.ext fun r => Subtype.ext (by
    show σ ((φ r : O) : F) = (φ r : F)
    rw [hφ]; exact σ.commutes _)
  have hres : (IsLocalRing.residue O).comp σO = IsLocalRing.residue O := RingHom.ext fun x => by
    show IsLocalRing.residue O (σO x) = IsLocalRing.residue O x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply (ValuationSubring.valuation_lt_one_iff O _).2
    have : ((σO x - x : O) : F) = σ (x : F) - x := by push_cast; rfl
    rw [this]; exact hσ x x.2
  have hsub : σ.toRingHom.comp O.subtype = O.subtype.comp σO := rfl
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨b', hb'⟩ := exists_extend O φ ρ rfl p.g.b
  let σ' : Over.mk (spMap φ) ⟶ Over.mk (spMap φ) := Over.homMk (spMap σO) (by
    show spMap σO ≫ spMap φ = spMap φ
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσφ])
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  haveI := D.P.isAb.comm
  have hd : IsDominant (spMap O.subtype) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical O.subtype).2
      (by rw [(RingHom.injective_iff_ker_eq_bot O.subtype).1 Subtype.val_injective]; exact bot_le)
  have hpk : p.g.b ^ k = cP D _ p.y := by
    rw [← nsmul_b, qk_nsmul hB, iota_b]
  have hpow : b' ^ k = cP D _ p.y := by
    have e : ρ ≫ b' ^ k = ρ ≫ cP D _ p.y := by
      rw [comp_cP, ← hpk, ← hb']; exact map_pow (preHom ρ) _ _
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk (spMap φ)).left := (inferInstance : IsReduced (Sp O))
    exact ext_of_isDominant (spMap O.subtype) (congrArg CommaMorphism.left e)
  have hpow' : b' ^ k = (σ' ≫ b') ^ k := by
    have e2 : σ' ≫ b' ^ k = (σ' ≫ b') ^ k := map_pow (preHom σ') b' k
    rw [← e2, hpow, comp_cP]
  have hcl : spMap (IsLocalRing.residue O) ≫ b'.left = spMap (IsLocalRing.residue O) ≫ (σ' ≫ b').left := by
    rw [Over.comp_left, ← Category.assoc]
    congr 1
    show _ = spMap (IsLocalRing.residue O) ≫ spMap σO
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hres]
  have heq : b' = σ' ≫ b' := _root_.GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) D.P.A D.P.isAb.smooth O (spMap φ) k hk b' (σ' ≫ b') hpow'
    (IsLocalRing.ResidueField O) (IsLocalRing.residue O) inferInstance hcl
  rw [← hb', Over.comp_left]
  show spMap σ.toRingHom ≫ spMap O.subtype ≫ b'.left = spMap O.subtype ≫ b'.left
  conv_rhs => rw [heq]
  rw [← Category.assoc, Over.comp_left, ← Category.assoc]
  congr 1
  show spMap σ.toRingHom ≫ spMap O.subtype = spMap O.subtype ≫ spMap σO
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.InertiaFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HodgeDomain.ActionDeriv

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  have h : ∀ᶠ x in nhds x0, ∀ τ, (1 - (unflat x τ)ᴴ * unflat x τ).PosDef := by
    refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually _ (fun a b => ?_)
      (fun x => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
    fun_prop
  exact h

theorem diffOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s) :
    ContDiffOn ℂ 1 (fun z => (M z).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem diffOn_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s)
    (hd : ∀ z ∈ s, (M z).det ≠ 0) (a b : Fin n) : ContDiffOn ℂ 1 (fun z => (M z)⁻¹ a b) s := by
  have hadj : ContDiffOn ℂ 1 (fun z => (M z).adjugate a b) s := by
    simp only [adjugate_apply]
    refine diffOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (diffOn_det h) hd) hadj

theorem diffOn_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) :
    DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) := by
  refine differentiableOn_pi.2 fun x => ?_
  obtain ⟨τ, a, b⟩ := x
  refine ContDiffOn.differentiableOn (n := 1) ?_ one_ne_zero
  have hinv : ∀ k, ContDiffOn ℂ 1 (fun v => (kapQ (g τ) (unflat v τ))⁻¹ k b) (DomFlat ι p q) := by
    intro k
    refine diffOn_inv (s := DomFlat ι p q) (M := fun v => kapQ (g τ) (unflat v τ)) (fun i j => ?_) (fun v hv => (kapQ_isUnit (hg τ (Set.mem_univ _)) (hv τ)).ne_zero) k b
    simp only [kapQ, Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
    fun_prop
  simp only [flat, moebI, moeb, Matrix.mul_apply]
  refine ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ (hinv k)
  simp only [Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
  fun_prop

theorem hasDerivAt_affine {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin k) ℂ)
    (z ξ : Matrix (Fin n) (Fin k) ℂ) (a : Fin m) (b : Fin k) :
    HasDerivAt (fun t : ℂ => (A * (z + t • ξ) + B) a b) ((A * ξ) a b) 0 := by
  have e : (fun t : ℂ => (A * (z + t • ξ) + B) a b) = fun t => t * (A * ξ) a b + (A * z + B) a b := by
    funext t
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((A * ξ) a b)).add_const ((A * z + B) a b)

theorem fderiv_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ : Pt ι p q) :
    fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) =
      flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) := by
  have hz' : flat z ∈ DomFlat ι p q := hz
  have hn := isOpen_domFlat.mem_nhds hz'
  have hF := ((diffOn_moebI hg).differentiableAt hn).hasFDerivAt
  set D := fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) with hD
  have hc : HasDerivAt (fun t : ℂ => flat z + t • flat ξ) (flat ξ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (flat ξ)).const_add (flat z)
  have hW : HasDerivAt (fun t : ℂ => flat (moebI g (unflat (flat z + t • flat ξ)))) D 0 :=
    hF.comp_hasDerivAt_of_eq (0 : ℂ) hc (by simp)
  have hev : ∀ᶠ t : ℂ in nhds 0, flat z + t • flat ξ ∈ DomFlat ι p q :=
    hc.continuousAt.eventually_mem (by simpa using hn)
  funext x
  obtain ⟨τ, a, b⟩ := x
  have hgτ := hg τ (Set.mem_univ _)
  have key : unflat D τ * kapQ (g τ) (z τ) = jW (g τ) (z τ) * ξ τ := by
    rw [jW, Matrix.sub_mul, eq_sub_iff_add_eq, Matrix.mul_assoc]
    ext i j
    have h1 := hasDerivAt_affine (g τ).1.toBlocks₁₁ (g τ).1.toBlocks₁₂ (z τ) (ξ τ) i j
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_pi.1 hW (τ, i, k)).mul (hasDerivAt_affine (g τ).1.toBlocks₂₁ (g τ).1.toBlocks₂₂ (z τ) (ξ τ) k j)
    have h3 := h2.congr_of_eventuallyEq (f₁ := fun t : ℂ =>
      ((g τ).1.toBlocks₁₁ * (z τ + t • ξ τ) + (g τ).1.toBlocks₁₂) i j) (by
        filter_upwards [hev] with t ht
        have := moeb_mul_kapQ hgτ (ht τ)
        exact (congrFun (congrFun this i) j).symm)
    rw [h1.unique h3, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [zero_smul, add_zero]
    rfl
  have e : unflat D τ = tanAct (g τ) (z τ) (ξ τ) := by
    rw [tanAct, ← key, mul_nonsing_inv_cancel_right _ _ (kapQ_isUnit hgτ (hz τ))]
  exact congrFun (congrFun e a) b

theorem isOpen_and_fderiv_moebI : ∀ (ι : Type) [Fintype ι] (p q : ℕ), IsOpen (DomFlat ι p q) ∧ ∀ g ∈ UpqI ι p q, DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) ∧ ∀ z ∈ DomI ι p q, ∀ ξ : Pt ι p q, fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) = flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) :=
  fun _ _ _ _ => ⟨isOpen_domFlat, fun _ hg => ⟨diffOn_moebI hg, fun _ hz ξ => fderiv_moebI hg hz ξ⟩⟩

end GlobalTheory.HodgeDomain.ActionDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KapMoved
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo

namespace GlobalTheory.FWKapMove

theorem kap_moved : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (τ : (w'.st Z').toD7.what₂.Tau),
        (∀ k : Fin ((w'.st Z').toD7.R.sigW ((i : ℕ) + 1)).1, (κ' i).aP τ k = aPl (w'.st Z').toD7 i ((Wc (w'.st Z').toD7 i).sig (tauE (w'.st Z').toD7 τ)).1 τ k) ∧
        (∀ k : Fin ((w'.st Z').toD7.R.sigW ((i : ℕ) + 1)).2,
          (κ' i).aM τ k = aMi (w'.st Z').toD7 i ((Wc (w'.st Z').toD7 i).sig (tauE (w'.st Z').toD7 τ)).1 ((Wc (w'.st Z').toD7 i).sig (tauE (w'.st Z').toD7 τ)).2 τ k) ∧
        (κ' i).n = (w'.st Z').toD7.R.nV := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι κ' hκ' i τ
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  obtain ⟨h1, h2, h3⟩ := hκ' i i rfl
  have h1' := eq_of_heq h1
  have h2' := eq_of_heq h2
  obtain ⟨k1, k2, k3⟩ := z.geo.fw.kap i τ
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · rw [h1']; exact k1 k
  · rw [h2']; exact k2 k
  · rw [h3]; exact k3

end GlobalTheory.FWKapMove
end

