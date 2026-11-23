module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0480
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

noncomputable section

namespace GlobalTheory.ToricTorsionSec

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem appTop_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    (spMap f).appTop.hom (unitOn u).val = (unitOn (Units.map f.toMonoidHom u)).val := by
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem isPullF_torusPt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (τ : Multiplicative D.X →* Fˣ)
    (g : GtPt D (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    (hg : ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) (q : GtPtF D F) (hq : GlobalTheory.UT.IsTor τ q) :
    GtPt.IsPullF F (𝟙 _) g q := by
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · rw [hq.1, (hg 0).1, Category.id_comp, Hom.one_def, DegPre.zeroT, Over.comp_left, Over.comp_left]
    congr 1
    have e₁ := Over.w (toUnit (TF (R := R) F))
    have e₂ := Over.w (toUnit (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := R) F)).left, ← Category.comp_id (toUnit (Over.mk _)).left]
    exact e₁.trans ((spMap_comp _ _).symm.trans e₂.symm)
  · refine Units.ext ?_
    rw [hq.2 χ y J hJ, val_pull hJ, Category.id_comp, GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) _ hJ]
    exact gs_unit (𝟙 _) y ⊤ trivial (unitOn (τ (Multiplicative.ofAdd χ)))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) → ∀ k : ℕ, 1 ≤ k →
    ∃ s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G),
      (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
        a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A') (f : A →+* A')
        (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
        a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
        (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt P.D.toPre F k),
        a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
        GlobalTheory.FlatTors.IsImage P F k q (s F a τ h).left := by
  intro E _ _ _ H R _ _ _ t P _ hR k hk
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ :=
    GlobalTheory.WholeBaseFinitePart.exists_torsion_toG E H R hR t P k hk
  let u : ∀ (A : Type) [CommRing A] (_ : Multiplicative P.D.toPre.X →* Aˣ),
      P.D.toPre.X →+ Additive Γ(Sp A, ⊤)ˣ := fun A _ τ =>
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : ∀ (A : Type) [CommRing A] (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → k • u A τ = 0 := by
    intro A _ τ hτ
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  have ex : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ),
      ∃ g : GtPt P.D.toPre (Over.mk (spMap a)), ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ))) := by
    intro A _ a τ
    obtain ⟨g, hg⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := P.D.toPre) (T := Over.mk (spMap a)) (u A τ)
    exact ⟨g, hg⟩
  choose gT hgT using ex
  have ex₂ : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 →
      ∃! h : Over.mk (spMap a) ⟶ N, GtPt.IsPull h.left g₀ (gT A a τ) := by
    intro A _ a τ hτ
    obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k (u A τ) (hu A τ hτ) (T := Over.mk (spMap a))
      (g := gT A a τ) (hgT A a τ)
    exact hU _ _ ⟨g', h₁, h₂⟩
  choose hT hhT hTu using ex₂
  refine ⟨fun A _ a τ hτ => hT A a τ hτ ≫ x₀, fun A _ a τ hτ => ?_,
    fun A A' _ _ a a' f τ hτ τ' hτ' ha hτf => ?_, fun A A' _ _ a ha a' f t₀ m₀ τ hτ z ha' hz => ?_,
    fun F _ _ _ a τ hτ q ha hq hqt => ?_⟩
  · show (hT A a τ hτ ≫ x₀) ^ k = 1
    rw [← MonObj.comp_pow, htors, MonObj.comp_one]
  · subst ha
    let ρ : Over.mk (spMap (f.comp a)) ⟶ Over.mk (spMap a) := Over.homMk (spMap f) (spMap_comp a f).symm
    have hρ : GtPt.IsPull ρ.left (gT A a τ) (gT A' (f.comp a) τ') :=
      GlobalTheory.TorusTorsion.isPull_of_units ρ (hgT A a τ) (hgT A' _ τ') fun χ => by
        refine (appTop_unitOn f _).trans ?_
        congr 2
        exact Units.ext (hτf _).symm
    have e := hTu A' _ τ' hτ' (ρ ≫ hT A a τ hτ) (isPull_trans (hhT A a τ hτ) hρ)
    show (hT A' (f.comp a) τ' hτ' ≫ x₀).left = spMap f ≫ (hT A a τ hτ ≫ x₀).left
    rw [← e]
    rfl
  · subst ha'
    exact _root_.GlobalTheory.TorusTorsionPoint.eq_torus_of_classify E H R t P N g₀ x₀ hform A A' a ha f t₀ m₀ τ z hz (gT A' _ τ) (hgT A' _ τ) (hT A' _ τ hτ)
      (hhT A' _ τ hτ)
  · subst ha
    have hx : OverGen F N (hT F _ τ hτ).left := (Over.w (hT F _ τ hτ)).trans (spMap_comp _ _)
    have hp := isPullF_trans (hhT F _ τ hτ) (isPullF_torusPt τ (gT F _ τ) (hgT F _ τ) q.g hqt)
    rw [Category.id_comp] at hp
    exact GlobalTheory.WholeBaseFinitePart.generic E H R hR t P k hk N g₀ x₀ hfin htors hform F _ hx q hq hp

end GlobalTheory.ToricTorsionSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformNormalisedAdelicSeeds
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

theorem seeds_uniform_exists : ∀ (K : Ctx) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P) (F : IntermediateField ℚ ℂ),
    ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P,
      (∃ F₀, SeedW K P f F F₀ px Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  classical
  intro K P f F
  have key : ∀ c : (Fin 2 → 𝓞 P.host.E) × (P.Word → 𝓞 P.host.E), ∃ (S : Finset ℕ) (S₂ : Finset ℂ),
      (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ Y : PreX P, (Y.piG, Y.piT) = c → (∃ F₀, SeedW K P f F F₀ Y Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ Y (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
    intro c
    by_cases hc : ∃ (X : PreX P) (F₀ : IntermediateField ℚ ℂ), (X.piG, X.piT) = c ∧ SeedW K P f F F₀ X Set.univ ⊤
    · obtain ⟨X, F₀, hX, hs⟩ := hc
      obtain ⟨S, S₂, hS₂, hb⟩ := seedW_bound hs
      refine ⟨S, S₂, hS₂, fun Y hY _ => ⟨F₀, ?_⟩⟩
      have e := hX.trans hY.symm
      exact seedW hb (congrArg Prod.fst e) (congrArg Prod.snd e)
    · exact ⟨∅, ∅, by simp, fun Y hY ⟨F₀, hs⟩ => absurd ⟨Y, F₀, hY, hs⟩ hc⟩
  choose S S₂ hS₂ hS using key
  have hfin := finite_gens P
  refine ⟨hfin.toFinset.biUnion S, hfin.toFinset.biUnion S₂, ?_, fun Y hs => ?_⟩
  · intro z hz
    obtain ⟨c, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS₂ c z hz
  · have hm : (Y.piG, Y.piT) ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨Y, rfl⟩
    obtain ⟨F₀, h⟩ := hS _ Y rfl hs
    refine ⟨F₀, h.mono ?_ (IntermediateField.adjoin.mono _ _ _ ?_)⟩
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)

end GlobalTheory.Mem.R3.Rw.Resize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupActionCoordinatewiseFieldEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.RhoExt

open Formalism.IndefR.FWT GlobalTheory.Mem.R3.GoodBC

theorem rel_of_span {LL LL' : Type} [Field LL] [Field LL'] (φ : LL →+* LL') {n n' : ℕ} (hn : n = n')
    (S : Set (Fin n → LL)) (hS : Submodule.span LL S = ⊤)
    (ρ : (Fin n → LL) →ₗ[LL] (Fin n → LL)) (ρ' : (Fin n' → LL') →ₗ[LL'] (Fin n' → LL'))
    (h : ∀ s ∈ S, ∀ (x' : Fin n' → LL'), (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (s k)) →
      ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ s k))
    (x : Fin n → LL) (x' : Fin n' → LL') (hx : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → ρ' x' k' = φ (ρ x k) := by
  subst hn
  have hx' : x' = cw φ x := funext fun k => hx k k rfl
  subst hx'
  have key : ∀ y ∈ Submodule.span LL S, ρ' (cw φ y) = cw φ (ρ y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      funext k
      exact h s hs (cw φ s) (fun k k' hk => by rw [Fin.ext hk]; rfl) k k rfl
    | zero => rw [cw_zero, map_zero, map_zero, cw_zero]
    | add a b _ _ ha hb => rw [cw_add, map_add (f := _), ha, hb, map_add (f := _), cw_add]
    | smul c a _ ha => rw [cw_smul, LinearMap.map_smul, ha, LinearMap.map_smul, cw_smul]
  intro k k' hk
  rw [← Fin.ext hk]
  exact congrFun (key x (hS ▸ Submodule.mem_top)) k


set_option maxHeartbeats 4000000 in
theorem rho_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → ∀ (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL), (∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) → ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → (z'.R.toRealDat.FW j').ρ g' x' k' = φ ((z.R.toRealDat.FW j).ρ g x k)) := by
  intro _ _ _ _ _ _ _
  refine StepW.trans (StepW.and _root_.GlobalTheory.Mem.R3.CuspExt.cusp_ext GlobalTheory.T.levelActions_on_liftRules_extendedData) (StepW.of_all fun K B' f' T' w' _ _ H => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hV z' hFine' hx j j' hj φ hφ g g' hg x x' hxx'
  obtain ⟨hR, hmem, hsub⟩ := H.1 B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hV z' hFine' hx j j' hj
  have hact := H.2 B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hV z' hFine' hx j j' hj

  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P => P.R.m) hE.1
  have hn : z'.R.nW j' = z.R.nW j := nat_heq_app hm z.R.nW z'.R.nW hx.nW j j' hj

  obtain ⟨eG, heG⟩ := gc_iso (w.st Z).B (w'.st Z').B hE.1 w.px w'.px hpx

  have hF : ∀ f f', HEq f' f → ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' →
      ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) k' =
        φ (((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) k) :=
    fun f f' h k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hx.forms j j' hj f f' h k k' hk).trans (hφ _).symm)

  have hkeep : ActKeeps (κ := z'.geo.κ) z'.geo.O j' ↔ ActKeeps (κ := z.geo.κ) z.geo.O j := by
    constructor
    · intro hk g0 f0 hf0
      have hr : HEq (cast hR.symm f0) f0 := cast_heq _ _
      have h1 := hk (eG g0) (cast hR.symm f0) ((hmem _ _ hr).2 hf0)
      exact (hmem _ _ (hact g0 (eG g0) (heG g0) f0 _ hr)).1 h1
    · intro hk g0' f0' hf0'
      have hr : HEq f0' (cast hR f0') := (cast_heq _ _).symm
      have hg0 : HEq g0' (eG.symm g0') := by
        have := heG (eG.symm g0')
        rwa [MulEquiv.apply_symm_apply] at this
      have h1 := hk (eG.symm g0') (cast hR f0') ((hmem _ _ hr).1 hf0')
      exact (hmem _ _ (hact _ _ hg0 _ _ hr)).2 h1
  by_cases hk : ActKeeps (κ := z.geo.κ) z.geo.O j
  · have A := (z.geo.rhoGeo j).1 hk
    have A' := (z'.geo.rhoGeo j').1 (hkeep.2 hk)
    have hS : Submodule.span (w.st Z).toD7.what₂.LL ((z.R.FW j).WK : Set (Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL)) = ⊤ := by
      obtain ⟨m, b, hb, -, -, -, hsp⟩ := z.geo.fw.ks j
      exact top_unique (hsp ▸ Submodule.span_mono (Set.range_subset_iff.2 hb))
    refine rel_of_span φ hn.symm _ hS ((z.R.toRealDat.FW j).ρ g) ((z'.R.toRealDat.FW j').ρ g') ?_ x x' hxx'
    intro s hs y' hy' k k' hk'
    obtain ⟨f0, hf0⟩ : ∃ f0, f0 = (z.geo.fw.e j).symm ⟨s, hs⟩ := ⟨_, rfl⟩
    have hs0 : ((z.geo.fw.e j f0 : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = s := by
      rw [hf0, LinearEquiv.apply_symm_apply]
    have hr : HEq (cast hR.symm (f0 : z.core.R ((j : ℕ) + 1))) (f0 : z.core.R ((j : ℕ) + 1)) := cast_heq _ _
    obtain ⟨f0', hf0'⟩ : ∃ f0' : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n,
        (f0' : z'.core.R ((j' : ℕ) + 1)) = cast hR.symm (f0 : z.core.R ((j : ℕ) + 1)) :=
      ⟨⟨_, (hmem _ _ hr).2 f0.2⟩, rfl⟩
    have hff : HEq f0' f0 := hsub f0.1 f0'.1 f0.2 f0'.2 (hf0' ▸ hr)
    have hy : ((z'.geo.fw.e j' f0' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = y' := by
      funext k1'
      have e1 := hF f0 f0' hff (Fin.cast hn k1') k1' rfl
      rw [e1, hs0, hy' (Fin.cast hn k1') k1' rfl]
    obtain ⟨h1, e1⟩ := A g f0
    obtain ⟨h1', e1'⟩ := A' g' f0'
    have hh := hsub _ _ h1 h1' (hact g g' hg _ _ (hf0' ▸ hr))
    rw [← hy, ← e1', hF _ _ hh k k' hk', e1, hs0]
  · have e0 : (z.R.toRealDat.FW j).ρ g = 1 := (z.geo.rhoGeo j).2 hk g
    have e0' : (z'.R.toRealDat.FW j').ρ g' = 1 := (z'.geo.rhoGeo j').2 (fun h => hk (hkeep.1 h)) g'
    intro k k' hk'
    rw [e0, e0', Module.End.one_apply, Module.End.one_apply]
    exact hxx' k k' hk'

end GlobalTheory.Mem.R3.RhoExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsDataExtendedDataBaseChangeSameValuesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsData_extendedData_baseChange_sameValues : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)), ∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((b.lift ψ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.gsdbc_ext | exact GlobalTheory.Mem.R3.DefLatBC.gsdbc_ext | (intros; apply GlobalTheory.Mem.R3.DefLatBC.gsdbc_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataCarriesClassSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsLift_extendedData_carries_classSum : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f g : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms, ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.csum (L f : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Cl → ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.V) (L g) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.csum f g)) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.csum_ext | exact GlobalTheory.Mem.R3.DefLatBC.csum_ext | (intros; apply GlobalTheory.Mem.R3.DefLatBC.csum_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataDeterminedByValuesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsLift_extendedData_determined_by_values : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX
            (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T'
            {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX'
            (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (f
            : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX
            (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr :=
            B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts
            w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map
            (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px)
            B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr :=
            B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I
            T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f)
            : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel
            (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
            ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch
            w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL
            : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch
            w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res
            (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields)
            (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr
            := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts
            w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) +
            1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V)
            d).1)) → ∀ b : Formalism.L2.Col.GSDBC φ (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px)
            B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) +
            1)) (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)), (∀ (ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F
            (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun) (d
            : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d'
            : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((b.lift ψ
            : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)).EqFun) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel
            (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1
            ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch
            w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v
            | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL
            : B.fields.K →+* ℂ) (((ψ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch
            w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)
            : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X :=
            B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD
            (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)).V) d).1)) → ∀ f, (Formalism.L2.Col.GSD.res
            (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) +
            1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X :=
            B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j'
            : ℕ) + 1))).symm (L f) = b.lift ((Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr
            := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T
            Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch
            w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm
            f)) := by
  exact @GlobalTheory.DatExtForms.forms_lift_eq_of_values
end

