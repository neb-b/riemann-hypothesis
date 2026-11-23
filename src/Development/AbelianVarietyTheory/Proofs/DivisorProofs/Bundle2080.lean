module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsTrans

theorem exists_refactor {X X₁ X₂ A : Scheme.{0}} {L : LB X} {M : LB A} (hL : L.IsLB) (hM : M.IsLB)
    {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X} {φ₁ : A ⟶ X₁} {φ₂ : A ⟶ X₂} (e : φ₁ ≫ F₁ = φ₂ ≫ F₂)
    (w₂ : LB.Iso M ((L.pull F₂).pull φ₂)) (hw₂ : PGen w₂) :
    ∃ w₁ : LB.Iso M ((L.pull F₁).pull φ₁), PGen w₁ ∧
      (∀ (z : A) (J : PUnit → L.ι) (k : M.ι), F₁ (φ₁ z) ∈ L.U (J PUnit.unit) → z ∈ M.U k →
        gw w₁ (𝟙 A) z J k = gw w₂ (𝟙 A) z J k) ∧
      ∀ {Y Y₁ Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₁ : Y₁ ⟶ X₁} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₁ : Y₁ ⟶ Y} {h₂ : Y₂ ⟶ Y}
        {g₁ : B ⟶ Y₁} {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₁ : LB.Gen (LB.LinComb (L.pull F₁) (fun _ : PUnit => u₁) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₁ = g₁ ≫ u₁ → v ≫ φ₂ = g₂ ≫ u₂ → g₁ ≫ h₁ = g₂ ≫ h₂ →
        PMaps (L := L) (F := F₁) (idIso (L.pull F₁)) (fun _ : PUnit => u₁) (fun _ => u) (fun _ => 1) t₁ t h₁ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w₁ (fun _ : PUnit => v) (fun _ => u₁) (fun _ => 1) a t₁ g₁ := by
  have hL₁ : (L.pull F₁).IsLB := LB.isLB_pull hL _
  have hL₂ : (L.pull F₂).IsLB := LB.isLB_pull hL _
  have p₁ := (isGen_iff (L := L) (F := F₁) (idIso _)).1 (idIso_isGen hL₁)
  have p₂ := (isGen_iff (L := L) (F := F₂) (idIso _)).1 (idIso_isGen hL₂)
  obtain ⟨w, T₂⟩ := exists_comp hL₂ (idIso (L.pull F₂)) w₂ p₂ hw₂ hL hM
  have pw := T₂.pgen_comp hL₂ p₂ hw₂
  have a₂ : ∀ (z : A) (J : PUnit → L.ι) (k : M.ι), (φ₂ ≫ F₂) z ∈ L.U (J PUnit.unit) → z ∈ M.U k →
      gw w (𝟙 A) z (J PUnit.unit) k = gw w₂ (𝟙 A) z J k := fun z J k hj hk => by
    have hJ : (𝟙 A ≫ φ₂) z ∈ (L.pull F₂).U J := mem_pull.2 hj
    rw [T₂ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₂) (idIso (L.pull F₂)) (𝟙 A ≫ φ₂) z (J PUnit.unit) J = 1 := gm_self hL₂ _ z hJ
    rw [this, _root_.one_mul]
  have b₂ : ∀ {Y Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₂ : Y₂ ⟶ Y}
        {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₂ = g₂ ≫ u₂ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w (fun _ : PUnit => v) (fun _ => u) (fun _ => 1) a t (g₂ ≫ h₂) :=
    fun t t₂ a hc H H' => T₂.pmaps_comp hL₂ (fun _ => hc) H H'
  clear T₂
  generalize φ₂ ≫ F₂ = H at e w pw a₂ b₂
  subst e
  obtain ⟨w₁, T₁⟩ := exists_cancel hL (idIso (L.pull F₁)) w p₁ pw hL₁ hM
  refine ⟨w₁, T₁.pgen_cancel hL p₁ pw, fun z J k hj hk => ?_, ?_⟩
  · have hJ : (𝟙 A ≫ φ₁) z ∈ (L.pull F₁).U J := mem_pull.2 hj
    rw [← a₂ z J k hj hk, T₁ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₁) (idIso (L.pull F₁)) (𝟙 A ≫ φ₁) z (J PUnit.unit) J = 1 := gm_self hL₁ _ z hJ
    rw [this, _root_.one_mul]
  · intro Y Y₁ Y₂ B u u₁ u₂ v h₁ h₂ g₁ g₂ t t₁ t₂ a c₁ c₂ c H₁ H₂ H
    exact T₁.pmaps_cancel hL (fun _ => c₁) H₁ (c ▸ b₂ t t₂ a c₂ H₂ H)

theorem gs_locSec {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    {σ : (CechPic.tens L.L (δ.pull G.hom)).Sec} {i : δ.ι} {R : Type} [CommRing R] {ξ : Sp R ⟶ S}
    {t : (KeyVals.bL L ξ).L.Sec} (hξ : ⊤ ≤ ξ ⁻¹ᵁ δ.U i) (ht : KeyVals.IsLocSec σ i ξ t) {Z : Scheme.{0}}
    (q : Z ⟶ (KeyVals.bG G ξ).left) (z : Z) (J : (KeyVals.bL L ξ).L.ι) (hJ : q z ∈ (KeyVals.bL L ξ).L.U J) :
    gs q z _ (t.f J) = gs (q ≫ pullback.fst G.hom ξ) z _ (σ.f (J PUnit.unit, fun _ => i)) := by
  have hle : (KeyVals.bL L ξ).L.U J ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (J PUnit.unit, fun _ => i) := by
    intro p hp
    refine ⟨mem_pull.1 hp, mem_pull.2 ?_⟩
    have e := congrArg (fun g => g p) (pullback.condition (f := G.hom) (g := ξ))
    have h2 : ξ (pullback.snd G.hom ξ p) ∈ δ.U i := hξ (show pullback.snd G.hom ξ p ∈ (⊤ : (Sp R).Opens) from trivial)
    exact e.symm ▸ h2
  rw [ht J hle]
  exact gs_appLE _ _ _ hle q z hJ _

theorem pmaps_bL {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ S) : PMaps (L := L.L) (F := pullback.fst G.hom ξ) (idIso (L.L.pull (pullback.fst G.hom ξ))) (K := PUnit)
      (fun _ => eSec (KeyVals.bG G ξ)) (fun _ => eSec G) (fun _ => 1) (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) :=
  (maps_iff _ _ _ _ (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) (KeyVals.bL L ξ).rig
    (rigPull_le (G' := KeyVals.bG G ξ) (pullback.fst G.hom ξ) (KeyVals.eb ξ) (KeyVals.eSec_bG G ξ) L.L)
    (fun _ => rfl)).1 (idIso_maps (KeyVals.bL L ξ))

theorem keyOn_trans : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  intro S G _ _ g L δ σ i R R' K _ _ _ ξ r ξ' f t y t' y' x hg hξ hU ht ht' hy hK
  obtain ⟨φ', he', ψ', F', hφ', hψ', hrig', hsec', hF1, hF2, hFv⟩ := hK
  have hU' : ⊤ ≤ ξ' ⁻¹ᵁ δ.U i := by
    intro p _
    rw [← hξ]
    exact hU (show spMap r p ∈ (⊤ : (Sp R).Opens) from trivial)
  have hP := isGrpPullback_pullback G ξ
  have hP' := isGrpPullback_pullback G ξ'
  obtain ⟨m, hm, hfst, hsnd⟩ : ∃ m : (KeyVals.bG G ξ').left ⟶ (KeyVals.bG G ξ).left,
      IsGrpPullback (KeyVals.bG G ξ') (KeyVals.bG G ξ) (spMap r) m ∧ m ≫ pullback.fst G.hom ξ = pullback.fst G.hom ξ' ∧
        m ≫ (KeyVals.bG G ξ).hom = (KeyVals.bG G ξ').hom ≫ spMap r := by
    have sq : pullback.fst G.hom ξ' ≫ G.hom = (pullback.snd G.hom ξ' ≫ spMap r) ≫ ξ := by
      rw [Category.assoc, hξ]; exact pullback.condition
    refine ⟨pullback.lift _ _ sq, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, hξ]
    exact hP'
  have hφ : IsGrpPullback x.P.A (KeyVals.bG G ξ) (spMap (f.comp r)) (φ' ≫ m) := by
    rw [spMap_comp]
    exact IsGrpPullback.comp hφ' hm
  have he : eSec x.P.A ≫ φ' ≫ m = spMap (f.comp r) ≫ eSec (KeyVals.bG G ξ) := PolBaseChange.eSec_comm hφ
  have e : (φ' ≫ m) ≫ pullback.fst G.hom ξ = φ' ≫ pullback.fst G.hom ξ' := by rw [Category.assoc, hfst]
  obtain ⟨ψ, pψ, hgw, hmap⟩ := exists_refactor L.isLB x.P.isLB e ψ' ((isGen_iff ψ').1 hψ')
  have H' : PMaps ψ' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec (KeyVals.bG G ξ')) (fun _ => 1) x.rig
      (KeyVals.bL L ξ').rig (spMap f) :=
    (maps_iff ψ' _ _ _ x.rig (KeyVals.bL L ξ').rig (spMap f) _
      (rigPull_le (G' := x.P.A) φ' (spMap f) he' (KeyVals.bL L ξ').L) (fun _ => rfl)).1 hrig'
  have c : spMap (f.comp r) ≫ ξ = spMap f ≫ ξ' := by rw [spMap_comp, Category.assoc, hξ]
  have H := hmap L.rig (KeyVals.bL L ξ).rig (KeyVals.bL L ξ').rig x.rig he he' c (pmaps_bL L ξ) (pmaps_bL L ξ') H'
  have hD1 : ∀ a, Chart.dualMapR r (algebraMap R _ a) = algebraMap R' _ (r a) := fun a => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hD2 : Chart.dualMapR r DualNumber.eps = DualNumber.eps := by
    ext <;> simp [Chart.dualMapR]
  refine ⟨φ' ≫ m, he, ψ, F'.comp (Chart.dualMapR r), hφ, (isGen_iff ψ).2 pψ,
    (maps_iff ψ _ _ _ x.rig (KeyVals.bL L ξ).rig (spMap (f.comp r)) _
      (rigPull_le (G' := x.P.A) (φ' ≫ m) (spMap (f.comp r)) he (KeyVals.bL L ξ).L) (fun _ => rfl)).2 H,
    ?_, fun a => ?_, ?_, fun j => ?_⟩
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk ψ t x.th ?_
    intro z J k hJ hk
    have ha : ((φ' ≫ m) ≫ pullback.fst G.hom ξ) z ∈ L.L.U (J PUnit.unit) :=
      (mem_pull (F := pullback.fst G.hom ξ)).1 hJ
    have ha' : (φ' ≫ pullback.fst G.hom ξ') z ∈ L.L.U (J PUnit.unit) := e ▸ ha
    have hJ' : φ' z ∈ (KeyVals.bL L ξ').L.U J := (mem_pull (F := pullback.fst G.hom ξ')).2 ha'
    have hW : (𝟙 x.P.A.left) z ∈ ((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k := ⟨mem_pull.2 hJ', hk⟩
    have s2 : gs (𝟙 _ ≫ φ') z _ (t'.f J) = (gw ψ' (𝟙 _) z J k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e0 := congrArg (gs (𝟙 _) z (((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k))
        (hsec' (fun _ => J) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE φ' _ _ _ (𝟙 _) z hW _).symm.trans (e0.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := gs_locSec hU ht (𝟙 _ ≫ φ' ≫ m) z J hJ
    have e2 := gs_locSec hU' ht' (𝟙 _ ≫ φ') z J hJ'
    have e3 : (𝟙 _ ≫ φ' ≫ m) ≫ pullback.fst G.hom ξ = (𝟙 _ ≫ φ') ≫ pullback.fst G.hom ξ' := by
      rw [Category.id_comp, Category.id_comp, e]
    rw [e3] at e1
    exact e1.trans (e2.symm.trans (s2.trans (congrArg (fun u : _ˣ => u.val * _) (hgw z J k ha hk).symm)))
  · rw [RingHom.comp_apply, hD1, hF1]; rfl
  · rw [RingHom.comp_apply, hD2, hF2]
  · have hv : (y' (j.cast hg)).left ≫ m = spMap (Chart.dualMapR r) ≫ (y (j.cast hg)).left := by
      refine hP.1.hom_ext ?_ ?_
      · rw [Category.assoc, hfst, Category.assoc]
        exact hy _ hD1 hD2 _
      · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (y' _), Category.assoc, Over.w (y _)]
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact RingHom.ext fun a => (hD1 a).symm
    rw [← Category.assoc, hFv j, Category.assoc, hv, spMap_comp, Category.assoc]

end GlobalTheory.KeyValsTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FibreCrit

theorem exists_generization_mem {Y : Scheme.{0}} [IsLocallyNoetherian Y] {O : Set Y} (hO : IsOpen O)
    (hd : Dense O) (y : Y) : ∃ e0 : Y, e0 ⤳ y ∧ e0 ∈ O := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) trivial
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  obtain ⟨y', rfl⟩ : y ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hyU
  have hC := irreducibleComponent_mem_irreducibleComponents y'
  obtain ⟨o, ho, hne, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwO⟩ :=
    hd.inter_open_nonempty _ (U.ι.isOpenEmbedding.isOpenMap _ ho) (hne.image _)
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  exact ⟨U.ι hC.1.genericPoint, (hg.specializes mem_irreducibleComponent).map U.ι.continuous,
    ((hg.specializes (hoC hwo)).map U.ι.continuous).mem_open hO hwO⟩

theorem spMap_algebraMap_apply (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (p : Sp K) : spMap (algebraMap V K) p = (⊥ : PrimeSpectrum V) := by
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap V K) p.asIdeal = ⊥
  rw [(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)

end GlobalTheory.FibreCrit

namespace GlobalTheory.FibreCrit

theorem finite_fibre_of_isFinite : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  intro X Y₀ Y s t i hs hi hd hY hfin z
  refine (s.finite_preimage (hfin z)).subset ?_
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨e0, he0y, he0i⟩ := exists_generization_mem i.isOpenEmbedding.isOpen_range i.denseRange y
  obtain ⟨V, _, _, _, g, hg0, hg1⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V)
      (_ : IsDiscreteValuationRing V) (g : Sp V ⟶ Y),
      g (⊥ : PrimeSpectrum V) ∈ Set.range i ∧ g (IsLocalRing.closedPoint V) = y := by
    by_cases he : e0 = y
    · subst he
      have hpt : ∀ q, (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0) q = e0 := fun q => by
        have h := Set.mem_range_self (f := Y.fromSpecResidueField e0)
          (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) q)
        rw [Scheme.range_fromSpecResidueField] at h
        rw [Scheme.Hom.comp_apply]
        exact h
      exact ⟨PowerSeries (Y.residueField e0), inferInstance, inferInstance, inferInstance,
        spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0, (hpt _).symm ▸ he0i, hpt _⟩
    · obtain ⟨O, hO, hV, -, f, hf0, hf1⟩ :=
        GlobalTheory.exists_complete_discreteValuationRing_of_specializes he0y he
      exact ⟨O, inferInstance, hO, hV, f, hf0 ▸ he0i, hf1⟩
  have hr : Set.range (spMap (algebraMap V (FractionRing V)) ≫ g) ⊆ Set.range i := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, spMap_algebraMap_apply V (FractionRing V) q]
    exact hg0
  refine ⟨V, FractionRing V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g ≫ s, g ≫ t, IsOpenImmersion.lift i _ hr, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (· ≫ s) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (congrArg (· ≫ t) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (Scheme.Hom.comp_apply g s _).trans (congrArg s hg1)
  · exact ((Scheme.Hom.comp_apply g t _).trans (congrArg t hg1)).trans hy

end GlobalTheory.FibreCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFractionFieldOfFinitelyManyProportionalIma
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LevelFinite.finite_of_isAlgebraic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (K0 : Subfield Ω), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → (∀ a : o, algebraMap o Ω a ∈ K0) → Algebra.IsAlgebraic K0 Ω → Module.Finite K0 Ω := by
  intro o Ω _ _ _ R K0 hfg hfrac ho halg
  obtain ⟨s, hs⟩ := hfg
  have hL : FiniteDimensional K0 (IntermediateField.adjoin K0 (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hR : ∀ a ∈ R, a ∈ IntermediateField.adjoin K0 (s : Set Ω) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K0 _ hx
    | algebraMap r => exact IntermediateField.algebraMap_mem _ (⟨_, ho r⟩ : K0)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have htop : IntermediateField.adjoin K0 (s : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, ha, c, hc, rfl⟩ := hfrac z
    exact div_mem (hR a ha) (hR c hc)
  rw [htop] at hL
  exact (IntermediateField.topEquiv (F := K0) (E := Ω)).toLinearEquiv.finiteDimensional

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  first
  | rfl
  | simp [spMap, ← Spec.map_comp]
  | (simp only [spMap]; rw [← Spec.map_comp]; rfl)

private theorem pow_injective_of_transcendental {Ω : Type} [Field Ω] (K0 : Subfield Ω) (z : Ω) (hz : Transcendental K0 z) :
    Function.Injective (fun m : ℕ => z ^ m) := by
  have h0 : z ≠ 0 := fun h => hz (h ▸ isAlgebraic_zero)
  have h1 : ∀ k : ℕ, 0 < k → z ^ k ≠ 1 := by
    intro k hk hzk
    apply hz
    refine ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hk 1, ?_⟩
    simp [hzk]
  have key : ∀ m m' : ℕ, m < m' → z ^ m = z ^ m' → False := by
    intro m m' h hmm
    apply h1 (m' - m) (Nat.sub_pos_of_lt h)
    have : z ^ m * z ^ (m' - m) = z ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hmm]
    exact mul_left_cancel₀ (pow_ne_zero _ h0) this
  intro m m' hmm
  simp only at hmm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key m m' h hmm
  · exact key m' m h hmm.symm

theorem GlobalTheory.LevelFinite.finite_ratio_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (X : Scheme.{0}) (x : Sp R ⟶ X) (I : Type) [Finite I] (v : I → R), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ (K : Type) [Field K] [IsAlgClosed K] (c : I → K), Set.Finite {y : Sp K ⟶ X | ∃ σ : R →+* K, spMap σ ≫ x = y ∧ ∃ u : K, u ≠ 0 ∧ ∀ i, σ (v i) = u * c i}) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})) Ω := by
  intro o Ω _ _ _ R X x I _ v hfg hfrac hfin hpts
  refine GlobalTheory.LevelFinite.finite_of_isAlgebraic o Ω R _ hfg hfrac
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) ⟨fun z => ?_⟩
  by_contra hz
  obtain ⟨φ, hφ, hφeq⟩ := _root_.GlobalTheory.StalkField.exists_stalk_field_hom Ω X (spMap R.val.toRingHom ≫ x) hfin
  have hτ : ∀ m : ℕ, ∃ τ : Ω →ₐ[Subfield.closure (Set.range (algebraMap o Ω) ∪
      {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})] AlgebraicClosure Ω,
      τ z = algebraMap Ω (AlgebraicClosure Ω) z ^ (m + 1) :=
    fun m => _root_.GlobalTheory.exists_algHom_algebraicClosure_apply_eq_pow Ω _ z hz (m + 1) m.succ_pos
  choose τ hτ using hτ
  have hfib : ∀ y : Sp (AlgebraicClosure Ω) ⟶ X,
      Set.Finite {τ' : Ω →+* AlgebraicClosure Ω | spMap τ' ≫ spMap R.val.toRingHom ≫ x = y} := by
    intro y
    by_cases hne : ∃ τ0 : Ω →+* AlgebraicClosure Ω, spMap τ0 ≫ spMap R.val.toRingHom ≫ x = y
    · obtain ⟨τ0, hτ0⟩ := hne
      refine (_root_.GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite _ Ω _ φ (τ0.comp φ) hφ).subset ?_
      intro τ' hτ'
      exact hφeq _ τ' τ0 (hτ'.trans hτ0.symm)
    · apply Set.Finite.subset Set.finite_empty
      intro τ' hτ'
      exact (hne ⟨τ', hτ'⟩).elim
  have hS := hpts (AlgebraicClosure Ω) (fun i => algebraMap Ω (AlgebraicClosure Ω) (v i))
  have hinj : Function.Injective (fun m : ℕ => ((τ m : Ω →ₐ[_] AlgebraicClosure Ω) : Ω →+* AlgebraicClosure Ω)) := by
    intro m m' hmm
    have h1 : τ m z = τ m' z := by
      simpa using congrArg (fun f : Ω →+* AlgebraicClosure Ω => f z) hmm
    rw [hτ, hτ, ← map_pow, ← map_pow] at h1
    exact Nat.succ_injective (pow_injective_of_transcendental _ z hz ((algebraMap Ω (AlgebraicClosure Ω)).injective h1))
  apply Set.infinite_range_of_injective hinj
  refine (hS.biUnion (fun y _ => hfib y)).subset ?_
  rintro _ ⟨m, rfl⟩
  refine Set.mem_biUnion (x := spMap ((τ m : Ω →+* AlgebraicClosure Ω)) ≫ spMap R.val.toRingHom ≫ x) ?_ rfl
  refine ⟨((τ m : Ω →+* AlgebraicClosure Ω)).comp R.val.toRingHom, by rw [spMap_comp_moduli_spaces, Category.assoc], ?_⟩
  by_cases h : ∃ i, (v i : Ω) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    have hc0 : algebraMap Ω (AlgebraicClosure Ω) (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    have hτ0 : τ m (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    refine ⟨τ m (v i0) / algebraMap Ω (AlgebraicClosure Ω) (v i0), div_ne_zero hτ0 hc0, fun i => ?_⟩
    have hr : (v i : Ω) / (v i0 : Ω) ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪
        {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)}) := Subfield.subset_closure (Or.inr ⟨i, i0, rfl⟩)
    have hfix : τ m ((v i : Ω) / (v i0 : Ω)) = algebraMap Ω (AlgebraicClosure Ω) ((v i : Ω) / (v i0 : Ω)) := by
      have := (τ m).commutes ⟨_, hr⟩
      rw [IsScalarTower.algebraMap_apply _ Ω (AlgebraicClosure Ω)] at this
      exact this
    have key : τ m (v i) = τ m ((v i : Ω) / (v i0 : Ω)) * τ m (v i0) := by
      rw [← map_mul, div_mul_cancel₀ _ hi0]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, key, hfix, map_div₀]
    ring
  · push_neg at h
    refine ⟨1, one_ne_zero, fun i => ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, h i]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic

def ConstSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ m : Pic A.left, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∀ ψ : A ⟶ A, IsMonHom ψ → GlobalTheory.EffBound.Eff (m - t • pull ψ.left (cls L hL)) → ψ = 1

def CubeSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ (c : Pic A.left) (x y z : A ⟶ A),
      pull (x * y * z).left c + pull x.left c + pull y.left c + pull z.left c =
        pull (x * y).left c + pull (x * z).left c + pull (y * z).left c + pull (1 : A ⟶ A).left c

def FiniteOrderSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ σ : A ≅ A, IsMonHom σ.hom →
      pull σ.hom.left (cls L hL) = cls L hL → ∃ m : ℕ, m ≠ 0 ∧ (GlobalTheory.SerreField.iter σ m).hom = 𝟙 A

def SeparatedSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ q : ℕ, 2 ≤ q → ∀ u : A ⟶ A,
      (∀ k : ℕ, ∃ ψ : A ⟶ A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1

def SerreAmpleSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ N : ℕ, 3 ≤ N → (N : K) ≠ 0 →
      ∀ σ : A ≅ A, IsMonHom σ.hom → pull σ.hom.left (cls L hL) = cls L hL →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A), x ^ N = 1 → x ≫ σ.hom = x) →
      σ.hom = 𝟙 A


end GlobalTheory.AmpleRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKaehlerResidueField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SmoothStalk

theorem finrank_baseChange_kaehler_of_formallyEtale {k B A K : Type} [Field k] [CommRing B] [CommRing A] [Field K]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra A K] [Algebra B K]
    [IsScalarTower B A K] [Algebra.FormallyEtale B A] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] [Nontrivial A] :
    Module.finrank K (K ⊗[B] Ω[B⁄k]) = Module.finrank A Ω[A⁄k] := by
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k B A
  have hbc2 := TensorProduct.isBaseChange A Ω[A⁄k] K
  have hcomp := hbc.comp hbc2
  rw [hcomp.equiv.finrank_eq, Module.finrank_baseChange]

theorem finrank_residue_kaehler : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsAffineOpen U → letI : Algebra k Γ(X, U) := (cstOn f U).toAlgebra; letI : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra; Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x)) (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]) = d := by
  intro k _ X f d _ U x hxU hU
  letI iB : Algebra k Γ(X, U) := (cstOn f U).toAlgebra
  letI iBK : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra
  letI iBA : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI iA : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  obtain ⟨-, hfree, hfin, hrank⟩ := GlobalTheory.SmoothStalk.smooth_stalk k X f d ⟨U, hU⟩ x hxU
  haveI : Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := hfree
  haveI : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := hfin
  have hrank' : Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = d := hrank
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI hsc : @IsScalarTower Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _
      iBK.toSMul := IsScalarTower.of_algebraMap_eq' rfl
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  rw [← hrank']
  exact @finrank_baseChange_kaehler_of_formallyEtale k Γ(X, U) (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _ _ _ iB iA iBA _ _ iBK hsc _ _ _ _

end GlobalTheory.SmoothStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.PullAlong

theorem idlAlong_comap_eq : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X) (J : X.IdealSheafData) {R : Type} [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ Y), idlAlong (J.comap π) ξ = idlAlong J (ξ ≫ π) := by
  intro X Y π J R _ _ ξ
  unfold idlAlong
  rw [GlobalTheory.VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

end GlobalTheory.PullAlong
end
end

