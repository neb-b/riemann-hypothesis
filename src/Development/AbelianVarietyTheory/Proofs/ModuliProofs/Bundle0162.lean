module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingOfPolarisationFormLinComb
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransitionFramesPushOpenImmersionImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem appIso_inv_topIso_inv {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ⟶ W.toScheme) (hv : v ≫ W.ι = W'.ι ≫ f) :
    (f.appIso W').inv ≫ Z.presheaf.map (homOfLE hle).op ≫ W.topIso.inv ≫ v.appTop = W'.topIso.inv := by
  have e : W.topIso.inv = W.ι.appLE W ⊤ (by simp) := (Scheme.Opens.ι_appLE W W ⊤ _).symm
  have e' : W'.topIso.inv = W'.ι.appLE W' ⊤ (by simp) := (Scheme.Opens.ι_appLE W' W' ⊤ _).symm
  have e₂ : v.appTop = v.appLE ⊤ ⊤ (le_top (a := ⊤) |>.trans (Scheme.Hom.preimage_top v).ge) := (Scheme.Hom.appLE_eq_app v).symm
  rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom', e, e', e₂, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.map_appLE]
  simp only [hv]

theorem exists_iso_image {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (h : W = f ''ᵁ W') : ∃ v : W'.toScheme ≅ W.toScheme, v.hom ≫ W.ι = W'.ι ≫ f := by
  subst h
  exact ⟨f.isoImage W', Scheme.Hom.isoImage_hom_ι f W'⟩

theorem appTop_hom_inv {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(X, ⊤)) :
    v.hom.appTop.hom (v.inv.appTop.hom a) = a := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, v.hom_inv_id, Scheme.Hom.id_appTop]; rfl

theorem appTop_inv_hom {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(Y, ⊤)) :
    v.inv.appTop.hom (v.hom.appTop.hom a) = a := appTop_hom_inv v.symm a

theorem exists_transport {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hφ : IsPullback φ G'.hom G.hom f)
    (hw : LBIso L' (L.pull φ)) (N : ℕ) :
    ∃ e : ∀ {X' X : Scheme.{0}} (a' : X' ⟶ Z') (a : X ⟶ Z) (u : X' ≅ X), u.hom ≫ a = a' ≫ f →
      LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a')) → LB.Sec (Out.LPow G L (N : ℤ) (Over.mk a)),
    (∀ {X₁' X₂' X₁ X₂ : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₂' : X₂' ⟶ Z'} {a₁ : X₁ ⟶ Z} {a₂ : X₂ ⟶ Z}
      (u₁ : X₁' ≅ X₁) (u₂ : X₂' ≅ X₂) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f) (h₂ : u₂.hom ≫ a₂ = a₂' ≫ f)
      (k' : X₂' ⟶ X₁') (k : X₂ ⟶ X₁) (hk' : k' ≫ a₁' = a₂') (hk : k ≫ a₁ = a₂), k' ≫ u₁.hom = u₂.hom ≫ k →
      ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))) (c' : Fin n → Γ(X₂', ⊤))
        (c : Fin n → Γ(X₂, ⊤)), (∀ i, u₂.hom.appTop.hom (c i) = c' i) →
        ∀ s : LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₂')),
        Lin G' L' N (Over.homMk k' hk' : Over.mk a₂' ⟶ Over.mk a₁') b c' s →
          Lin G L N (Over.homMk k hk : Over.mk a₂ ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) c (e a₂' a₂ u₂ h₂ s)) ∧
    ∀ {X₁' X₁ Y : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₁ : X₁ ⟶ Z} (u₁ : X₁' ≅ X₁) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f)
      (χ : Y ⟶ X₁) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))),
      BasisAlong G' L' N (Over.homMk (χ ≫ u₁.inv) rfl : Over.mk ((χ ≫ u₁.inv) ≫ a₁') ⟶ Over.mk a₁') b →
        BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ a₁) ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) := by
  obtain ⟨e, he⟩ := _root_.GlobalTheory.SecMove.transport Z Z' G G' f φ L L' hL hL' hφ hw N
  refine ⟨fun a' a u h => e (Over.mk a') (Over.mk a) u h, ?_, ?_⟩
  · intro X₁' X₂' X₁ X₂ a₁' a₂' a₁ a₂ u₁ u₂ h₁ h₂ k' k hk' hk hc n b c' c hcc s H
    obtain rfl : c' = fun i => u₂.hom.appTop.hom (c i) := funext fun i => (hcc i).symm
    exact (he (Over.mk a₁') (Over.mk a₂') (Over.mk a₁) (Over.mk a₂) u₁ u₂ h₁ h₂ (Over.homMk k' hk') (Over.homMk k hk)
      hc n b c s).1 H
  · intro X₁' X₁ Y a₁' a₁ u₁ h₁ χ n b B σ
    have hc' : (Iso.refl Y).hom ≫ χ ≫ a₁ = ((χ ≫ u₁.inv) ≫ a₁') ≫ f := by
      simp [← h₁]
    have hk : (χ ≫ u₁.inv) ≫ u₁.hom = (Iso.refl Y).hom ≫ χ := by simp
    have hid : ∀ a : Γ(Y, ⊤), (Iso.refl Y).hom.appTop.hom a = a := fun a => by simp
    obtain ⟨σ', rfl⟩ := (e (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk (χ ≫ a₁)) (Iso.refl Y) hc').surjective σ
    refine (existsUnique_congr fun c => ?_).1 (B σ')
    refine Iff.trans ?_ (he (Over.mk a₁') (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk a₁)
      (Over.mk (χ ≫ a₁)) u₁ (Iso.refl Y) h₁ hc' (Over.homMk (χ ≫ u₁.inv) rfl) (Over.homMk χ rfl) hk n b c σ')
    exact iff_of_eq (congrArg (fun c => Lin G' L' N _ b c σ') (funext fun k => (hid (c k)).symm))

theorem unit_rel_push {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ≅ W.toScheme) (hv : v.hom ≫ W.ι = W'.ι ≫ f) {n : ℕ} (r s : ℤ)
    (g : Γ(Z', W')) (c : Γ(W'.toScheme, ⊤)ˣ) (M : GL (Fin n) Γ(W'.toScheme, ⊤))
    (hg : W'.topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) :
    W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g)) =
      (Units.map v.inv.appTop.hom.toMonoidHom c ^ r *
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) ^ s).val := by
  have E : v.hom.appTop.hom (W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g))) =
      W'.topIso.inv.hom g := congrArg (fun k => k.hom g) (appIso_inv_topIso_inv f W' W hle v.hom hv)
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) =
      Units.map v.inv.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det M) :=
    Units.ext (RingHom.map_det v.inv.appTop.hom M.val).symm
  rw [hd, ← map_zpow, ← map_zpow, ← map_mul]
  exact (appTop_inv_hom v _).symm.trans (congrArg v.inv.appTop.hom (E.trans hg))

theorem hasFrames_pushLB : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) [IsOpenImmersion f] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → f ⁻¹' abLocus G ⊆ abLocus G' → ∀ (N : ℕ) (A : LB Z') (n : ℕ) (r s : ℤ), HasFrames G' L' N A n r s → HasFrames G L N (pushLB f A) n r s := by
  intro Z Z' G G' f _ φ L L' hL hL' hφ hw hab N A n r s ⟨th, b, h₁, h₂⟩
  obtain ⟨e₁, he₁, hb₁⟩ := exists_transport hL hL' hφ hw 1
  obtain ⟨eN, heN, hbN⟩ := exists_transport hL hL' hφ hw N
  choose u hu using fun i : A.ι => exists_iso_image f (A.U i) (f ''ᵁ A.U i) rfl
  refine ⟨fun i => e₁ (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (th i),
    fun i k => eN (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (b i k), fun (i j : A.ι) => ?_,
    fun (i : A.ι) W _ _ _ hW (χ : Sp W ⟶ (f ''ᵁ A.U i).toScheme) hχ => ?_⟩
  · obtain ⟨c, M, ⟨t, ht, ht'⟩, hb, hg⟩ := h₁ i j
    obtain ⟨v, hv⟩ := exists_iso_image f (A.U i ⊓ A.U j) (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j)
      (le_antisymm (image_inf_le f _ _) (le_inf (f.image_mono inf_le_left) (f.image_mono inf_le_right)))
    have ki : Z'.homOfLE (inf_le_left : A.U i ⊓ A.U j ≤ A.U i) ≫ (u i).hom =
        v.hom ≫ Z.homOfLE (inf_le_left : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U i).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    have kj : Z'.homOfLE (inf_le_right : A.U i ⊓ A.U j ≤ A.U j) ≫ (u j).hom =
        v.hom ≫ Z.homOfLE (inf_le_right : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U j).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    refine ⟨Units.map v.inv.appTop.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map v.inv.appTop.hom M,
      ⟨e₁ (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩, fun k => ?_, ?_⟩
    · exact he₁ (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => th i) (fun _ => 1) (fun _ => 1)
        (fun _ => map_one _) t ht
    · exact he₁ (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj 1 (fun _ => th j) (fun _ => c.val)
        (fun _ => v.inv.appTop.hom c.val) (fun _ => appTop_hom_inv v _) t ht'
    · obtain ⟨t, ht, ht'⟩ := hb k
      refine ⟨eN (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩
      · exact heN (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => b i k) (fun _ => 1) (fun _ => 1)
          (fun _ => map_one _) t ht
      · exact heN (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj n (b j) (fun k' => M.val k k')
          (fun k' => v.inv.appTop.hom (M.val k k')) (fun _ => appTop_hom_inv v _) t ht'
    · exact unit_rel_push f (A.U i ⊓ A.U j) _ (image_inf_le f _ _) v hv r s _ c M hg
  · have hc : ((Out.jK W ≫ (χ ≫ (u i).inv) ≫ (A.U i).ι) ≫ f) = Out.jK W ≫ χ ≫ (f ''ᵁ A.U i).ι := by
      simp only [Category.assoc]; rw [← hu i, Iso.inv_hom_id_assoc]
    obtain ⟨B₁, BN⟩ := h₂ i W hW (χ ≫ (u i).inv) (by
      rintro _ ⟨x, rfl⟩
      refine hab (hχ ⟨x, ?_⟩)
      exact (congrArg (fun k => k x) hc).symm.trans (Scheme.Hom.comp_apply _ _ _))
    exact ⟨hb₁ (u i) (hu i) χ 1 (fun _ => th i) B₁, hbN (u i) (hu i) χ n (b i) BN⟩

end GlobalTheory.ModelSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfUnitBall
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GoodRedUnitBall

theorem finiteType_closure (s : Set ℂ) (hs : s.Finite) :
    (algebraMap ℤ (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) := Algebra.FiniteType.adjoin_of_finite hs
  rw [RingHom.finiteType_algebraMap]
  have e : (Algebra.adjoin ℤ s).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_int]; rfl
  refine Algebra.FiniteType.of_surjective (R := ℤ) (A := Algebra.adjoin ℤ s)
    (RingEquiv.subringCongr e).toRingHom.toIntAlgHom (RingEquiv.subringCongr e).surjective

theorem valuationRing_of_unitBall {V C : Type} [CommRing V] [NormedField C] [Algebra V C] (h : IsUnitBall V C) :
    ∃ _ : IsDomain V, ValuationRing V ∧ IsFractionRing V C := by
  have hd : IsDomain V := h.1.isDomain _
  refine ⟨hd, ?_⟩
  have key : ∀ x : C, IsLocalization.IsInteger V x ∨ IsLocalization.IsInteger V x⁻¹ := by
    intro x
    rcases le_total ‖x‖ 1 with hx | hx
    · exact Or.inl ((h.2 x).2 hx)
    · exact Or.inr ((h.2 x⁻¹).2 (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx))
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 h.1
  have hf : IsFractionRing V C := by
    refine IsFractionRing.of_field V C fun x => ?_
    rcases key x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, 1, by simp [ha]⟩
    · exact ⟨1, a, by simp [ha]⟩
  exact ⟨(ValuationRing.iff_isInteger_or_isInteger V C).2 key, hf⟩

theorem goodRedExt_unitBall : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), Raises B Y → ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra V C], IsUnitBall V C → Y.GoodRedExt V C := by
  intro hext E _ _ _ H D Xo n N T l₀ B l c O _ β Y hR V C _ _ _ _ hV b y hy ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, hab, _, _, h₁, h₂, _⟩
  obtain ⟨_, _, _⟩ := valuationRing_of_unitBall hV
  obtain ⟨b₀, r, ν, -, -, ⟨ab⟩⟩ := hR
  have hp : IsProper Y.s := projProper _ _ _ Y.proj
  have hp' : IsProper B.C.s := projProper _ _ _ B.C.proj
  have hE : ValuativeCriterion.Existence Y.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1
  obtain ⟨⟨q⟩⟩ := hE
    { R := V
      K := C
      i₁ := y ≫ Y.j
      i₂ := spMap b
      commSq := ⟨by rw [Category.assoc]; exact hy⟩ }
  obtain ⟨y', hs, hl⟩ : ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V C) ≫ y' = y ≫ Y.j :=
    ⟨q.l, q.fac_right, q.fac_left⟩
  obtain ⟨π, hπ⟩ : ∃ π : Y.X ⟶ B.C.X, π = ab.π := ⟨_, rfl⟩
  refine ⟨y', hs, hl, ?_⟩
  have hz : LocallyOfFiniteType (spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact finiteType_closure _ (Set.toFinite _)
  have hc : IsGrpPullback Y.t.G B.C.t.G π ab.mu.φ := hπ ▸ ab.mu.cart
  have h₃ := (h₂.comp Y.m.cart).comp hc
  have h₄ : IsGrpPullback A B.C.t.G (spMap (algebraMap V C) ≫ (y' ≫ π)) ((φ₂ ≫ Y.m.φ) ≫ ab.mu.φ) := by
    rw [← Category.assoc, hl]
    exact h₃
  have h₅ := _root_.GlobalTheory.range_subset_abLocus_of_goodReduction hext B.C.X (B.C.s ≫ spMap (algebraMap ℤ (RZ H (n * l₀.M) 1))) B.C.t.G V C (y' ≫ π) 𝒜 A φ₁ _
    inferInstance B.C.t.semi hab h₁ h₄
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne B.C.t.semi hc.1 _).1 (h₅ ⟨x, rfl⟩)

end GlobalTheory.GoodRedUnitBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingTorsionBasisSymplectic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormTorsion

theorem rel_prod {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hm : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) :
    ∀ (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ), (∀ i, R (y i) (c i)) →
      R (List.ofFn fun i => y i ^ a i).prod (∏ i, c i ^ a i) := by
  first
  | exact @_root_.GlobalTheory.RelationPowers.rel_prod_pow
  | exact _root_.GlobalTheory.RelationPowers.rel_prod_pow
  | (apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationPowers.rel_prod_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationPowers.rel_prod_pow ..)

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_linComb (hW : Out.WeilSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ) {n : ℕ}
    (y : Fin n → (Out.baseOver (Sp K) ⟶ P.A)) (z : Out.baseOver (Sp K) ⟶ P.A) (hz : z ^ k = 1)
    (e : Fin n → ℤ) (a : Fin n → ℕ) (h : ∀ i, Out.WeilIs P.A P.L k (y i) z (unitOn (ζ ^ e i))) :
    Out.WeilIs P.A P.L k (Out.linComb y a) z (unitOn (ζ ^ ∑ i, (a i : ℤ) * e i)) := by
  obtain ⟨hu, hm, -, -⟩ := hW (Sp K) P k (Out.baseOver (Sp K))
  have h1 : Out.WeilIs P.A P.L k 1 z 1 := by
    obtain ⟨c, hc, hc'⟩ := hu 1 z (one_pow k) hz
    have h2 := hm _ _ _ _ _ hc hc
    rw [_root_.mul_one] at h2
    have : c = 1 := mul_eq_left.1 (hc' _ h2)
    exact this ▸ hc
  have H := rel_prod (fun x (c : Kˣ) => Out.WeilIs P.A P.L k x z (unitOn c))
    (by
      have : unitOn (1 : Kˣ) = 1 := map_one _
      show Out.WeilIs P.A P.L k 1 z (unitOn 1)
      rw [this]; exact h1)
    (fun x x' c c' hx hx' => by
      have : unitOn (c * c') = unitOn c * unitOn c' := map_mul _ _ _
      show Out.WeilIs P.A P.L k (x * x') z (unitOn (c * c'))
      rw [this]; exact hm _ _ _ _ _ hx hx') n y (fun i => ζ ^ e i) a h
  have e' : ∏ i, (ζ ^ e i) ^ a i = ζ ^ ∑ i, (a i : ℤ) * e i := by
    have key : ∀ t : Finset (Fin n), ∏ i ∈ t, (ζ ^ e i) ^ a i = ζ ^ ∑ i ∈ t, (a i : ℤ) * e i := fun t => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add, ← zpow_natCast, ← zpow_mul,
          _root_.mul_comm (e b)]
    exact key _
  rw [← e']
  exact H

theorem weilIs_symm_zpow {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ)
    {x y : Out.baseOver (Sp K) ⟶ P.A} {e : ℤ} (h : Out.WeilIs P.A P.L k x y (unitOn (ζ ^ e))) :
    Out.WeilIs P.A P.L k y x (unitOn (ζ ^ (-e))) := by
  have : unitOn (ζ ^ (-e)) = (unitOn (ζ ^ e))⁻¹ := by
    rw [zpow_neg]; exact map_inv _ _
  rw [this]
  exact GlobalTheory.CommPairing.weilIs_symm P.isLB h

theorem injective_stdSymp (g k : ℕ) :
    Function.Injective (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k)) := by
  intro x x' h
  apply GlobalTheory.injective_toBilin'_stdSymp (R := ZMod k) g
  ext a
  have := congrFun h a
  simpa [Matrix.toBilin'_apply, Pi.single_apply] using this

theorem exists_matrix_form : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  intro hL hL2 g N k Mat
  classical
  refine ⟨fun i j => Function.invFun
    (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k))
    (fun a => -(((Out.stdSymp g a j : ℤ) : ZMod k) * N +
      (∑ i, Mat i a * -(∑ l, Mat l j * ((Out.stdSymp g l i : ℤ) : ZMod k))) * N)) i, ?_⟩
  intro K _ _ P pt ζ f s hk hζ hB hpt hf hM hs
  refine ⟨hB.pos, fun j => ?_⟩
  haveI : NeZero k := ⟨fun e => hk (by simp [e])⟩
  haveI := hs.isMonHom
  have tors : ∀ (u : P.A ⟶ P.A) [IsMonHom u] i, (pt i ≫ u) ^ k = 1 := fun u _ i => by
    have := congrArg (IsMonHom.monoidHom u _) (hB.pow_eq_one i)
    rw [map_pow, map_one] at this
    exact this
  obtain ⟨c, hc, -⟩ := hB.existsUnique (tors s j)
  rw [← hc]
  congr 1
  funext i
  congr 1
  refine congrFun (?_ : c = _) i
  rw [← Function.leftInverse_invFun (injective_stdSymp g k) c]
  congr 1
  funext a
  have w₁ := weilIs_linComb hL.weil P k ζ pt (pt a) (hB.pow_eq_one a) _ (fun i => (c i).val) (fun i => hpt i a)
  rw [hc] at w₁
  have w₂ : ∀ i, Out.WeilIs P.A P.L k (pt i) (pt j ≫ f)
      (unitOn (ζ ^ (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i))) := fun i => by
    rw [hM.comp_eq j]
    exact weilIs_symm_zpow P k ζ (weilIs_linComb hL.weil P k ζ pt (pt i) (hB.pow_eq_one i) _ _ (fun l => hpt l i))
  have w₃ := weilIs_linComb hL.weil P k ζ pt _ (tors f j) _ (fun i => (Mat i a).val) w₂
  rw [← hM.comp_eq a] at w₃
  have eφ : (fun i : Fin 2 => ((![𝟙 P.A, f] : Fin 2 → (P.A ⟶ P.A)) i).left) = ![𝟙 P.A.left, f.left] := by
    funext i; fin_cases i <;> rfl
  have w₄ := _root_.GlobalTheory.weilIs_of_formIs_linComb hL hL2 K P (Fin 2) ![𝟙 P.A, f] ![(N : ℤ), (N : ℤ)] s k (pt a) (pt j)
    ![ζ ^ Out.stdSymp g a j, ζ ^ ∑ i, ((Mat i a).val : ℤ) * (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i)] hk
    (fun i => by
      fin_cases i
      · exact (inferInstance : IsMonHom (𝟙 P.A))
      · exact hf)
    (by rw [eφ]; exact hs) (hB.pow_eq_one a) (hB.pow_eq_one j)
    (fun i => by
      fin_cases i
      · show Out.WeilIs P.A P.L k (pt a ≫ 𝟙 _) (pt j ≫ 𝟙 _) _
        rw [Category.comp_id, Category.comp_id]
        exact hpt a j
      · exact w₃)
  rw [Fin.prod_univ_two] at w₄
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at w₄
  rw [← zpow_mul, ← zpow_mul, ← zpow_add] at w₄
  have w₅ := weilIs_symm_zpow P k ζ w₄
  have e := unitOn_inj (((hL.weil (Sp K) P k _).1 _ _ (tors s j) (hB.pow_eq_one a)).unique w₁ w₅)
  rw [← mul_inv_eq_one, ← zpow_sub, hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at e
  push_cast at e
  simp only [ZMod.natCast_zmod_val] at e
  exact sub_eq_zero.1 e

end GlobalTheory.FormTorsion
end

