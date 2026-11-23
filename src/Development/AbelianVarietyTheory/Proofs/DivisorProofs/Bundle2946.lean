module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModuleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicNorm_degree_eq_padicNorm_det_tateModule : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), ‖((deg (A := A) (B := A) f.asHom : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  intro K _ l _ hl A f
  obtain ⟨hfree, hfin, -, hVfin, -⟩ := tl_free_finrank K l hl A
  by_cases hf : IsIsogeny (A := A) (B := A) f.asHom
  · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A f.asHom hf
    obtain ⟨-, hcard⟩ :=
      GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A f.asHom hf
    have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A)
      (tmap l A A f.asHom) (padicValNat l (deg f.asHom)) hcard
    have hnorm : ‖((deg f.asHom : ℕ) : ℤ_[l])‖ =
        (l : ℝ) ^ (-(padicValNat l (deg f.asHom) : ℤ)) := by
      rw [PadicInt.norm_def]
      push_cast
      have h := Padic.eq_padicNorm (p := l) (deg f.asHom : ℚ)
      push_cast at h
      rw [h, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hpos.ne'), padicValRat.of_nat,
        Rat.cast_zpow, Rat.cast_natCast, Nat.padicValNat_def]
    change _ = ‖LinearMap.det (tmap l A A f.asHom)‖
    rw [hdet, hnorm]
  · have hdeg : deg (A := A) (B := A) f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
    by_contra hne
    apply hf
    rw [(_root_.GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective K l hl A A f.asHom).2]
    have hu : IsUnit (LinearMap.det (vmap l f.asHom)) := by
      rw [vmap, LinearMap.det_baseChange]
      exact (isUnit_iff_ne_zero).2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
    rw [← LinearMap.isUnit_iff_isUnit_det] at hu
    exact (Module.End.isUnit_iff _).1 hu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreChar
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.ChartCob

theorem resG_appLE {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O : Z.Opens} {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ O) (h' : V' ≤ V)
    (s : Γ(Z, O)) : resG Y h' ((f.appLE O V h).hom s) = (f.appLE O V' (h'.trans h)).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_resG {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O O' : Z.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ O') (h' : O' ≤ O)
    (s : Γ(Z, O)) :
    (f.appLE O' V h).hom (resG Z h' s) = (f.appLE O V (fun _ hx => h' (h hx))).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem isCoc_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {J : Type} (W : J → Z.Opens)
    (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hc : GlobalTheory.CechFin.IsCoc W c) :
    GlobalTheory.CechFin.IsCoc (fun i => f ⁻¹ᵁ W i)
      (fun i i' => (f.appLE (W i ⊓ W i') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) := by
  intro i i' i''
  have h3 : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'' ≤ f ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have e := congrArg (f.appLE (W i ⊓ W i' ⊓ W i'') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'') h3).hom
    (hc i i' i'')
  rw [map_add (f := _), appLE_resG, appLE_resG, appLE_resG] at e
  exact (congrArg₂ (· + ·) (resG_appLE f _ _ _) (resG_appLE f _ _ _)).trans (e.trans (resG_appLE f _ _ _).symm)

theorem isCoc_sum {Z X : Scheme.{0}} (p : Z ⟶ X) (U : X.Opens) (L : LB Z) (hL : L.IsLB) {n : ℕ}
    (δ : Fin n → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hδ : ∀ a, IsField (p ⁻¹ᵁ U) (δ a))
    {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) (hj : ∀ i, W i ≤ L.U (j i))
    (r : Fin n → Γ(X, U)) :
    GlobalTheory.CechFin.IsCoc W (fun i i' => ∑ b, (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) *
      (δ b (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) *
        resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val)) := by
  intro i i' i''
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e := GlobalTheory.DlogCocycle.dlog_cocycle Z L hL _ (δ b) (hδ b) J W j hWU hj i i' i''
  rw [map_mul (resG Z _) ((p.appLE _ _ _).hom _), map_mul (resG Z _) ((p.appLE _ _ _).hom _),
    map_mul (resG Z _) ((p.appLE _ _ _).hom _), resG_appLE, resG_appLE, resG_appLE, ← e, mul_add]

theorem isCob_pbT {Y Z : Scheme.{0}} (f : Y ⟶ Z) {I : Type} (V Ω : I → Z.Opens)
    (hle : ∀ a, f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ Ω a) (c : ∀ a b : I, Γ(Z, Ω a ⊓ Ω b)) (h : ∀ a, Γ(Y, f ⁻¹ᵁ Ω a))
    (hh : ∀ a b, (f.appLE (Ω a ⊓ Ω b) (f ⁻¹ᵁ Ω a ⊓ f ⁻¹ᵁ Ω b) (fun _ hx => hx)).hom (c a b) =
      resG Y inf_le_left (h a) - resG Y inf_le_right (h b)) :
    GlobalTheory.KS.IsCob (fun a => f ⁻¹ᵁ V a) (fun a b => GlobalTheory.KS.pbT f (c a b) (f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b)) := by
  refine ⟨fun a => -resG Y (hle a) (h a), fun a b => ?_⟩
  have e := (resG_appLE f _ (inf_le_inf (hle a) (hle b)) _).symm.trans
    (congrArg (resG Y (inf_le_inf (hle a) (hle b))) (hh a b))
  rw [map_sub, GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG] at e
  have hab : f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ≤ f ⁻¹ᵁ (Ω a ⊓ Ω b) := fun x hx => ⟨hle a hx.1, hle b hx.2⟩
  simp only [GlobalTheory.KS.pbT, GlobalTheory.KS.rsT]
  rw [dite_eq_left hab, dite_eq_left inf_le_left, dite_eq_left inf_le_right, map_neg, map_neg,
    GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG]
  refine e.trans ?_
  ring

theorem chart_isCob : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  intro E _ _ _ H X t U n δ hδ J W j _ hsup hWU hj m A _ ι hι r h' hh'
  have htop : ∀ x : A.left, x ∈ ι ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    intro x
    have hw := hι.1.w
    have : x ∈ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := by
      rw [hw]
      show (A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U) x ∈ (U.1 : Set X)
      rw [← U.2.range_fromSpec]
      exact ⟨(A.hom ≫ spMap (Ideal.Quotient.mk m)) x, rfl⟩
    exact this
  let Ω : J ⊕ t.PP.L.ι → t.G.left.Opens := Sum.elim W (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1)
  let jj : J ⊕ t.PP.L.ι → t.PP.L.ι := Sum.elim j id
  have hΩU : ∀ q, Ω q ≤ t.G.hom ⁻¹ᵁ U.1 := by
    rintro (i | a)
    · exact hWU i
    · exact inf_le_right
  have hΩj : ∀ q, Ω q ≤ t.PP.L.U (jj q) := by
    rintro (i | a)
    · exact hj i
    · exact inf_le_left
  have hc := isCoc_pullback ι Ω _ (isCoc_sum t.G.hom U.1 t.PP.L t.PP.isLB δ hδ Ω jj hΩU hΩj r)
  obtain ⟨h, hh⟩ := GlobalTheory.CechFin.isCob_of_isCob_subcover A.left (J ⊕ t.PP.L.ι) (fun q => ι ⁻¹ᵁ Ω q)
    (Set.range Sum.inl) (by
      intro q x _
      have hx : ι x ∈ ⨆ i, W i := by rw [hsup]; exact htop x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl i, TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, rfl⟩, hi⟩⟩)
    _ hc (fun q => match q with | Sum.inl i => h' i | Sum.inr _ => 0) (by
      rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
      exact hh' i i')
  exact isCob_pbT ι t.PP.L.U (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) (fun a x hx => ⟨hx, htop x⟩) _
    (fun a => h (Sum.inr a)) (fun a b => hh (Sum.inr a) (Sum.inr b))

end GlobalTheory.ChartCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationValueSpacesGenericPointDictionary
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem vs_iff_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (j₀ : P.A.L.ι) (q : FractionRing Ω), ⊤ ≤ ξ ⁻¹ᵁ P.A.L.U j₀ ∧ q ≠ 0 ∧ ∀ (k : ℕ) (s : FractionRing Ω), 1 ≤ k → (GlobalTheory.HeatSym.VS φ t.PP.L x' g k s ↔ ∃ σ : SecM (𝟙 P.A.A.left) P.A.L k, s = q ^ k * valR ξ _ (σ.f fun _ => j₀)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' _ _ _ _
  rw [← P.bundle]
  intro g hg δL _ ψ ξ hψ hξA hξx _
  obtain ⟨w, hw⟩ := P.U.ext
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.inv_hom_id]; rfl
  have hig : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id]; rfl
  have hξ1 : (ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left = ξ := by
    rw [Category.assoc, hgi, Category.comp_id]
  have hξ2 : (ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R) =
      spMap (algebraMap Ω (FractionRing Ω)) ≫ x' := by
    rw [Category.assoc]; exact hξx
  have chart : ∀ {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (L : LB Z), L.IsLB →
      ∀ (x : Sp A ⟶ Z), ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
    intro A _ _ Z L hL x
    have hc : x (IsLocalRing.closedPoint A) ∈ (⨆ i, L.U i : Z.Opens) := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨j, (GlobalTheory.ZH.CrdCalc.top_le_iff x _).2 hj⟩
  obtain ⟨j₀, hj₀⟩ := chart P.A.L P.A.isLB ξ
  obtain ⟨i, hi⟩ := chart P.U.LG.L P.U.LG.isLB x'
  have hiK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ P.U.LG.L.U i := by
    rw [hξ2]; exact fun p _ => hi (Set.mem_univ _)
  have hjK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left) ⁻¹ᵁ P.A.L.U j₀ := by
    rw [hξ1]; exact hj₀
  have hW : ⊤ ≤ (ξ ≫ P.U.gen.inv.left) ⁻¹ᵁ
      (LB.div (P.U.LG.L.pull (pullback.fst t.G.hom (jK R))) (P.A.L.pull P.U.gen.hom.left)).U
        (fun _ => i, fun _ => j₀) :=
    fun p hp => ⟨Set.mem_iInter.2 fun _ => hiK hp, Set.mem_iInter.2 fun _ => hjK hp⟩
  have hG : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (LB.LinComb P.U.LG.L (fun _ : PUnit => x' ≫ 𝟙 t.G.left) (fun _ => 1)).U (fun _ => i) :=
    fun p hp => Set.mem_iInter.2 fun _ => hi hp
  set e₀ : Ω := valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val with he₀
  set W : FractionRing Ω := valR (ξ ≫ P.U.gen.inv.left) _ (w.s (fun _ => i, fun _ => j₀)).val with hWdef
  have he₀u : IsUnit e₀ := by
    rw [he₀, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hG]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hG).toMonoidHom (g.s fun _ => i)).isUnit
  have hWu : IsUnit W := by
    rw [hWdef, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hW]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hW).toMonoidHom (w.s (fun _ => i, fun _ => j₀))).isUnit
  have hι0 : algebraMap Ω (FractionRing Ω) e₀ ≠ 0 := (he₀u.map _).ne_zero
  have hφne : ∀ r : R, r ≠ 0 → algebraMap Ω (FractionRing Ω) (φ r) ≠ 0 := by
    intro r hr
    rw [← hψ]
    exact (map_ne_zero ψ).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  refine ⟨j₀, W * (algebraMap Ω (FractionRing Ω) e₀)⁻¹, hj₀, mul_ne_zero hWu.ne_zero (inv_ne_zero hι0), ?_⟩
  intro k s hk

  have htop : ∀ {Y : Scheme.{0}} (a : Γ(Y, ⊤)), resTop (⊤ : Y.Opens) a = a := by
    intro Y a
    have e : (homOfLE le_top : (⊤ : Y.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    simp only [resTop, e, op_id, CategoryTheory.Functor.map_id]
    rfl
  have v1 := fun σ ω hv => _root_.GlobalTheory.HeatV.valR_of_isValue t.G.left P.U.LG.L P.U.LG.isLB Ω x' g k σ ω hv i hi
  have v5 : ∀ σ : SecM (𝟙 t.G.left) P.U.LG.L k,
      valR ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) _ (σ.f fun _ => i) =
        algebraMap Ω (FractionRing Ω) (valR x' _ (σ.f fun _ => i)) := by
    intro σ
    rw [hξ2]
    exact (GlobalTheory.ZH.CrdCalc.valR_spMap _ x' ((LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))).U fun _ => i) (fun p hp => Set.mem_iInter.2 fun _ => hi hp)).2 _
  have hj₀' : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb P.A.L (K := Fin 1) (fun _ => 𝟙 P.A.A.left) (fun _ => (k : ℤ))).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => hj₀ hp
  constructor
  · rintro ⟨r, σ, ω, hr, hv, hs⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_pullback_power_bundle_scalar_one _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ
    obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.exists_section_power_through_genIso_and_schemeIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB P.U.gen.inv.left hgi hig k s₁
    obtain ⟨σ', hσ'⟩ := _root_.GlobalTheory.SecSmul.exists_smul _ P.A.L k σ₀ (scal P.A.A.hom (algebraMap R (FractionRing R) r)⁻¹)
    refine ⟨σ', ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ 1 hs₁ (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ₀ s₁ hσ₀
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have e4 : valR ξ _ (σ'.f fun _ => j₀) = (algebraMap Ω (FractionRing Ω) (φ r))⁻¹ * valR ξ _ (σ₀.f fun _ => j₀) := by
      erw [hσ' (fun _ => j₀)]
      rw [GlobalTheory.ZH.CrdCalc.valR_mul _ _ hj₀', GlobalTheory.ZH.FormCount.valR_scal ψ ξ _ hξA _ hj₀', map_inv₀, hψ]
    have e1' : valR (ξ ≫ P.U.gen.inv.left) ⊤ 1 = 1 := by
      rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_top, map_one]
    rw [v5, e1, e1', _root_.one_mul, e3] at e2
    rw [e4]
    have hr' := hφne r hr
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    have hk0 : algebraMap Ω (FractionRing Ω) e₀ ^ k ≠ 0 := pow_ne_zero _ hι0
    field_simp
    linear_combination (-(algebraMap Ω (FractionRing Ω) e₀ ^ k)) * hs + e2
  · rintro ⟨σ', rfl⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_power_through_generating_lineBundleIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB k σ'
    obtain ⟨F, hF, -⟩ := (P.U.expand k hk).1 s₁
    obtain ⟨r, hr, σ, f, hsc, -⟩ := hF
    obtain ⟨ω, hv⟩ := GlobalTheory.HeatV.exists_isValue t.G.left P.U.LG.L P.U.LG.isLB Ω x' g hg k σ
    refine ⟨r, σ, ω, hr, hv, ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ _ hsc (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ' s₁ hs₁
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have hq : (ξ ≫ P.U.gen.inv.left) ≫ pullback.snd t.G.hom (jK R) ≫ jK R =
        spMap ((algebraMap Ω (FractionRing Ω)).comp φ) := by
      rw [← pullback.condition, ← Category.assoc, hξ2, Category.assoc, hx', spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have e5 : valR (ξ ≫ P.U.gen.inv.left) ⊤ (scal (pullback.snd t.G.hom (jK R) ≫ jK R) r) =
        algebraMap Ω (FractionRing Ω) (φ r) := by
      have := GlobalTheory.ZH.FormCount.valR_scal ((algebraMap Ω (FractionRing Ω)).comp φ) (ξ ≫ P.U.gen.inv.left) _ hq ⊤ le_top r
      rw [htop] at this
      exact this
    rw [v5, e1, e5, e3] at e2
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    field_simp
    linear_combination e2

end GlobalTheory.HeatSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraLeftActio
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory

theorem potModel_of_divAlg_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hmon h1 hmul hadd B _ _ _ jj hunit hinj hspan hdim
  haveI : Module.Finite ℚ Bᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv ℚ (M := B))
  refine _root_.GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action V K A g hA hg Oᵐᵒᵖ (fun a => act a.unop) (fun a => hmon a.unop) h1
    (fun a b => hmul b.unop a.unop) (fun a b => hadd a.unop b.unop) Bᵐᵒᵖ (RingHom.op jj)
    ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : x.unop ≠ 0 := by simpa using hx
    simpa using (hunit x.unop hx').op
  · intro a b h
    exact MulOpposite.unop_injective (hinj (MulOpposite.op_injective h))
  · have : Set.range (RingHom.op jj) = (MulOpposite.opLinearEquiv ℚ (M := B)) '' Set.range jj := by
      ext x; constructor
      · rintro ⟨a, rfl⟩; exact ⟨jj a.unop, ⟨a.unop, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨MulOpposite.op a, rfl⟩
    rw [this, ← LinearEquiv.coe_coe, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · rwa [(MulOpposite.opLinearEquiv ℚ (M := B)).symm.finrank_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreChartOfTautologicalChartEtaleCompletion
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartPre

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem eq_of_jK_comp_eq {R o : Type} [CommRing R] [IsDomain R] [CommRing o] {u v : Sp R ⟶ Sp o}
    (h : jK R ≫ u = jK R ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := Spec.map_surjective u
  obtain ⟨v, rfl⟩ := Spec.map_surjective v
  have h' : u ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = v ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  congr 1
  ext a
  exact IsFractionRing.injective R (FractionRing R) (congrArg (fun f => f.hom a) h')

theorem preChart_of_isEtaleCompletion : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → PreChart F (π ≫ z) j φ BD d (ξ (closedPoint C.R)) := by
  intro g hg φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy het hfu
  obtain ⟨J, -, -, -, -, hP, -, hji, -, -, hval⟩ := hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hM
  obtain ⟨hsa, hab, hgen, hmum, hbase⟩ := hF
  obtain ⟨hreg, hch, -, -, hrel, -⟩ := GlobalTheory.TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, -⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  haveI : IsProper (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : S.IsSeparated := ⟨by
    rw [← terminal.comp_from (π ≫ z)]
    infer_instance⟩
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hc : IsAdicComplete (maximalIdeal C.R) C.R := C.compl.2.1
  have hξ : ξ ≫ π ≫ z = spMap C.b := eq_of_jK_comp_eq (by
    rw [← hbase, ← Category.assoc, ← hy, Category.assoc, ← Category.assoc j, hji, hiz])
  have hrad := GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ (Scheme.stalkClosedPointTo ξ).hom hc het hfu
  obtain ⟨hb₁, hb₂⟩ := GlobalTheory.BdEqChart.boundary_eq g n F S j C.R C.b ξ G₁ y ((Over.pullback (jK C.R)).obj G₁)
    (pullback.fst G₁.hom (jK C.R)) α₁ hsa (isGrpPullback_pullback G₁ (jK C.R)) hgen hy hrad C.m C.t hrel hab
  haveI : Module.Free ℤ C.Q.X := Module.Free.of_equiv C.e.toIntLinearEquiv.symm
  have hnat : ∀ k, ∃ c : ℕ, φ.evalZ ((n : ℤ) • C.δ k) = c := fun k =>
    (hφ C.Q.X hrk).exists_nat (Submodule.smul_mem _ _ (hcone.mem k)) fun w =>
      mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
  choose c hcn using hnat
  have ha : ∀ k, ((d * c k : ℕ) : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := fun k => by rw [hcn, Nat.cast_mul]
  have hBD := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F S j φ hφ d BD.idealSheaf hval C.R hc C.b ξ C.Q G₁ y α₁ hsa hgen
    hy.symm hmum C.m C.t C.δ (fun k => d * c k) hrel hab hcone hdef hmono ha
  exact ⟨C.R, inferInstance, hreg, inferInstance, C.b, ξ, C.m, C.t, C.Q, C.δ, fun k => d * c k, G₁, inferInstance, y, α₁,
    ⟨hc, hch, hξ, rfl, het, hfu⟩, ⟨hrel, hb₂, hb₁⟩, ⟨hsa, hab, hy, hgen⟩, ⟨hmum, hrk, hcone, hdef, hmono⟩, ha, hBD⟩

end GlobalTheory.TChartPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresBasicOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtPres

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem isWt_div {α : Q.X} {V : Y.H.left.Opens} {f u u' : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hu : IsWt Y α V u)
    (h : u * u' = 1) : IsWt Y 0 V (f * u') := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have e : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V → valR b V u * valR b V u' = 1 := fun b hb => by
    rw [← WtAlg.valR_mul'' _ _ hb, h, WtAlg.valR_eq' _ _ hb, map_one, map_one]
  have e₁ := e a hV
  have e₂ := e a' hV'
  rw [hu S φ x x' c a a' ha ha' hV hV' hq hc] at e₂
  rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]
  linear_combination valR a V f * valR a V u' * e₂ - c α * valR a V f * valR a' V u' * e₁

end GlobalTheory.Heat.WtPres
end
end

