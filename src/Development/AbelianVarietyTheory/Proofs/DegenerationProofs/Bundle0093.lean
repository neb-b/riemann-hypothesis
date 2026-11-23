module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.IsTorus
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormCount

section Values
variable {F : Type} [CommRing F] {X Y : Scheme.{0}}

theorem valR_appLE (x : Sp F ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have hx' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [CrdCalc.valR_eq _ _ hx, CrdCalc.valR_eq _ _ hx', CrdCalc.valHom, CrdCalc.valHom,
    ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ h hx]
  rfl

theorem valR_scal {K : Type} [CommRing K] (ψ : K →+* F) (x : Sp F ⟶ Y) (q : Y ⟶ Sp K) (hq : x ≫ q = spMap ψ)
    (V : Y.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ V) (c : K) : valR x V (resTop V (scal q c)) = ψ c := by
  have e : valR x V (resTop V (scal q c)) =
      valR (x ≫ q) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
    valR_appLE x q ⊤ V le_top _ hx
  have e' := (CrdCalc.valR_spMap ψ (𝟙 (Sp K)) ⊤ le_rfl).2 ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  rw [Category.comp_id] at e'
  rw [e, hq, e', CrdCalc.valR_eq _ _ le_top]
  have h : (𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (((𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top).hom _) = c
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply c

theorem wchart_le (L : LB X) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem exists_monomial (L : LB X) (φ : Y ⟶ X) (N d : ℕ) {J : Type} [Fintype J]
    (σ : J → (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (N : ℤ))).Sec) (α : J → ℕ) (hα : ∑ i, α i = d) :
    ∃ s : (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => ((N * d : ℕ) : ℤ))).Sec,
      ∀ j, s.f j = ∏ i, (φ.appLE _ _ (wchart_le L φ j)).hom ((σ i).f j) ^ α i := by
  have pull_restrict {U U' : X.Opens} {V V' : Y.Opens} (hu : U' ≤ U) (hv : V' ≤ V)
      (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U') (a : Γ(X, U)) :
      (Y.presheaf.map (homOfLE hv).op).hom ((φ.appLE U V h).hom a) =
        (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE hu).op).hom a) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have transition {Z : Scheme.{0}} (f : Z ⟶ X) (j j' : Fin 1 → L.ι) (n : ℕ) :
      ((L.LinComb (fun _ : Fin 1 => f) (fun _ => (n : ℤ))).g j j').val =
        ((f.appLE _ _ (le_inf
          (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => f) j 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => f) j' 0)))).hom
          (L.g (j 0) (j' 0)).val) ^ n := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  let A (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => 𝟙 X) j
  let B (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => φ) j
  let s (i : J) (j : Fin 1 → L.ι) : Γ(X, A j) := (σ i).f j
  let m (j : Fin 1 → L.ι) : Γ(Y, B j) := ∏ i, (φ.appLE (A j) (B j) (wchart_le L φ j)).hom (s i j) ^ α i
  refine ⟨⟨m, ?_⟩, fun _ => rfl⟩
  rintro (j : Fin 1 → L.ι) (j' : Fin 1 → L.ι)
  let U := A j ⊓ A j'
  let V := B j ⊓ B j'
  have h : V ≤ φ ⁻¹ᵁ U := fun _ hy => ⟨wchart_le L φ j hy.1, wchart_le L φ j' hy.2⟩
  let p := (φ.appLE U V h).hom
  let gX : Γ(X, U) := ((L.LinComb (fun _ : Fin 1 => 𝟙 X) (fun _ => (N : ℤ))).g j j').val
  let gY : Γ(Y, V) := ((L.LinComb (fun _ : Fin 1 => φ) (fun _ => ((N * d : ℕ) : ℤ))).g j j').val
  have hg : p gX ^ d = gY := by
    dsimp only [p, gX, gY]
    rw [transition (𝟙 X) j j' N, transition φ j j' (N * d), map_pow, ← pow_mul,
      ← CommRingCat.comp_apply]
    erw [Scheme.Hom.appLE_comp_appLE φ (𝟙 X)]
    rfl
  let leftX := (X.presheaf.map (homOfLE (inf_le_left : U ≤ A j)).op).hom
  let rightX := (X.presheaf.map (homOfLE (inf_le_right : U ≤ A j')).op).hom
  have hc (i : J) : p (leftX (s i j)) = p gX * p (rightX (s i j')) := by
    rw [← map_mul]
    exact congrArg p ((σ i).compat j j')
  change (Y.presheaf.map (homOfLE (inf_le_left : V ≤ B j)).op).hom (m j) =
    gY * (Y.presheaf.map (homOfLE (inf_le_right : V ≤ B j')).op).hom (m j')
  simp only [m, map_prod, map_pow,
    pull_restrict (inf_le_left : U ≤ A j) (inf_le_left : V ≤ B j) (wchart_le L φ j) h,
    pull_restrict (inf_le_right : U ≤ A j') (inf_le_right : V ≤ B j') (wchart_le L φ j') h]
  change (∏ i, p (leftX (s i j)) ^ α i) = gY * ∏ i, p (rightX (s i j')) ^ α i
  simp only [hc, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα, hg]

end Values

theorem hilb_le {k J : Type} [Field k] [Fintype J] (C : Set (J → k)) (d m : ℕ) (β : Fin m → C → k)
    (h : ∀ α : J → ℕ, ∑ i, α i = d → ∃ c : Fin m → k, ∀ v : C, ∏ i, v.1 i ^ α i = ∑ l, c l * β l v) :
    hilb C d ≤ m := by
  have le : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) ≤ Submodule.span k (Set.range β) := by
    rintro _ ⟨P, hP, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hd : ∑ i, α i = d := by
      have := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hP hα
      rw [this]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.1 hi).symm
    obtain ⟨c, hc⟩ := h α hd
    refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨fun l => P.coeff α * c l, funext fun v => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      MvPolynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), hc v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => _root_.mul_assoc _ _ _
  have := Module.Finite.span_of_finite k (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem dim_eq (u : ρ.UTest p y₀) : u.A.g = S.g :=
  (ReciprocityTheory.ChartRestriction.G.H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint _))).trans ρ.g_eq

theorem gPt_j (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem hilb_generic_le : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (J : Type) [Fintype J] (σ : J → (u.H S.N).Sec) (d : ℕ), 1 ≤ d → hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w} d ≤ (S.N * d) ^ S.g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u J _ σ d hd
  have hN : 1 ≤ S.N * d := by
    rw [ρ.N_eq]
    exact Nat.mul_pos (pow_pos (pow_pos ρ.n_prime.pos _) _) hd
  obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hL.1.secBaseChange u.V _ u.D u.A u.G
    u.U.toUnifPre (S.N * d) hN
  rw [← dim_eq u]
  let C := {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left,
    a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w}
  have hC : ∀ w : C, ∃ (x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V)) (l : Fin 1 → u.U.LG.L.ι)
      (c : PadicAlgCl p), x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ∧
      ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => pullback.fst u.G.hom (jK u.V)) l ∧
      ∀ i, w.1 i = c * valR (x ≫ pullback.fst _ _) _ ((σ i).f l) := by
    rintro ⟨w, a, ha, l, c, hl, hw⟩
    obtain ⟨x, rfl, hx⟩ : ∃ x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = a ∧
        x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) :=
      ⟨pullback.lift a _ (ha.trans (gPt_j u)), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    exact ⟨x, l, c, hx, fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hl hy) k, hw⟩
  choose x l c hx hl hw using hC
  refine hilb_le C d _ (fun n w => c w ^ d * valR (x w) _ ((b n).f (l w))) fun α hα => ?_
  obtain ⟨s, hs⟩ := exists_monomial u.U.LG.L (pullback.fst u.G.hom (jK u.V)) S.N d σ α hα
  obtain ⟨e, he, -⟩ := hb s
  refine ⟨fun n => algebraMap _ _ (e n), fun w => ?_⟩
  have h := congrArg (CrdCalc.valHom (x w) _ (hl w)) ((hs (l w)).symm.trans (he (l w)))
  replace h := (map_prod _ _ _).symm.trans (h.trans (map_sum _ _ _))
  simp only [hw w, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα]
  refine Eq.trans ?_ ((congrArg (c w ^ d * ·) h).trans ?_)
  · refine congrArg (c w ^ d * ·) (Finset.prod_congr rfl fun i _ => Eq.symm ((map_pow _ _ _).trans ?_))
    exact congrArg (· ^ α i) ((CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_appLE _ _ _ _ _ _ (hl w)))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Eq.trans (congrArg (c w ^ d * ·) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (CrdCalc.valR_eq _ _ (hl w) _).symm))) (mul_left_comm _ _ _)
  exact (CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_scal _ (x w) _ (hx w) _ (hl w) (e n))

end GlobalTheory.ZH.FormCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdjoin
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

section
variable (R : Type) [CommRing R] [IsDomain R] (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E]
  [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] {X : Scheme.{0}} {L : LB X}

omit [IsDomain R] in
theorem comp_jFK : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def ιE : TF (R := R) F ⟶ TF (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (comp_jFK R E F)))

omit [IsDomain R] in
theorem ι_inj : Function.Injective fun ψ : (TF (R := R) E).left ⟶ X => (ιE R E F).left ≫ ψ := by
  intro a b h
  have : Epi (ιE R E F).left := by
    show Epi (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap E F))) := inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
      ⟨fun u => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (ιE R E F).left).1 h

omit [IsDomain R] in
theorem gs_ι (z : (TF (R := R) F).left) (a : Γ(Spec (CommRingCat.of E), ⊤)) :
    gs (ιE R E F).left z ⊤ a = cst F z (algebraMap E F ((Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom a)) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap E F)) a)


omit [IsDomain R] in
theorem sec_rat (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TF (R := R) E).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = 1) :
    ∃ a : E, ∀ z J, Good L z J → sval s (ιE R E F).left z J = cst F z (algebraMap E F a) := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιE R E F).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj R E F).extend_apply]) s
  have le : (⊤ : (TF (R := R) E).left.Opens) ≤
      LB.wchart L (PEmpty.elim : PEmpty → ((TF (R := R) E).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
    (((TF (R := R) E).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι R E F]
  exact (gs_res _ z le trivial _).symm

def HE (L : LB X) (σ : CoefVal.FS R F X)
    (f : ∀ z : (TF (R := R) F).left, (((TF (R := R) F).left ⟶ X) → L.ι) → (TF (R := R) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TF (R := R) E).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιE R E F).left z J).val

variable {R E F}

theorem HE.mul {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x) (H' : HE R E F L σ' f' x') :
    HE R E F L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HE.one : HE R E F L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TF (R := R) E).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HE.congr {σ σ' : CoefVal.FS R F X} {f f'} {x : F} (H : HE R E F L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HE R E F L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HE.pow {σ : CoefVal.FS R F X} {f} {x : F} (H : HE R E F L σ f x) (n : ℕ) :
    HE R E F L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HE.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HE.ratio (hL : L.IsLB) {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x)
    (H' : HE R E F L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) :
    ∃ a : E, ∀ z J, Good L z J → cst F z x' * f z J = cst F z (x * algebraMap E F a) * f' z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, hav⟩ := sec_rat R E F hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', hσ, mul_inv_cancel])
  refine ⟨a, fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : (val t (ιE R E F).left z J).val = cst F z (algebraMap E F a) * (val t' (ιE R E F).left z J).val := by
    rw [← b, Units.val_mul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [e z J hJ, e' z J hJ, c]
  simp only [cst_eq, map_mul]
  ring

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem he_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem he_sec (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    ∃ a : E, HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) (algebraMap E F a) := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := E) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, hav⟩ := sec_rat R E F hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_he (hL : L.IsLB) {φ : K → ((TF (R := R) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιE R E F).left ≫ ψ) :
    ∃ x : F, x ≠ 0 ∧ HE R E F L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := E) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιE R E F).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  refine ⟨c, hc, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], fun z J hJ => ?_⟩
  have := e (TF (R := R) F).left (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end

theorem exists_adjoin {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (A : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType A.hom] (b : TF (R := R) F ⟶ A) :
    ∃ (T : Finset F) (b₁ : TF (R := R) (IntermediateField.adjoin (FractionRing R) (T : Set F)) ⟶ A),
      ιE R _ F ≫ b₁ = b := by
  classical
  let a : Spec (CommRingCat.of F) ⟶ A.left := b.left
  obtain ⟨B, i, _, t, ht⟩ : ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ A.left) (_ : IsOpenImmersion i)
      (t : Spec B), i t = a (IsLocalRing.closedPoint F) := by
    obtain ⟨n, t, ht⟩ := A.left.affineCover.exists_eq (a (IsLocalRing.closedPoint F))
    exact ⟨_, A.left.affineCover.f n, A.left.affineCover.map_prop n, t, ht⟩
  have hr : Set.range a ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨t, ht.trans (congrArg a (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i a hr)
  have hφa : Spec.map φ ≫ i = a := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (show Spec B ⟶ Spec (CommRingCat.of R) from i ≫ A.hom)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, Spec.map_comp]
    exact Over.w b
  let : Algebra R B := ψ.hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra R B).FG := (show Algebra.FiniteType R B from h₂).out
  let K := IntermediateField.adjoin (FractionRing R) ((s.image φ.hom : Finset F) : Set F)
  have hm : ∀ x : B, φ.hom x ∈ K := fun x => by
    have hx : x ∈ Algebra.adjoin R (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have e : φ.hom (algebraMap R B r) = algebraMap (FractionRing R) F (algebraMap R _ r) := congr($hc r)
      rw [e]; exact K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have e : (ιE R K F).left ≫ Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i = b.left := by
    refine Eq.trans ?_ hφa
    show Spec.map _ ≫ _ = _
    rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨s.image φ.hom, Over.homMk (Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i) ?_,
    Over.OverMorphism.ext e⟩
  apply ι_inj R K F
  show (ιE R K F).left ≫ _ ≫ _ = (ιE R K F).left ≫ _
  rw [← Category.assoc, e, Over.w, Over.w]

end GlobalTheory.UT.CoefField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialise
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsoFinite

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [CommRing k] {C : Type} [CommRing C] [Algebra k C] {A A' : Over (Sp k)}

theorem comm_bcMap (R : Subalgebra k C)
    (f : (Over.pullback (spMap (algebraMap k C))).obj A ⟶ (Over.pullback (spMap (algebraMap k C))).obj A')
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A')
    (h : bcMap A.hom R.val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A'.hom R.val = bcMap A.hom R.val ≫ g.left := by
  have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (f.left ≫ ·) (bcMap_fst A'.hom R.val)).trans
      (h.symm.trans (Category.assoc _ _ _).symm))
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    have a₁ := congrArg (f.left ≫ ·) (bcMap_snd A'.hom R.val)
    have a₂ := congrArg (bcMap A.hom R.val ≫ ·) hg
    have a₃ := congrArg (· ≫ spMap R.val.toRingHom) hf
    exact a₁.trans ((Category.assoc _ _ _).symm.trans
      (a₃.trans ((bcMap_snd A.hom R.val).symm.trans a₂.symm)))

variable [GrpObj A] [GrpObj A']

theorem exists_fg_iso [QuasiCompact A.hom] [IsSeparated A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [QuasiCompact A'.hom] [IsSeparated A'.hom] [Flat A'.hom] [LocallyOfFinitePresentation A'.hom]
    (e : (Over.pullback (spMap (algebraMap k C))).obj A ≅ (Over.pullback (spMap (algebraMap k C))).obj A')
    [IsMonHom e.hom] :
    ∃ (R : Subalgebra k C)
      (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A'),
      R.FG ∧ IsMonHom g.hom := by
  obtain ⟨R₁, f₁, hR₁, _, h₁⟩ := exists_fg_isMonHom e.hom
  obtain ⟨R₂, f₂, hR₂, _, h₂⟩ := exists_fg_isMonHom e.inv
  let R : Subalgebra k C := R₁ ⊔ R₂
  obtain ⟨g₁, m₁, k₁⟩ := exists_specialise f₁ (Subalgebra.inclusion (le_sup_left : R₁ ≤ R))
  obtain ⟨g₂, m₂, k₂⟩ := exists_specialise f₂ (Subalgebra.inclusion (le_sup_right : R₂ ≤ R))
  have c₁ := comm_bcMap R e.hom g₁ ((congrArg (_ ≫ ·) k₁).trans
    ((bcMap_comp_of_eq_assoc A.hom _ _ R₁.val (fun _ => rfl) _).trans h₁))
  have c₂ := comm_bcMap R e.inv g₂ ((congrArg (_ ≫ ·) k₂).trans
    ((bcMap_comp_of_eq_assoc A'.hom _ _ R₂.val (fun _ => rfl) _).trans h₂))
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom R.val.toRingHom)
    Subtype.val_injective
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsIso g₁ := ExtUnique.isIso_of_isPullback (isGrpPullback_bcMap A R.val).1
    (isGrpPullback_bcMap A' R.val).1 e g₁ g₂ c₁ c₂
  exact ⟨R, asIso g₁, hR₁.sup hR₂, m₁⟩

theorem exists_iso_specialise {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A')
    [IsMonHom g.hom] (ρ : R →ₐ[k] S) :
    ∃ e : (Over.pullback (spMap (algebraMap k S))).obj A ≅ (Over.pullback (spMap (algebraMap k S))).obj A',
      IsMonHom e.hom := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_bcMap A ρ) (isGrpPullback_pullback _ _)
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback _ _) (isGrpPullback_bcMap A' ρ)
  exact ⟨a ≪≫ (Over.pullback (spMap ρ.toRingHom)).mapIso g ≪≫ b,
    inferInstanceAs (IsMonHom (a.hom ≫ (Over.pullback (spMap ρ.toRingHom)).map g.hom ≫ b.hom))⟩

theorem exists_finite_iso : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (T T' : Over (Spec (CommRingCat.of k))) [GrpObj T] [GrpObj T'], IsAffineHom T.hom → IsAffineHom T'.hom → LocallyOfFiniteType T.hom → LocallyOfFiniteType T'.hom → (∃ e : fieldBaseChange k Ω T ≅ fieldBaseChange k Ω T', IsMonHom e.hom) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k') (e : fieldBaseChange k k' T ≅ fieldBaseChange k k' T'), IsMonHom e.hom := by
  intro k Ω _ _ _ T T' _ _ _ _ _ _ ⟨e, he⟩
  have : LocallyOfFinitePresentation T.hom := inferInstance
  have : LocallyOfFinitePresentation T'.hom := inferInstance
  obtain ⟨R, g, hR, hg⟩ := exists_fg_iso (k := k) (C := Ω) (A := T) (A' := T') e
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := .of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  obtain ⟨e', he'⟩ := exists_iso_specialise g (Ideal.Quotient.mkₐ k m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, this, e', he'⟩

end GlobalTheory.IsoFinite
end
end

