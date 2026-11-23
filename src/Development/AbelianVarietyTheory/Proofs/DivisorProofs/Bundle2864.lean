module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
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

namespace GlobalTheory.Heat.InvWt

theorem top_le_preimage_of_fst {S : Type} [CommRing S] {X : Scheme.{0}} (w : Sp (DualNumber S) ⟶ X) (a : Sp S ⟶ X) (U : X.Opens)
    (h : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = a) (ha : ⊤ ≤ a ⁻¹ᵁ U) : ⊤ ≤ w ⁻¹ᵁ U := by
  intro p _
  let p0 : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (DualNumber S)) p
  have hp : (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) p0 = p := by
    apply PrimeSpectrum.ext
    ext z
    show algebraMap S (DualNumber S) (TrivSqZeroExt.fst z) ∈ p.asIdeal ↔ z ∈ p.asIdeal
    have hz : TrivSqZeroExt.inr (TrivSqZeroExt.snd z) ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    constructor
    · intro h1
      rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      exact p.asIdeal.add_mem h1 hz
    · intro h1
      have e : TrivSqZeroExt.inl (TrivSqZeroExt.fst z) = z - TrivSqZeroExt.inr (TrivSqZeroExt.snd z) := by
        rw [eq_sub_iff_add_eq, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
      rw [e]
      exact p.asIdeal.sub_mem h1 hz
  have hm : p0 ∈ a ⁻¹ᵁ U := ha (Set.mem_univ _)
  rw [← h] at hm
  show w p ∈ U
  rw [← hp]
  exact hm

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) := by
  ext
  have e := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem exists_tan_over {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    {S : Type} [CommRing S] (φ : R →+* S) :
    ∃ v' : Over.mk (spMap ((algebraMap S (DualNumber S)).comp φ)) ⟶ G,
      v'.left = spMap (dualMap φ) ≫ (tv v).left ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = (1 : Over.mk (spMap φ) ⟶ G).left := by
  refine ⟨Over.homMk (spMap (dualMap φ) ≫ (tv v).left) ?_, rfl, ?_⟩
  · rw [Category.assoc, Over.w (tv v)]
    simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
    congr 1
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp]
  · let ψ : Over.mk (spMap φ) ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) (by
        simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
        congr 1
        ext r
        simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hψ : ψ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp R)) (tm ((0 : R) • LinearMap.id)) = ψ := by
      apply Over.OverMorphism.ext
      show (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ spMap _ =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)
      simp only [spMap, ← Spec.map_comp, Category.assoc]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      simp [dualMap, CommRingCat.hom_comp, tm]
    have e := congrArg (·.left) (Formalism.L2.Pj.tan_pull (𝟙 (Sp R)) ψ hψ (tv v) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v))
    simpa [ψ] using e

theorem cv_pull_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T T' : Over (Sp R)} (k : T' ⟶ T) (x x' : T ⟶ Y.H) (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (k ≫ x')).s χ) (𝟙 _) y J =
        gm (𝟙 T'.left) y ⊤ (Units.map k.left.appTop.hom.toMonoidHom (u χ)) * val ((Y.Φ _ (k ≫ x)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have p' := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x')).2 χ y J hJ
  have p := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x)).2 χ y J hJ
  let g : LB.Gen (LB.LinComb Q.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top (u χ)⟩
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) z J', Good Q.P.L z J' → val g r z J' = gm r z ⊤ (u χ) :=
    fun Z r z J' hJ' => gm_res r z le_top (hJ'.mem PEmpty.elim r) (u χ)
  have hC := corr_of_val Q.P.isLB (t := (Y.Φ _ x').s χ) (t' := LB.mulGen Q.P.L _ _ _ _ g ((Y.Φ _ x).s χ))
    (fun y' J' hJ' => by rw [val_mul hJ', hg _ _ _ _ hJ']; exact h χ y' J' hJ')
  have e := val_corr hJ hC k.left
  rw [val_mul hJ, hg _ _ _ _ hJ] at e
  show GlobalTheory.TorusModel.cv _ χ y J = _ * GlobalTheory.TorusModel.cv _ χ y J
  rw [p', p, e]
  congr 1
  have e2 := gm_pull (𝟙 _) k.left y ⊤ trivial (u χ)
  rw [Category.id_comp] at e2
  rw [← e2]
  rfl

theorem cv_mul_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T : Over (Sp R)} (X X' v : T ⟶ Y.H) (hq : X' ≫ Y.q = X ≫ Y.q)
    (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ X').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ X).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (X' * v)).s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ (X * v)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X v)).2 χ y J hJ
  have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X' v)).2 χ y J hJ
  rw [Y.Φ_b, Y.Φ_b] at h1 h2
  rw [hq] at h2
  have h3 := h χ y J hJ
  apply mul_right_cancel (b := DVR.th Q y J (DVR.cP Q _ χ) (X ≫ Y.q) (v ≫ Y.q))
  show GlobalTheory.TorusModel.cv _ χ y J * _ = _ * GlobalTheory.TorusModel.cv _ χ y J * _
  rw [h2, _root_.mul_assoc, h1, ← _root_.mul_assoc]
  congr 1

theorem _root_.GlobalTheory.Heat.IsInv.isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  intro R _ _ Q O _ _ _ oa Y v dd hinv α V f hf
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  let φε : R →+* DualNumber S := (algebraMap S (DualNumber S)).comp φ
  let π : Over.mk (spMap φε) ⟶ Over.mk (spMap φ) :=
    Over.homMk (spMap (algebraMap S (DualNumber S))) (by
      show spMap (algebraMap S (DualNumber S)) ≫ spMap φ = spMap φε
      simp only [spMap, φε, ← Spec.map_comp]; rfl)
  let ie : Over.mk (spMap φ) ⟶ Over.mk (spMap φε) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap φε = spMap φ
      simp only [spMap, φε, ← Spec.map_comp]
      congr 1)
  obtain ⟨v'', hv₁, hv₂⟩ := exists_tan_over Y.H v φ
  have hιπ : ie ≫ π = 𝟙 _ := by
    ext1
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _
    simp only [spMap, ← Spec.map_comp]
    rw [← Spec.map_id]; congr 1
  have hiev : ie ≫ v'' = 1 := by
    ext1
    exact hv₂
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have hW : ∀ z : Over.mk (spMap φ) ⟶ Y.H, ie ≫ (π ≫ z * v'') = z := by
    intro z
    rw [MonObj.comp_mul, ← Category.assoc, hιπ, Category.id_comp, hiev, _root_.mul_one]
  have hWa : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x * v'').left = a := by
    rw [ha]; exact congrArg (·.left) (hW x)
  have hWa' : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x' * v'').left = a' := by
    rw [ha']; exact congrArg (·.left) (hW x')
  have htr : ∀ z : Over.mk (spMap φ) ⟶ Y.H, IsTr Y.H φ z.left v (π ≫ z * v'').left := by
    intro z
    let e : tEpsG (z.left ≫ Y.H.hom) ⟶ Over.mk (spMap φε) := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap φε = spMap (algebraMap S (DualNumber S)) ≫ z.left ≫ Y.H.hom
      rw [Over.w z]
      simp only [Over.mk_hom, Category.id_comp, spMap, φε]
      rw [← Spec.map_comp]; rfl)
    refine ⟨e ≫ π ≫ z, e ≫ v'', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ spMap (algebraMap S (DualNumber S)) ≫ z.left = _
      rw [Category.id_comp]
    · show 𝟙 _ ≫ v''.left = _
      rw [Category.id_comp, hv₁]
    · rw [← MonObj.comp_mul]
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  let c' : Q.X → (DualNumber S)ˣ := fun χ => Units.map (algebraMap S (DualNumber S)).toMonoidHom (c χ)
  have hqW : (π ≫ x' * v'') ≫ Y.q = (π ≫ x * v'') ≫ Y.q := by
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, hq]
  have hcW := cv_mul_of_unit Y (π ≫ x) (π ≫ x') v'' (by rw [Category.assoc, Category.assoc, hq])
    (fun χ => Units.map π.left.appTop.hom.toMonoidHom (unitOn (c χ))) (cv_pull_of_unit Y π x x' (fun χ => unitOn (c χ)) hc)
  have key := hf (DualNumber S) φε (π ≫ x * v'') (π ≫ x' * v'') c' _ _ rfl rfl
    (top_le_preimage_of_fst _ a V hWa hV) (top_le_preimage_of_fst _ a' V hWa' hV') hqW (fun χ y J hJ => by
      rw [hcW χ y J hJ]
      congr 2
      exact map_unitOn _ _)
  have e₁ := hinv.2 S φ a (π ≫ x * v'').left V f (by rw [ha]; exact Over.w x) hV (ha ▸ htr x)
  have e₂ := hinv.2 S φ a' (π ≫ x' * v'').left V f (by rw [ha']; exact Over.w x') hV' (ha' ▸ htr x')
  rw [← e₁, ← e₂, key]
  show ((c' α : DualNumber S) * _).snd = _
  rw [TrivSqZeroExt.snd_mul]
  simp [c', TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.Heat.InvWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionOfBasicOpens
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

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open GlobalTheory.TorusModel (isPull_iff)

theorem gm_comp' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ q) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm q (r z) U a) := by
  refine Units.ext ?_
  rw [← gs_unit (r ≫ q) z U h, ← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h,
    Category.id_comp, gs_unit q (r z) U h]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem isWt_of_local (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V))
    (h : ∀ (S : Type) [CommRing S] [IsLocalRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ),
      ⊤ ≤ x.left ⁻¹ᵁ V → ⊤ ≤ x'.left ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
      (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
      valR (A := S) x'.left V f = c α * valR (A := S) x.left V f) : IsWt Y α V f := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun P hP => (map_sub _ _ _).trans (sub_eq_zero.2 ?_))
  let l := algebraMap S (Localization.AtPrime P)
  let k : Over.mk (spMap (l.comp φ)) ⟶ Over.mk (spMap φ) := Over.homMk (spMap l)
    (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom l)).symm
  obtain ⟨a₁, a₂⟩ := valR_spMap l x.left V hV
  obtain ⟨b₁, b₂⟩ := valR_spMap l x'.left V hV'
  have := h _ (l.comp φ) (k ≫ x) (k ≫ x') (fun χ => Units.map l.toMonoidHom (c χ)) a₁ b₁
    (by rw [Category.assoc, Category.assoc, hq]) fun χ y J hJ => by
      have hJ' : Good Q.P.L (k.left y) fun ψ => J (k.left ≫ ψ) := fun ψ => hJ (k.left ≫ ψ)
      have key : ∀ u : Over.mk (spMap φ) ⟶ Y.H, val ((Y.Φ _ (k ≫ u)).s χ) (𝟙 _) y J =
          Units.map (k.left.stalkMap y).hom.toMonoidHom
            (val ((Y.Φ _ u).s χ) (𝟙 _) (k.left y) fun ψ => J (k.left ≫ ψ)) := fun u => by
        refine (((isPull_iff _ _ _).1 (Y.rep.1 _ _ k u)).2 χ y J hJ).trans ?_
        rw [val_of _ (𝟙 _) _ _ (fun i => J (k.left ≫ DegPre.gtφT Q _ (Y.Φ _ u).b χ i)) (fun i => by rw [Category.id_comp])]
        refine Eq.trans ?_ (gm_comp' k.left (𝟙 _) y _ (hJ.mem _ k.left) _)
        rw [Category.comp_id]
        rfl
      rw [key, key, hc χ _ _ hJ', map_mul, ← gm_comp' k.left (𝟙 _) y ⊤ trivial]
      congr 1
      refine Units.ext ?_
      rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
      refine congrArg ((Sp (Localization.AtPrime P)).presheaf.germ ⊤ y trivial).hom ?_
      exact (congrArg (fun q => q.hom (c χ : S)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom l))).symm
  rw [map_mul]
  exact (b₂ f).symm.trans (this.trans (congrArg (_ * ·) (a₂ f)))

end GlobalTheory.Heat.WtLocal

namespace GlobalTheory.Heat.WtLocal

open GlobalTheory.ZH.CrdCalc (valR_res)

theorem isWt_of_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V')), (∀ (g : Γ(Q.P.A.left, V.1)) (h : Q.P.A.left.basicOpen g ≤ V'), IsWt Y α (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) (resG Y.H.left (Y.q.left.preimage_mono h) f)) → IsWt Y α (Y.q.left ⁻¹ᵁ V') f := by
  intro R _ _ Q O _ _ _ oa Y V V' hV α f hf
  refine isWt_of_local Y α _ _ fun S _ _ φ x x' c hx hx' hq hc => ?_
  have e : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg (fun q => q.left) hq
  have hp : Y.q.left (x'.left (closedPoint S)) ∈ V' := hx' trivial
  obtain ⟨g, hg, hpg⟩ := V.2.exists_basicOpen_le ⟨_, hp⟩ (hV hp)
  have m' : ⊤ ≤ x'.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of S) x'.left hpg).ge
  have m : ⊤ ≤ x.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) := by
    rw [← Scheme.Hom.comp_preimage, ← e]; exact m'
  have t := hf g hg S φ x x' c _ _ rfl rfl m m' hq hc
  exact (valR_res (R := S) x'.left _ m' f).symm.trans (t.trans (congrArg (_ * ·) (valR_res (R := S) x.left _ m f)))

end GlobalTheory.Heat.WtLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
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

namespace GlobalTheory.HeatRatio

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R)

def IsRatio {N : ℕ} {α : Q.X} (σ σ' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J

def IsRem {N : ℕ} {α : Q.X} (σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f g : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    sval σp (𝟙 _) z J = gs (𝟙 _) z U f * sval σp' (𝟙 _) z J + gs (𝟙 _) z U g * sval σ' (𝟙 _) z J

end GlobalTheory.HeatRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
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

namespace GlobalTheory.ChartKSBracket

theorem tanPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (u : TanM (𝟙 (Sp R)) Y.H), ∃ v' : TanM (𝟙 (Sp R)) t.G, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv u)) (tv v') := by
  intro E _ _ _ H R _ _ _ _ _ t P Y u
  letI := H.starRing
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hs : spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R)) := Category.comp_id _
  obtain ⟨x, hx, -⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ (tv u))
  obtain ⟨x₀, -, hu₀⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ 1)
  have h1 := hx.pull (homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R)))) (Y.rep.1 _ _ _ (tv u))
  have e : homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R))) ≫ tv u = 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem u
  rw [e] at h1
  have h2 := GlobalTheory.FormalPoint.isPointOf_one P.U.toUnifPre (GlobalTheory.ExpTan.isZero_one Y.rep (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R))))
  have hk : smT (𝟙 (Sp R)) 0 x = 1 := (hu₀ _ h1).trans (hu₀ _ h2).symm
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT x hk, hx⟩

theorem isTanAtG_tv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v' : TanM (𝟙 (Sp R)) t.G), IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv v').left) := by
  intro E _ _ _ H R _ t v'
  refine GlobalTheory.LieMet.isTan_map _ ?_ (GlobalTheory.LieMet.isTan_tv v')
  rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rfl

end GlobalTheory.ChartKSBracket
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

section General

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {n : ℕ}

def combF (dd : Fin n → Fld Z) (c : Fin n → R) : Fld Z :=
  fun W f => ∑ a, constFn s W (c a) * dd a W f

def quadF (dd : Fin n → Fld Z) (M : Matrix (Fin n) (Fin n) R) : Fld Z :=
  fun W f => ∑ a, ∑ b, constFn s W (M a b) * dd a W (dd b W f)

end General

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {Ω : Type} [CommRing Ω] [StarRing Ω] [Module Ω Q.X]
  {oa : Q.OAct Ω} (Y : Ray oa)

def IsTorField (F : Fld Y.H.left) (ℓ : Q.X → R) : Prop :=
  IsField ⊤ F ∧ (∀ W r, F W (constFn Y.H.hom W r) = 0) ∧
    (∀ (α : Q.X) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f →
      F W f = constFn Y.H.hom W (ℓ α) * f) ∧
    ∀ (U : Q.P.A.left.Opens) (g : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)),
      W ≤ Y.q.left ⁻¹ᵁ U → F W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * F W f

end Raynaud

end GlobalTheory.HeatMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSurjModP
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem lie_surj_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie),
      QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ O E _ _ _ hF G d c l
  obtain ⟨b, z, hbz, hl⟩ := GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow p O G l 1
  rw [pow_one] at hbz
  obtain ⟨f, s, y, hf, hs, hy⟩ := _root_.GlobalTheory.QLog.additive_mod_p_is_defect p O E hF G d c b z hbz
  obtain ⟨l', hl', -⟩ := _root_.GlobalTheory.QLog.Chart.existsUnique_isLie p O E hF G d c f hf
  have hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w := by
    intro w
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    have h1 := hl w φ hφ
    have h2 := hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)
    rw [pow_one] at h1 h2
    rw [hy, map_add (f := _), map_smul, smul_eq_mul] at h2
    have h3 : (p : O) ∣ l' w - φ b := by
      have := dvd_add h2 (dvd_mul_right (p : O) (φ y))
      rwa [show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring] at this
    have := dvd_sub h1 h3
    rwa [show l w - φ b - (l' w - φ b) = (l - l') w by simp] at this
  obtain ⟨l'', hl''⟩ := _root_.GlobalTheory.dual_eq_smul_of_forall_dvd O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv
  exact ⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩

end GlobalTheory.QLog
end

