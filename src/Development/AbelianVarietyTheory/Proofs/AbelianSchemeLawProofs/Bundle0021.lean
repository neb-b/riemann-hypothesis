module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeOfSumEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EndDivisible

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace

def germPull {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) :
    Γ(Y, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem germPull_apply {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    germPull r z U h a = gs r z U a := (gs_eq r z U h a).symm

theorem gs_appLE {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens)
    (hle : V ≤ r ⁻¹ᵁ U) (h : f z ∈ V) (a : Γ(X, U)) :
    gs f z V ((r.appLE U V hle).hom a) = gs (f ≫ r) z U a :=
  (gs_res f z hle h _).trans (gs_pull f r z U (hle h) a)

theorem exists_factor {X W Y S : Scheme.{0}} [IsIntegral X] [Y.IsSeparated] [IsAffine S] (f : X ⟶ W)
    (w : W ⟶ Y) (g : X ⟶ S) (hS : IsField Γ(S, ⊤)) (D : W.Opens) (hD : IsAffineOpen D) (z : X) (hz : f z ∈ D)
    (h : ∀ a : Γ(W, D), ∃ c : Γ(S, ⊤), gs g z ⊤ c = gs f z D a) : ∃ p : S ⟶ Y, f ≫ w = g ≫ p := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVD⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ ((f ⁻¹ᵁ D : X.Opens) : Set X) from hz)
      (f ⁻¹ᵁ D).isOpen
  have hVD' : V ≤ f ⁻¹ᵁ D := hVD
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  let κ := (g.appLE ⊤ V le_top).hom
  let φ := (f.appLE D V hVD').hom
  have hκ : Function.Injective κ := by
    letI := hS.toField
    exact κ.injective
  have hr : ∀ a, φ a ∈ κ.range := fun a => by
    obtain ⟨c, hc⟩ := h a
    refine ⟨c, germ_injective_of_isIntegral X z hzV ?_⟩
    refine (gs_eq (𝟙 X) z V hzV _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X) z V hzV _))
    refine (gs_appLE (𝟙 X) g z ⊤ V le_top hzV c).trans
      (Eq.trans ?_ (gs_appLE (𝟙 X) f z D V hVD' hzV a).symm)
    rw [Category.id_comp, Category.id_comp, hc]
  let e : Γ(S, ⊤) ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b hab => hκ (congrArg Subtype.val hab), κ.rangeRestrict_surjective⟩
  let χ : Γ(W, D) ⟶ Γ(S, ⊤) := CommRingCat.ofHom (e.symm.toRingHom.comp (φ.codRestrict κ.range hr))
  have hχ : f.appLE D V hVD' = χ ≫ g.appLE ⊤ V le_top := by
    ext a
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hr a⟩)).symm
  refine ⟨S.isoSpec.hom ≫ Spec.map χ ≫ hD.fromSpec ≫ w, ?_⟩
  have : IsDominant hV.fromSpec := ⟨by
    rw [DenseRange, hV.range_fromSpec]
    exact V.isOpen.dense ⟨z, hzV⟩⟩
  refine ext_of_isDominant hV.fromSpec ?_
  rw [← Category.assoc, ← hD.SpecMap_appLE_fromSpec f hV hVD', ← Category.assoc hV.fromSpec,
    ← (isAffineOpen_top S).SpecMap_appLE_fromSpec g hV le_top, hχ, IsAffineOpen.fromSpec_top]
  simp

theorem exists_monomials {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (t : ℕ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(t : ℤ), -1])) (hα : α.IsGen)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w ≫ m) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    ∃ b : (Z.presheaf.stalk z)ˣ, ∀ a ≤ t,
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => (N : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) * b.val := by
  obtain ⟨β, hβ⟩ : ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k)
      (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)), β.IsGen :=
    exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hα (f ≫ w)) _
  refine ⟨val β (𝟙 Z) z J, fun a ha => ?_⟩
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N ⊕ Fin 2)
      (Sum.elim (fun _ => f ≫ w) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k))
      (Sum.elim (fun _ => 1) (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)) (fun _ : Unit => u) (fun _ => (N : ℤ)) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, hu]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      Category.assoc, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha]
    rw [← _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
    simp [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullMulSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f β hβ)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp

theorem mem_range_of_sum_eq_zero {K R : Type} [Field K] [IsAlgClosed K] [CommRing R] [IsDomain R]
    (κ : K →+* R) {n : ℕ} (c : Fin n → K) (hc : c ≠ 0) (x : R) (h : ∑ k, κ (c k) * x ^ (k : ℕ) = 0) :
    x ∈ κ.range := by
  let p : Polynomial K := ∑ k : Fin n, Polynomial.monomial (k : ℕ) (c k)
  have hp : p ≠ 0 := fun h0 => hc (funext fun k => by
    have := congrArg (fun q : Polynomial K => q.coeff k) h0
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Fin.val_inj,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Polynomial.coeff_zero] at this
    exact this)
  refine (IsAlgClosed.splits p).mem_range_of_isRoot hp ?_
  rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_finsetSum]
  simpa [Polynomial.eval₂_monomial] using h

theorem eq_one_of_forall_pow_dvd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (q : ℕ), 2 ≤ q → ∀ u : P.A ⟶ P.A, (∀ k : ℕ, ∃ ψ : P.A ⟶ P.A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1 := by
  intro hGI hmul hfin K _ _ P q hq u hu
  have := P.isAb.proper
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from P.A.hom]; infer_instance⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, -, M, s, hcov, hs⟩ := P.ample ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := hfin K P _ (DVR.linComb_isLB P.L P.isLB (K := Unit) (fun _ => u.left) (fun _ => (N : ℤ)))
  obtain ⟨ψ, hψ, hu⟩ := hu n
  have H := hmul _ P (q ^ n)
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have hnt : n ≤ (q ^ n) ^ 2 := (Nat.lt_pow_self hq).le.trans (Nat.le_self_pow two_ne_zero _)
  let w := (P.A.hom ⁻¹ᵁ ⊤).ι
  let f : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  have hu' : u.left = f ≫ w ≫ (mulA P.A (q ^ n)).left := by
    rw [← Category.assoc, hf, ← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, hu]
  obtain ⟨z⟩ : Nonempty P.A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good P.L z J := by
    choose I hI using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ z)
    exact ⟨I, hI⟩
  let κ := germPull P.A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver P.A P.L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    obtain ⟨b, hb⟩ := exists_monomials P.L P.isLB w N (s i) (s j) _ _ α hα f u.left hu' z J hJ
    choose σ hσ using fun a : Fin n => hb a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn σ
    have hm := hJ.mem (K := Unit) (fun _ => u.left) (𝟙 _)
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (fun _ => J (𝟙 _ ≫ u.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (E (c k)) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ ((q ^ n) ^ 2) * b.val) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) P.A.hom z ⊤ _ le_top hm (c k)) (hσ k)).symm
      have e₁ : (κ.comp E.symm.toRingHom) (E (c k)) = gs (𝟙 _ ≫ P.A.hom) z ⊤ (c k) := by
        rw [Category.id_comp]
        exact (congrArg κ (E.symm_apply_apply _)).trans (germPull_apply _ _ _ _ _)
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) (fun k => E (c k))
      (fun h => hc (funext fun k => E.injective ((congrFun h k).trans (map_zero E).symm))) (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right ((hy.pow _).mul b.isUnit).ne_zero)
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w P.A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have h2 : η[P.A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  have h3 : ψ = 1 := by
    apply Over.OverMorphism.ext
    rw [hp, ← h2, Hom.one_def]
    simp
  rw [hu, h3, one_pow]

end GlobalTheory.EndDivisible
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlobalLift

open CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem weilIs_of_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k θx θy c) : WeilIs A L k θx.pt θy.pt c := by
  intro p
  obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
  exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
    commIsOf_change hG hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

theorem weilIs_iff_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k θx.pt θy.pt c ↔ CommIsOf A L k θx θy c := by
  refine ⟨fun H => ?_, weilIs_of_commIsOf hG hA hL⟩
  obtain ⟨c₀, h₀⟩ := CommutatorPairing.exists_commIsOf hG hA hL θx θy
  rw [CommutatorPairing.weilIs_unique hG hA hL H (weilIs_of_commIsOf hG hA hL h₀)]
  exact h₀

theorem val_powGen {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ i : Fin n, tval θ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J := by
  refine Eq.trans (map_prod (gm r z (LB.wchart L (powφ A θ.pt n) fun b => J (r ≫ powφ A θ.pt n b))) _
    (Finset.univ : Finset (Fin n))) ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans (val_pull hJ
    (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ _ r)

def nval {T : Over S} (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J

theorem val_symGen {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J * nval ν r z J) *
      (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg (· * nval ν r z J) (val_pull hJ _ _ _)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))

theorem exists_neg_pull (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T) (ν : LB.Gen (negLB A L k T)) (hν : ν.IsGen) :
    ∃ ν' : LB.Gen (negLB A L k T'), ν'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J),
      Good L z J → nval ν' r z J = nval ν (r ≫ (h ▷ A).left) z J := by
  have e₀ : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  have e₁ : (h ▷ A).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, whiskerRight_snd_assoc]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left])
    (ε' := ![k, -k])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ k) e₀
      · exact congrArg (fun q => f q ^ (-k)) e₁)
    (LB.pullGen L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] ν (h ▷ A).left)
    (DVR.pullGen_isGen _ _ _ _ hν _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem whisker_negT {T T' : Over S} (h : T' ⟶ T) : negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [negT]
  · simp [negT]

theorem exists_symLift_pull (hL : L.IsLB) {n : ℕ} {T T' : Over S} (h : T' ⟶ T) {x : T ⟶ A} {θ : ThetaGrp A L k T}
    (H : SymLift A L k n x θ) : ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' := by
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  obtain ⟨θ', e, v⟩ := exists_pull hL h θ
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have t : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left) (x : T ⟶ A), (r ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (translT A x).left := fun r x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have u : ∀ (r : (T' ⊗ A).left ⟶ (T' ⊗ A).left), (r ≫ (negT A T').left) ≫ (h ▷ A).left =
      (r ≫ (h ▷ A).left) ≫ (negT A T).left := fun r => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_negT]
  refine ⟨θ', e, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩
  · have q := val_corr hJ hp (𝟙 _ ≫ (h ▷ A).left)
    rw [val_powGen _ _ _ hJ, val_one] at q ⊢
    refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
    rw [v _ _ y J hJ, e, ← MonObj.comp_pow, t]
  · have q := val_corr hJ hs (𝟙 _ ≫ (h ▷ A).left)
    rw [val_symGen _ _ _ hJ, val_one] at q ⊢
    rw [v _ _ y J hJ, v _ _ y J hJ, w _ _ y J hJ, w _ _ y J hJ, e, ← GrpObj.comp_inv, t, u]
    exact q

theorem exists_symLift_empty (hL : L.IsLB) (n : ℕ) {T : Over S} [IsEmpty T.left] (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k n x θ := by
  have he : ∀ {Q : Prop} (_ : (T ⊗ A).left), Q := fun y => isEmptyElim ((fst T A).left y)
  exact ⟨⟨x, ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y⟩, rfl, corr_of_val hL fun y _ _ => he y,
    ⟨fun _ => 1⟩, fun _ _ => unit_ext fun y _ => he y, corr_of_val hL fun y _ _ => he y⟩


omit [GrpObj A] in
theorem exists_section {T : Over S} [Subsingleton T.left] {V : T.left.Opens} {p : T.left} (hp : p ∈ V) :
    ∃ h : T ⟶ overRes V, h ≫ overResι V = 𝟙 T := by
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]
  exact ⟨Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]), Over.OverMorphism.ext T.left.toIso_inv_ι⟩

end GlobalTheory.GlobalLift

namespace GlobalTheory


open GlobalLift in
theorem weilIs_iff_commIsOf_and_lift_subsingleton : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧ ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' → LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ)) := by
  intro hG hlift hsym S P k T
  refine ⟨weilIs_iff_commIsOf hG P.isAb P.isLB, fun x hx hT => ?_⟩
  rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
  · obtain ⟨θ, H⟩ := exists_symLift_empty (k := (k : ℤ)) P.isLB k x
    exact ⟨θ, H.pt_eq, fun _ => H⟩
  by_cases hk : Odd k
  · obtain ⟨V, hp, θ, H⟩ := (hsym S P k hk T x hx).1 p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', H'⟩ := exists_symLift_pull P.isLB h H
    rw [← Category.assoc, e, Category.id_comp] at H'
    exact ⟨θ', H'.pt_eq, fun _ => H'⟩
  · obtain ⟨V, hp, θ, H⟩ := hlift S P k T x hx p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', e', -⟩ := CommPairing.exists_pull P.isLB h θ
    rw [H, ← Category.assoc, e, Category.id_comp] at e'
    exact ⟨θ', e', fun h => absurd h hk⟩

end GlobalTheory
end
end

