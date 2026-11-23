module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isGen_pull {X Y : Scheme.{0}} (M : LB X) (v : LB.Gen M) (hv : v.IsGen) (f : Y ⟶ X) :
    ∃ c : LB.Gen (M.pull f), c.IsGen := by
  have le : ∀ J : PUnit → M.ι, (M.pull f).U J ≤ f ⁻¹ᵁ M.U (J PUnit.unit) := fun J y hy => mem_pull.1 hy
  refine ⟨⟨fun J => res (le J) (pullU f _ (v.s (J PUnit.unit)))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J : PUnit → M.ι, y ∈ (M.pull f).U J →
      gm (𝟙 Y) y _ (res (le J) (pullU f _ (v.s (J PUnit.unit)))) =
        gm (𝟙 Y ≫ f) y _ (v.s (J PUnit.unit)) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  have hm : (𝟙 Y ≫ f) y ∈ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gm (𝟙 Y ≫ f) y _) (hv (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at e
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))

theorem exists_isGen_of_invariant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y'))
    (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, φ' k = m ≫ φ k)
    (u : LB.Gen (LB.LinComb L φ' ε)) (hu : u.IsGen)
    (hinv : ∀ i y J, Good L y J → val u (t i) y J = val u (𝟙 Y') y J) :
    ∃ v : LB.Gen (LB.LinComb L φ ε), v.IsGen := by
  obtain rfl : φ' = fun k => m ≫ φ k := funext hφ
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have le : ∀ j : K → L.ι, m ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => m ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hex : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j)ˣ, pullU m _ b = res (le j) (u.s j) := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    have hJ' : Good L y J := hJ
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ LB.wchart L φ j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    refine (gm_res (t i) y (le j) (e hy) _).trans (Eq.trans ?_ (gm_res (𝟙 Y') y (le j) hy _).symm)
    refine (gen_trans hu (t i) y (le j (e hy)) (hJ'.mem _ _)).trans
      (Eq.trans ?_ (gen_trans hu (𝟙 Y') y (le j hy) (hJ'.mem _ _)).symm)
    refine congrArg₂ (· * ·) ?_ (hinv i y J hJ')
    have e3 : ∀ k, t i ≫ m ≫ φ k = 𝟙 Y' ≫ m ≫ φ k := fun k => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X => gm ψ y (L.U (j k) ⊓ L.U (J ψ)) (L.g (j k) (J ψ)) ^ ε k) (e3 k)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j : K → L.ι, y ∈ m ⁻¹ᵁ LB.wchart L φ j →
      gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (u.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans ((congrArg _ (hb j)).trans (gm_res (𝟙 Y') y (le j) hj _))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans
    ((gen_trans hu (𝟙 Y') y (le i hy.1) (le j hy.2)).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_linComb L φ ε (𝟙 Y' ≫ m) y i j hy.1 hy.2).trans ?_) ((gm_res _ y _ hy _).trans (val j hy.2)))
  simp only [trF, Category.assoc]

theorem weilNondeg_of_descent :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε)))) → WeilNondegSt := by
  intro hG hC K _ _ P k hk x hx hy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, ε, hu, -, hcorr⟩ := hC K P k x hx
  let B := baseOver (Spec (CommRingCat.of K))
  let β : P.A ⟶ B := Over.homMk P.A.hom (Category.comp_id _)
  have hβ : ∀ {T : Over (Spec (CommRingCat.of K))} (a b : T ⟶ B), a = b := fun a b =>
    Over.OverMorphism.ext (((Category.comp_id _).symm.trans (Over.w a)).trans
      ((Category.comp_id _).symm.trans (Over.w b)).symm)
  let σ : P.A ⟶ B ⊗ P.A := lift β (𝟙 _)
  have hσ : snd B P.A ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ]
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ P.A), y ≫ mulA P.A k = y ^ k :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have h0 : σ ≫ mulT P.A B k = mulA P.A k ≫ σ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ, mulT, mulA, MonObj.comp_pow]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(σ ≫ translPt P.A x).left, 𝟙 _] ![1, -1] (mulA P.A k).left
    (I := {y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A // y ^ k = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul, mulA])
    (fun U f hf => hG K P k hk U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change (σ ≫ mulT P.A B k ≫ translPt P.A x).left = (mulA P.A k ≫ σ ≫ translPt P.A x).left
        rw [reassoc_of% h0]
      · change (σ ≫ snd B P.A ^ k).left = (mulA P.A k ≫ 𝟙 _).left
        simp [σ, mulA, MonObj.comp_pow])
    (LB.pullGen P.L _ _ u σ.left) (DVR.pullGen_isGen _ _ _ u hu _)
    (fun y z J hJ => by
      have hy' : (toUnit B ≫ y.1) ^ k = 1 := by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      have h1 := val_corr hJ (hcorr _ 1 hy' (hy _ hy')) σ.left
      have h2 : ((toUnit P.A ≫ y.1) * 𝟙 P.A) ≫ σ = σ ≫ translT P.A (toUnit B ≫ y.1) := by
        apply CartesianMonoidalCategory.hom_ext
        · exact hβ _ _
        · clear hG hC hcorr h1
          simp only [σ, translT, translPt, Hom.mul_def, Category.assoc, lift_snd, Category.comp_id,
            comp_lift_assoc, lift_fst_assoc, comp_toUnit_assoc]
      rw [val_pull hJ, val_mul hJ, one_zpow] at h1
      rw [val_pull hJ, val_pull hJ, Category.id_comp, ← Over.comp_left, h2]
      refine h1.trans ?_
      refine mul_eq_left.2 ?_
      exact (congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans (map_one _))
  refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
  have h3 : (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) =
      ![(translPt P.A x).left, (snd B P.A).left] := by
    funext i
    fin_cases i
    · change (snd B P.A ≫ σ ≫ translPt P.A x).left = (translPt P.A x).left
      rw [reassoc_of% hσ]
    · exact Category.comp_id _
  have h4 : ∃ w : LB.Gen (LB.LinComb P.L
      (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) ![1, -1]), w.IsGen :=
    ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
  rw [h3] at h4
  obtain ⟨w, hw⟩ := h4
  exact exists_isGen_pull (translDiff P.A P.L x) w hw _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtend

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DvrModel

theorem gm_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r')) (z : Z)
    (a : I → L.ι) (ha : r z ∈ LB.wchart L φ a) (ha' : r' z ∈ LB.wchart L φ' a) :
    gm r z (LB.wchart L φ a) (t.s a) = gm r' z (LB.wchart L φ' a) (t'.s a) := by
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hv := val_corr hJ hc (𝟙 Z)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at hv
  rw [gen_trans ht r z ha (Good.mem hJ φ r), gen_trans ht' r' z ha' (Good.mem hJ φ' r')]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) hv
  show gm (r ≫ φ k) z (L.U (a k) ⊓ L.U (J (r ≫ φ k))) (L.g (a k) (J (r ≫ φ k))) ^ _ =
    gm (r' ≫ φ' k) z (L.U (a k) ⊓ L.U (J (r' ≫ φ' k))) (L.g (a k) (J (r' ≫ φ' k))) ^ _
  rw [h k]

theorem res_pullU_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r'))
    (a : I → L.ι) {A : Z.Opens} (hA : A ≤ r ⁻¹ᵁ LB.wchart L φ a)
    (hA' : A ≤ r' ⁻¹ᵁ LB.wchart L φ' a) :
    r'.appLE (LB.wchart L φ' a) A hA' (LB.ts t' a : Γ(Y', LB.wchart L φ' a)ˣ) =
      r.appLE (LB.wchart L φ a) A hA (LB.ts t a : Γ(Y, LB.wchart L φ a)ˣ) := by
  have hur : res hA' (pullU r' (LB.wchart L φ' a) (t'.s a)) =
      res hA (pullU r (LB.wchart L φ a) (t.s a)) := by
    refine unit_ext fun z hz => ?_
    rw [gm_res _ z hA hz, gm_res _ z hA' hz, gm_pull _ r z _ (hA hz), gm_pull _ r' z _ (hA' hz),
      Category.id_comp, Category.id_comp]
    exact (gm_eq_of_corr hL ht ht' r r' h hc z a (hA hz) (hA' hz)).symm
  exact congrArg Units.val hur

theorem existsUnique_gen_extend :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t := by
  intro V _ _ _ K _ _ _ H X p e hsm hgi he eK heK L hL I _ φ ε t ρ ht hρ hc
  have hK := IsPullback.of_hasPullback p (etaK V K)
  have hs := IsPullback.of_hasPullback p
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := isIntegral_of_geometricallyIntegral hK
  have := isIntegral_of_geometricallyIntegral hs
  have hcomp : ∀ i, eK ≫ pullback.fst p (etaK V K) ≫ φ i = etaK V K ≫ e ≫ φ i := fun i => by
    rw [← Category.assoc, heK, Category.assoc]
  obtain ⟨a₀, h₀⟩ := LB.mem_of_cover (LB.isLB_linComb hL (fun i => e ≫ φ i) ε)
    (IsLocalRing.closedPoint V)
  have hA' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ =
      etaK V K ⁻¹ᵁ LB.wchart L (fun i => e ≫ φ i) a₀ := wchart_comp L _ _ _
  have hA'' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ ≤
      eK ⁻¹ᵁ LB.wchart L (fun i => pullback.fst p (etaK V K) ≫ φ i) a₀ := by
    rw [← wchart_comp, funext hcomp]
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := LB.wchart L φ) (g := fun a b ↦ LB.lcg L φ ε a b)
    (W := LB.wchart L fun k ↦ pullback.fst p (etaK V K) ≫ φ k)
    (wchart_comp L _ φ) (LB.mem_of_cover (LB.isLB_linComb hL φ ε)) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ LB.ts t a)
    (fun a b ↦ by
      have := congrArg Units.val ((LB.isGen_iff L t).1 ht a b)
      rw [LB.lcg_comp] at this
      exact this)
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := LB.wchart L (fun i => e ≫ φ i) a₀) h₀
    (wchart_comp L e φ a₀).le hA' hA'' (LB.ts ρ a₀).isUnit
    (res_pullU_eq_of_corr hL ht hρ eK (etaK V K) hcomp hc a₀ hA'' hA'.le)
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr a))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ (r' a).val) ⟨fun a ↦ Units.isUnit _,
      fun a b ↦ congrArg Units.val (h₁ a b), fun a ↦ congrArg (fun c ↦ (LB.ts c a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))

end GlobalTheory.GenExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EvVal

theorem existsUnique_sec_eq_mul_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (s : LB.Sec M) (t : LB.Gen M) (ht : t.IsGen) :
    ∃! v : Γ(Y, ⊤), ∀ j, s.f j =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom v * (t.s j).val := by
  obtain ⟨v, hv⟩ := TLinPf.glue M.U hc (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e := congrArg (fun x : Γ(Y, M.U i ⊓ M.U j)ˣ => (x⁻¹).val) (ht i j)
    simp only [mul_inv, ← map_inv, Units.val_mul] at e
    rw [map_mul, map_mul, s.compat i j]
    refine (congrArg (_ * ·) e).trans ?_
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]
    rfl)
  refine ⟨v, fun j => ?_, fun w hw => TLinPf.eq_local M.U hc _ _ fun j => ?_⟩
  · rw [hv j, Units.inv_mul_cancel_right]
  · rw [hv j, hw j, Units.mul_inv_cancel_right]

def pullSec {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (ψ : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = ψ k)
    (le : ∀ j, LB.wchart L ψ j ≤ h ⁻¹ᵁ LB.wchart L φ j) (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb L ψ ε) where
  f := fun j => (Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))
  compat := fun (j j' : K → L.ι) => Geo.Tor.fn_ext fun y hy => by
    have v : ∀ j : K → L.ι, y ∈ LB.wchart L ψ j →
        Geo.Tor.gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))) =
        Geo.Tor.gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
      (Geo.Tor.gs_res _ y _ hj _).trans (Geo.Tor.gs_pull _ h y _ (le j hj) _)
    refine ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_
      ((Geo.Tor.gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (Geo.Tor.gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2)))
        ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
    rw [Geo.Tor.sec_trans s (𝟙 Y' ≫ h) y (le j hy.1) (le j' hy.2)]
    simp only [Geo.Tor.trF, Category.assoc, e]

theorem powFrame_isGen {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S}
    (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem evValSt : ∀ S : Scheme.{0}, EvValSt (S := S) := by
  intro S P N T z e he s
  exact existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover P.L P.isLB _ _)
    (pullSec P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => (N : ℤ)) (ptSecT P.A z).left
      (fun _ => z.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le P.A P.L z) s)
    (powFrame P.A P.L z e N) (powFrame_isGen P.A P.L z e he N)

end GlobalTheory.EvVal
end
end

