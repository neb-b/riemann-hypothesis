module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem holFamily_of_affine
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (Z : Scheme.{0}) (c : E → (Sp ℂ ⟶ Z))
    (hc : ∀ w ∈ W, ∃ V : Z.Opens, IsAffineOpen V ∧ ⊤ ≤ c w ⁻¹ᵁ V ∧ IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∧
      ∀ g : Γ(Z, V), DifferentiableOn ℂ (fun w => valAt' (c w) V g) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by
  have hpt : ∀ (Y : Scheme.{0}) (x : Sp ℂ ⟶ Y) (O : Y.Opens),
      ⊤ ≤ x ⁻¹ᵁ O ↔ x (default : PrimeSpectrum ℂ) ∈ O := fun Y x O => (hv Y x).1 O

  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U}, ∃ N : Set E, IsOpen N ∧ w₀ ∈ N ∧
      N ⊆ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (c w) U f) N := by
    rintro w₀ ⟨hw₀, hU₀⟩
    obtain ⟨V, hVa, hV₀, hVo, hVd⟩ := hc w₀ hw₀
    obtain ⟨g, hgU, hg₀⟩ := hVa.exists_basicOpen_le (V := U)
      ⟨c w₀ (default : PrimeSpectrum ℂ), (hpt _ _ _).1 hU₀⟩ ((hpt _ _ _).1 hV₀)
    have hDV : Z.basicOpen g ≤ V := Z.basicOpen_le g
    let := hVa.isLocalization_basicOpen g
    obtain ⟨⟨h, ⟨_, n, rfl⟩⟩, hh⟩ := IsLocalization.surj (Submonoid.powers g) (resG Z hgU f)
    have hh' : resG Z hgU f * resG Z hDV g ^ n = resG Z hDV h := by
      rw [← map_pow]
      exact hh
    refine ⟨{w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ,
      (hVd g).continuousOn.isOpen_inter_preimage hVo isOpen_compl_singleton, ?_, ?_, ?_⟩
    · refine ⟨⟨hw₀, hV₀⟩, ?_⟩
      exact ((hv Z (c w₀)).2.2.2.2.1 V g).1 ((hpt _ _ _).2 hg₀)
    · rintro w ⟨⟨hw, -⟩, hg⟩
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg
      exact ⟨hw, (hpt _ _ _).2 (hgU ((hpt _ _ _).1 hD))⟩
    · have hq : DifferentiableOn ℂ (fun w => valAt' (c w) V h * (valAt' (c w) V g ^ n)⁻¹)
          ({w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ) :=
        by
        apply DifferentiableOn.fun_mul
        · exact (hVd h).mono Set.inter_subset_left
        · apply DifferentiableOn.fun_inv
          · exact ((hVd g).mono Set.inter_subset_left).fun_pow n
          · intro w hw
            exact pow_ne_zero _ hw.2
      refine hq.congr fun w ⟨⟨hw, hwV⟩, hg⟩ => ?_
      have hg' : valAt' (c w) V g ≠ 0 := hg
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg'
      obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hD
      have h1 := (hv Z (c w)).2.2.1 U _ hgU f hD
      have h2 := (hv Z (c w)).2.2.1 V _ hDV g hD
      have h3 := (hv Z (c w)).2.2.1 V _ hDV h hD
      rw [he] at h1 h2 h3
      have h4 := congrArg e hh'
      rw [map_mul, map_pow, h1, h2, h3] at h4
      rw [← div_eq_mul_inv]
      exact eq_div_of_mul_eq (pow_ne_zero _ hg') h4
  refine ⟨isOpen_iff_forall_mem_open.2 fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨N, hNo, hwN, hNs, -⟩ := key w hw
    exact ⟨N, hNs, hNo, hwN⟩
  · obtain ⟨N, hNo, hwN, -, hNd⟩ := key w hw
    exact (hNd.differentiableAt (hNo.mem_nhds hwN)).differentiableWithinAt

theorem holFamily_of_isPullback
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) {S X Y Z : Scheme.{0}} [IsAffine S]
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) (c : E → (Sp ℂ ⟶ Z))
    (ha : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U})
    (hb : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by
  have hpt : ∀ (T : Scheme.{0}) (x : Sp ℂ ⟶ T) (O : T.Opens),
      ⊤ ≤ x ⁻¹ᵁ O ↔ x (default : PrimeSpectrum ℂ) ∈ O := fun T x O => (hv T x).1 O
  refine holFamily_of_affine hv W Z c (fun w hw => ?_) U f
  obtain ⟨VX, hVXa, hVX₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (p (c w (default : PrimeSpectrum ℂ))))
  obtain ⟨VY, hVYa, hVY₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (q (c w (default : PrimeSpectrum ℂ))))
  have hSX : VX ≤ s ⁻¹ᵁ (⊤ : S.Opens) := le_top
  have hST : VY ≤ t ⁻¹ᵁ (⊤ : S.Opens) := le_top

  have hmem : ∀ x : Sp ℂ ⟶ Z, ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) ↔
      ⊤ ≤ (x ≫ p) ⁻¹ᵁ VX ∧ ⊤ ≤ (x ≫ q) ⁻¹ᵁ VY := by
    intro x
    show ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ VX) ⊓ x ⁻¹ᵁ (q ⁻¹ᵁ VY) ↔ _
    exact le_inf_iff
  have hPO := (isIso_pushoutSection_iff H hST hSX (UY := p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) rfl).1
    (isIso_pushoutSection_of_isAffineOpen H hST hSX rfl (isAffineOpen_top S) hVYa hVXa)
  have hVa : IsAffineOpen (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) := by
    have : IsAffine (⊤ : S.Opens) := isAffineOpen_top S
    have : IsAffine VY := hVYa
    have : IsAffine VX := hVXa
    exact .of_isIso (Scheme.Hom.isPullback_resLE H hST hSX rfl).isoPullback.hom

  have hNo : IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)} := by
    convert (ha VX 0).1.inter (hb VY 0).1 using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hmem]
    tauto

  let T : Subring Γ(Z, p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) :=
    { carrier := {g | DifferentiableOn ℂ (fun w => valAt' (c w) (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) g)
        {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)}}
      mul_mem' := fun {a b} ha' hb' => (ha'.fun_mul hb').congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_mul]
      one_mem' := (differentiableOn_const (1 : ℂ)).congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_one]
      add_mem' := fun {a b} ha' hb' => (ha'.fun_add hb').congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_add (f := _)]
      zero_mem' := (differentiableOn_const (0 : ℂ)).congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_zero]
      neg_mem' := fun {a} ha' => ha'.fun_neg.congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_neg] }

  have hXT : ∀ a : Γ(X, VX), (p.appLE VX (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_left).hom a ∈ T := by
    intro a
    change DifferentiableOn ℂ
      (fun w => valAt' (c w) (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)
        ((p.appLE VX (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_left).hom a)) _
    have hd : DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) VX a)
        {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ VX} := (ha VX a).2
    have hm : DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) VX a)
        {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)} :=
      hd.mono fun w hw => ⟨hw.1, ((hmem _).1 hw.2).1⟩
    refine hm.congr fun w hw => by
      change w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) at hw
      have h1 := (hv Z (c w)).2.2.1 (p ⁻¹ᵁ VX) _ inf_le_left ((p.app VX).hom a) hw.2
      have h2 := (hv Z (c w)).2.2.2.1 X p VX a
      exact h1.trans h2
  have hYT : ∀ b : Γ(Y, VY), (q.appLE VY (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_right).hom b ∈ T := by
    intro b
    change DifferentiableOn ℂ
      (fun w => valAt' (c w) (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)
        ((q.appLE VY (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_right).hom b)) _
    have hd : DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) VY b)
        {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ VY} := (hb VY b).2
    have hm : DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) VY b)
        {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)} :=
      hd.mono fun w hw => ⟨hw.1, ((hmem _).1 hw.2).2⟩
    refine hm.congr fun w hw => by
      change w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) at hw
      have h1 := (hv Z (c w)).2.2.1 (q ⁻¹ᵁ VY) _ inf_le_right ((q.app VY).hom b) hw.2
      have h2 := (hv Z (c w)).2.2.2.1 Y q VY b
      exact h1.trans h2

  let φX : Γ(X, VX) ⟶ CommRingCat.of T := CommRingCat.ofHom ((p.appLE VX _ inf_le_left).hom.codRestrict T hXT)
  let φY : Γ(Y, VY) ⟶ CommRingCat.of T := CommRingCat.ofHom ((q.appLE VY _ inf_le_right).hom.codRestrict T hYT)
  have hw' : s.appLE ⊤ VX hSX ≫ φX = t.appLE ⊤ VY hST ≫ φY := by
    ext x
    exact congrArg (fun k => k.hom x) hPO.w
  have hid : hPO.desc φX φY hw' ≫ CommRingCat.ofHom T.subtype = 𝟙 _ := by
    refine hPO.hom_ext ?_ ?_
    · rw [← Category.assoc, hPO.inl_desc, Category.comp_id]
      rfl
    · rw [← Category.assoc, hPO.inr_desc, Category.comp_id]
      rfl
  refine ⟨_, hVa, (hmem _).2 ⟨(hpt _ _ _).2 hVX₀, (hpt _ _ _).2 hVY₀⟩, hNo, fun g => ?_⟩
  have h1 := congrArg (fun k => k.hom g) hid
  have h2 : ((hPO.desc φX φY hw').hom g : Γ(Z, p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)) = g := h1
  rw [← h2]
  exact ((hPO.desc φX φY hw').hom g).2

theorem holFamily_lift :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) := by
  intro hv E _ _ W X Y a b ha hb U f

  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have hfa : ∀ w, (lift (a w) (b w)).left ≫ (fst X Y).left = (a w).left := fun w => by
    rw [← Over.comp_left, lift_fst]
  have hfb : ∀ w, (lift (a w) (b w)).left ≫ (snd X Y).left = (b w).left := fun w => by
    rw [← Over.comp_left, lift_snd]
  exact holFamily_of_isPullback hv W H (fun w => (lift (a w) (b w)).left)
    (fun U' f' => by simpa only [hfa] using ha U' f')
    (fun U' f' => by simpa only [hfb] using hb U' f') U f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ComplexPointsGroup

def IsContFamily {T : Type} [TopologicalSpace T] {X : Scheme.{0}} (e : T → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)) (O : Set ℂ), IsOpen O → IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ U ∧ valAt' (e t) U f ∈ O}

variable {T : Type} [TopologicalSpace T]

theorem IsContFamily.isOpen_mem {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens) :
    IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ U} := by
  simpa using he U 0 Set.univ isOpen_univ

theorem IsContFamily.continuousOn {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens)
    (f : Γ(X, U)) : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ U} :=
  (continuousOn_open_iff (he.isOpen_mem U)).2 fun O hO => he U f O hO

variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv

theorem IsContFamily.comp {X Y : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (φ : X ⟶ Y) :
    IsContFamily (fun t => e t ≫ φ) := by
  intro U f O hO
  have := he (φ ⁻¹ᵁ U) ((φ.app U).hom f) O hO
  simp only [(hv X _).2.2.2.1] at this
  exact this

theorem isContFamily_of_affine {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)}
    (h : ∀ t₀, ∃ P : X.Opens, IsAffineOpen P ∧ ⊤ ≤ e t₀ ⁻¹ᵁ P ∧ IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ P} ∧
      ∀ g : Γ(X, P), ContinuousOn (fun t => valAt' (e t) P g) {t | ⊤ ≤ e t ⁻¹ᵁ P}) :
    IsContFamily e := by
  intro U f O hO
  rw [isOpen_iff_forall_mem_open]
  rintro t₀ ⟨hU, hf⟩
  obtain ⟨P, hP, h₀, hopen, hcont⟩ := h t₀
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, ((hv X _).1 U).1 hU⟩ (((hv X _).1 P).1 h₀)
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen X P hP s (resG X hsU f)
  have key : ∀ t, ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s →
      valAt' (e t) U f = valAt' (e t) P g / valAt' (e t) P s ^ n := by
    intro t ht
    have hne := ((hv X (e t)).2.2.2.2.1 P s).1 ht
    obtain ⟨ev, hev⟩ := (hv X (e t)).2.1 _ ht
    have h1 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) g ht
    have h2 := (hv X (e t)).2.2.1 P _ (X.basicOpen_le s) s ht
    have h3 := (hv X (e t)).2.2.1 U _ hsU f ht
    have hg' : resG X (X.basicOpen_le s) g = resG X (X.basicOpen_le s) s ^ n * resG X hsU f := hg
    rw [eq_div_iff (pow_ne_zero n hne), ← h1, ← h2, ← h3, hg', hev, hev, hev, map_mul, map_pow, mul_comm]
  have hN : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} =
      {t | ⊤ ≤ e t ⁻¹ᵁ P} ∩ (fun t => valAt' (e t) P s) ⁻¹' {0}ᶜ := by
    ext t
    constructor
    · intro ht
      exact ⟨le_trans ht ((e t).preimage_mono (X.basicOpen_le s)), ((hv X (e t)).2.2.2.2.1 P s).1 ht⟩
    · intro ht
      exact ((hv X (e t)).2.2.2.2.1 P s).2 ht.2
  have hNo : IsOpen {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    rw [hN]
    exact (hcont s).isOpen_inter_preimage hopen isOpen_compl_singleton
  have hsub : {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ⊆ {t | ⊤ ≤ e t ⁻¹ᵁ P} := by
    rw [hN]; exact Set.inter_subset_left
  have hc : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} := by
    refine ContinuousOn.congr (f := fun t => valAt' (e t) P g / valAt' (e t) P s ^ n) ?_ key
    exact ((hcont g).mono hsub).div (((hcont s).mono hsub).pow n)
      fun t ht => pow_ne_zero n (((hv X (e t)).2.2.2.2.1 P s).1 ht)
  refine ⟨{t | ⊤ ≤ e t ⁻¹ᵁ X.basicOpen s} ∩ (fun t => valAt' (e t) U f) ⁻¹' O, ?_,
    hc.isOpen_inter_preimage hNo hO, ((hv X _).1 _).2 hs₀, hf⟩
  rintro t ⟨ht, hto⟩
  exact ⟨le_trans ht ((e t).preimage_mono hsU), hto⟩

theorem valAt'_appLE {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(Y, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((φ.appLE U V h).hom f) = valAt' (x ≫ φ) U f := by
  rw [← (hv X x).2.2.2.1, ← (hv X x).2.2.1 _ V h _ hx]
  rfl

theorem isContFamily_of_isPullback {X Y S Z : Scheme.{0}} [IsAffine S] {f : Y ⟶ S} {g : Z ⟶ X} {iX : X ⟶ S}
    {iY : Z ⟶ Y} (H : IsPullback g iY iX f) {e : T → (Sp ℂ ⟶ Z)}
    (h₁ : IsContFamily (fun t => e t ≫ g)) (h₂ : IsContFamily (fun t => e t ≫ iY)) : IsContFamily e := by
  refine isContFamily_of_affine hv fun t₀ => ?_
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (e t₀ ≫ g) (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤)
    (x := (e t₀ ≫ iY) (default : PrimeSpectrum ℂ)) trivial
  have hmem : ∀ t, ⊤ ≤ e t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) ↔ ⊤ ≤ (e t ≫ g) ⁻¹ᵁ U ∧ ⊤ ≤ (e t ≫ iY) ⁻¹ᵁ V := by
    intro t
    rw [Scheme.Hom.preimage_inf, le_inf_iff]
    rfl
  have hP : IsAffineOpen (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) := by
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    have : IsAffine _ := isAffineOpen_top S
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV hU)
  refine ⟨_, hP, (hmem t₀).2 ⟨((hv _ _).1 _).2 hpU, ((hv _ _).1 _).2 hpV⟩, ?_, fun r => ?_⟩
  · simp only [hmem]
    exact (h₁.isOpen_mem U).inter (h₂.isOpen_mem V)
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ((h₁.continuousOn U a).mono fun t ht => ((hmem t).1 ht).1).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
    · exact ((h₂.continuousOn V b).mono fun t ht => ((hmem t).1 ht).2).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
  | zero =>
    refine (continuousOn_const (c := (0 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_zero]
  | one =>
    refine (continuousOn_const (c := (1 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_one]
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_add (f := _), Pi.add_apply]
  | neg x _ hx =>
    refine hx.neg.congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_neg, Pi.neg_apply]
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_mul, Pi.mul_apply]


omit hv in
theorem continuous_iff_isContFamily {A : Over (Sp ℂ)} (e : T → (𝟙_ (Over (Sp ℂ)) ⟶ A)) :
    Continuous[_, TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}] e ↔
      IsContFamily (X := A.left) (fun t => (e t).left) := by
  rw [continuous_generateFrom_iff]
  constructor
  · intro h U f O hO
    exact h _ ⟨U, f, O, hO, rfl⟩
  · rintro h _ ⟨U, f, O, hO, rfl⟩
    exact h U f O hO

theorem isContFamily_lift {A B : Over (Sp ℂ)} {a : T → (𝟙_ (Over (Sp ℂ)) ⟶ A)} {b : T → (𝟙_ (Over (Sp ℂ)) ⟶ B)}
    (ha : IsContFamily (X := A.left) (fun t => (a t).left)) (hb : IsContFamily (X := B.left) (fun t => (b t).left)) :
    IsContFamily (X := (A ⊗ B).left) (fun t => (lift (a t) (b t)).left) := by
  have H : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback A.hom B.hom
  refine isContFamily_of_isPullback hv H ?_ ?_
  · convert ha using 2 with t
    exact congrArg CommaMorphism.left (lift_fst (a t) (b t))
  · convert hb using 2 with t
    exact congrArg CommaMorphism.left (lift_snd (a t) (b t))

end GlobalTheory.ComplexPointsGroup

namespace GlobalTheory


open ComplexPointsGroup in
theorem isTopologicalGroup_complexPoints :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp ℂ)) [GrpObj A], @IsTopologicalGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) (TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}) _) := by
  intro hv A _
  let : TopologicalSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ A) | ∃ (U : A.left.Opens) (f : Γ(A.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
  have hmul : ContinuousMul (𝟙_ (Over (Sp ℂ)) ⟶ A) := ⟨by
    refine (continuous_iff_isContFamily _).2 ?_
    exact (isContFamily_lift hv ((continuous_iff_isContFamily _).1 continuous_fst)
      ((continuous_iff_isContFamily _).1 continuous_snd)).comp hv μ[A].left⟩
  have hinv : ContinuousInv (𝟙_ (Over (Sp ℂ)) ⟶ A) := ⟨by
    refine (continuous_iff_isContFamily _).2 ?_
    exact ((continuous_iff_isContFamily _).1 continuous_id).comp hv (GrpObj.inv (X := A)).left⟩
  exact {}

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.KrullDimLEAndIsLocalRingQuotientPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace ArtinReduction

theorem eq_zero_of_forall_mem_pow {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (hy : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  first
  | exact @_root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
  | exact _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
  | (apply _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> assumption)
  | (intros; apply _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal ..)

theorem krullDimLE_and_isLocalRing_quotient_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  have hJt : m ^ (n + 1) ≠ ⊤ := fun h => hm.ne_top
    (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 hJt
  have key : ∀ P : Ideal (R ⧸ m ^ (n + 1)), P.IsPrime →
      P = m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
    intro P hP
    have hc : (P.comap (Ideal.Quotient.mk (m ^ (n + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h1 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (n + 1))) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm.trans
      (congrArg _ (hm.eq_of_le hc.ne_top h1).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (R ⧸ m ^ (n + 1))
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ m ^ (n + 1))).out 2 1 rfl rfl).mp
    ⟨P, hP.isPrime, fun Q hQ => (key Q hQ).trans (key P hP.isPrime).symm⟩

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (q : T' ⟶ T) (x : T ⟶ A)
    (h : ∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) :
    ∃ c : LB.Gen (Out.translDiff A L (q ≫ x)), c.IsGen := by
  obtain ⟨c, hc⟩ := h
  have h4 : ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) (fun i => (q ▷ A).left ≫
      ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] i) ![1, -1]), w.IsGen :=
    ⟨_, DVR.pullGen_isGen _ _ _ c hc _⟩
  have h3 : (fun i => (q ▷ A).left ≫
      ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] i) =
      ![(lift (fst T' A ≫ q ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext i
    fin_cases i
    · change (q ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ q ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (q ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

end ArtinReduction


open ArtinReduction in
theorem translDiff_triv_of_artin_local :
    (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing R] [Algebra ℂ R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) := by
  intro A _ L hA _ h R _ _ hR x hx
  have := hA.proper
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  refine TorusLocal.pt_ext_of_quotients (A := ℂ) (C := R)
    (fun i : MaximalSpectrum R × ℕ => i.1.asIdeal ^ (i.2 + 1)) eq_zero_of_forall_mem_pow
    (B := A) fun i => ?_
  have := i.1.isMaximal
  obtain ⟨h1, h2⟩ := krullDimLE_and_isLocalRing_quotient_pow i.1.asIdeal i.2
  have h3 : Module.Finite ℂ (R ⧸ i.1.asIdeal ^ (i.2 + 1)) :=
    (Module.finite_iff_krullDimLE_zero ℂ _).2 h1
  exact (h _ h2 h3 _ (exists_isGen_translDiff_comp A L _ x hx)).trans (MonObj.comp_one _).symm

end GlobalTheory
end

