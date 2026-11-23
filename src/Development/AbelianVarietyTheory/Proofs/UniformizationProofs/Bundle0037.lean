module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

private theorem isCub_mul_swap_middle {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (a b c d y : A) :
    θ a b y * θ (a * b) (c * d) y * θ c d y = θ (a * c) (b * d) y * θ a c y * θ b d y := by
  have e1 : θ a b y * θ (a * b) (c * d) y = θ a (b * (c * d)) y * θ b (c * d) y := by
    rw [_root_.mul_comm]; exact h.coc a b (c * d) y
  have e2 : θ b (c * d) y * θ c d y = θ (b * c) d y * θ b c y := (h.coc b c d y).symm
  have e3 : θ (a * c) (b * d) y * θ a c y = θ a (c * (b * d)) y * θ c (b * d) y := h.coc a c (b * d) y
  have e4 : θ c (b * d) y * θ b d y = θ (c * b) d y * θ c b y := (h.coc c b d y).symm
  rw [e1, _root_.mul_assoc, e2, e3, _root_.mul_assoc, e4, _root_.mul_comm c b, h.s01 c b, mul_left_comm c b d]

private theorem v_sub_one_add_le_v_pow_l_sub_one {U : Type} [CommGroup U] {P B C D Px Px' D' E F : U} {k : ℕ}
    (ih : P * C ^ k = D * Px * Px') (e : D * B * C = D' * E * F) :
    P * B * C ^ (k + 1) = D' * (Px * E) * (Px' * F) := by
  calc P * B * C ^ (k + 1) = (P * C ^ k) * (B * C) := by rw [pow_succ]; ac_rfl
    _ = Px * Px' * (D * B * C) := by rw [ih]; ac_rfl
    _ = D' * (Px * E) * (Px' * F) := by rw [e]; ac_rfl

theorem cubN_mul_left {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ)
    (x x' y : A) :
    cubN θ k 1 (x * x') y * θ x x' y ^ k = θ (x ^ k) (x' ^ k) y * cubN θ k 1 x y * cubN θ k 1 x' y := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ x, pow_succ x', mul_pow x x' k]
    exact v_sub_one_add_le_v_pow_l_sub_one ih (isCub_mul_swap_middle h (x ^ k) (x' ^ k) x x' y)

private theorem gm_id_global_mul {X : Scheme.{0}} (z : X) (a b : Γ(X, ⊤)ˣ) :
    gm (𝟙 X) z ⊤ (a * b) = gm (𝟙 X) z ⊤ a * gm (𝟙 X) z ⊤ b :=
  map_mul _ a b

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}

theorem CubWeil.mul_left {ζ ζ' : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : CubWeil c N x' y ζ') :
    CubWeil c N (x * x') y (ζ * ζ') := by
  obtain ⟨hx, hy, hv⟩ := h
  obtain ⟨hx', -, hv'⟩ := h'
  refine ⟨by rw [mul_pow, hx, hx', _root_.one_mul], hy, fun z J hJ => ?_⟩
  have hc := isCub_cubV c hJ
  have e1 := cubN_mul_left hc N x x' y
  rw [hx, hx', hc.face, _root_.one_mul, hc.s12 x x' y, hc.s01 x y x'] at e1
  have e2 := hc.N_add N 1 y x x'
  simp only [hc.face, _root_.one_mul, _root_.mul_one, hy] at e2
  apply mul_right_cancel (b := cubV c z J y x x' ^ N)
  rw [gm_id_global_mul, _root_.mul_assoc, e1, e2, ← hv z J hJ, ← hv' z J hJ]
  exact mul_mul_mul_comm _ _ _ _

theorem cubWeil_one_left (c : CubicalStr G L) (hy : y ^ N = 1) : CubWeil c N 1 y 1 := by
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil (x := (1 : T ⟶ G)) c (one_pow N) hy
  have h2 := hζ.mul_left hζ
  rw [_root_.one_mul] at h2
  have e : ζ * ζ = ζ * 1 := by rw [_root_.mul_one]; exact h2.unique hζ
  rw [mul_left_cancel e] at hζ
  exact hζ

theorem CubWeil.pow_left {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (n : ℕ) : CubWeil c N (x ^ n) y (ζ ^ n) := by
  induction n with
  | zero => simpa using cubWeil_one_left c h.2.1
  | succ n ih => simpa [pow_succ] using ih.mul_left h

theorem CubWeil.pow_eq_one {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) : ζ ^ N = 1 := by
  have hp := h.pow_left N
  rw [h.1] at hp
  exact hp.unique (cubWeil_one_left c h.2.1)

end

theorem cubWeil_basic : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (N : ℕ) (T : Over S), (∀ x y : T ⟶ G, x ^ N = 1 → y ^ N = 1 → ∃! ζ, CubWeil c N x y ζ) ∧ (∀ (x x' y : T ⟶ G) ζ ζ', CubWeil c N x y ζ → CubWeil c N x' y ζ' → CubWeil c N (x * x') y (ζ * ζ')) ∧ (∀ (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N y x ζ⁻¹ ∧ ζ ^ N = 1) ∧ (∀ (T' : Over S) (ρ : T' ⟶ T) (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N (ρ ≫ x) (ρ ≫ y) (Units.map ρ.left.appTop.hom.toMonoidHom ζ)) ∧ ∀ (H : Over S) [GrpObj H] (i : H ⟶ G), IsMonHom i → Nonempty (BiTriv c i) → ∀ (t : T ⟶ H) (y : T ⟶ G), t ^ N = 1 → y ^ N = 1 → CubWeil c N (t ≫ i) y 1) := by
  intro S G _ _ L c N T
  refine ⟨fun x y hx hy => existsUnique_cubWeil c hx hy, fun x x' y ζ ζ' h h' => h.mul_left h',
    fun x y ζ h => ⟨h.symm, h.pow_eq_one⟩, fun T' ρ x y ζ h => h.comp ρ, ?_⟩
  intro H _ i hi hne t y ht hy
  obtain ⟨σ⟩ := hne
  exact σ.cubWeil ht hy

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

private theorem comp_mul_of_isGrpPullback_lift {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left)
    {T : Over S'} (x y : T ⟶ G') : (x * y) ≫ a' = (x ≫ a') * (y ≫ a') := by
  apply Over.OverMorphism.ext
  apply hψ.1.hom_ext
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ φ) (by
      show (y.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
    let x₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((x ≫ a').left ≫ ψ) (by
      show ((x ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    let y₁ : Over.mk (T.hom ≫ f) ⟶ H := Over.homMk ((y ≫ a').left ≫ ψ) (by
      show ((y ≫ a').left ≫ ψ) ≫ H.hom = T.hom ≫ f
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w])
    have e1 := hφ.2 T x y x₀ y₀ rfl rfl
    have e2 := hψ.2 T (x ≫ a') (y ≫ a') x₁ y₁ rfl rfl
    have e3 : x₁ = x₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [x₁, x₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    have e4 : y₁ = y₀ ≫ a := by
      apply Over.OverMorphism.ext
      simp only [y₁, y₀, Over.comp_left, Over.homMk_left, Category.assoc, h]
    calc ((x * y) ≫ a').left ≫ ψ = (x * y).left ≫ φ ≫ a.left := by
          rw [Over.comp_left, Category.assoc, h]
      _ = ((x₀ * y₀) ≫ a).left := by rw [← Category.assoc, ← e1, Over.comp_left]
      _ = (x₁ * y₁).left := by rw [MonObj.mul_comp, e3, e4]
      _ = ((x ≫ a') * (y ≫ a')).left ≫ ψ := e2
  · rw [Over.w, Over.w]

theorem isMonHom_of_over_isMonHom {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback H' H f ψ)
    (a : G ⟶ H) [IsMonHom a] (a' : G' ⟶ H') (h : a'.left ≫ ψ = φ ≫ a.left) : IsMonHom a' := by
  have key := fun (T : Over S') (x y : T ⟶ G') => comp_mul_of_isGrpPullback_lift hφ hψ a a' h x y
  have hmul : μ ≫ a' = (a' ⊗ₘ a') ≫ μ := by
    have := key (G' ⊗ G') (fst G' G') (snd G' G')
    simpa [Hom.mul_def] using this
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h1' : (1 : 𝟙_ (Over S') ⟶ H') = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hone : η ≫ a' = η := by
    have e := key _ (1 : 𝟙_ (Over S') ⟶ G') 1
    rw [_root_.mul_one] at e
    have e' : ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * 1 = ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') * ((1 : 𝟙_ (Over S') ⟶ G') ≫ a') := by
      rw [_root_.mul_one]; exact e
    have e'' := (mul_left_cancel e').symm
    rw [h1, h1'] at e''
    exact e''
  exact { one_hom := hone, mul_hom := hmul }

theorem eSec_comp_of_isGrpPullback {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have h1 : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let P : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk ((η[G']).left ≫ φ) (by
    show ((η[G']).left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w])
  have e := hφ.2 (𝟙_ (Over S')) η[G'] η[G'] P P rfl rfl
  have hP : P * P = P := by
    apply Over.OverMorphism.ext
    rw [e, ← h1, _root_.mul_one, h1]
    rfl
  have hP1 : P = 1 := mul_eq_left.mp hP
  have hl := congrArg Over.Hom.left hP1
  rw [Hom.one_def, Over.comp_left] at hl
  change (η[G']).left ≫ φ = _ at hl
  rw [hl]
  congr 1

theorem IsWt.pull {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (hi : TorusCompat f F i' i) {V : G.left.Opens} {V' : G'.left.Opens} (hV : V' ≤ F ⁻¹ᵁ V) {u : Γ(G.left, V)}
    {χ : X} (hu : IsWt i V u χ) : IsWt i' V' ((F.appLE V V' hV).hom u) χ := by
  obtain ⟨τ, hτ, hχ, hτi⟩ := hi
  intro Z' t' g' h₁ h₂
  let Z : Over S := Over.mk (Z'.hom ≫ f)
  let t : Z ⟶ splitTorus S X := Over.homMk (t'.left ≫ τ) (by
    show (t'.left ≫ τ) ≫ (splitTorus S X).hom = Z'.hom ≫ f
    rw [Category.assoc, hτ, ← Category.assoc, Over.w])
  let g : Z ⟶ G := Over.homMk (g'.left ≫ F) (by
    show (g'.left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  let x₀ : Z ⟶ G := Over.homMk ((t' ≫ i').left ≫ F) (by
    show ((t' ≫ i').left ≫ F) ≫ G.hom = Z'.hom ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w])
  have hx₀ : t ≫ i = x₀ := by
    apply Over.OverMorphism.ext
    simp only [t, x₀, Over.comp_left, Over.homMk_left, Category.assoc, hτi]
  have hmul : (t ≫ i * g).left = (t' ≫ i' * g').left ≫ F := by
    rw [hx₀]
    exact hF.2 Z' (t' ≫ i') g' x₀ g rfl rfl
  have h₁' : ⊤ ≤ (t ≫ i * g).left ⁻¹ᵁ V := by
    rw [hmul]
    intro x _
    exact hV (h₁ trivial)
  have h₂' : ⊤ ≤ g.left ⁻¹ᵁ V := by
    intro x _
    exact hV (h₂ trivial)
  have key := hu Z t g h₁' h₂'
  have hcong : ∀ (a b : Z'.left ⟶ G.left) (hab : a = b) (ha : ⊤ ≤ a ⁻¹ᵁ V) (hb : ⊤ ≤ b ⁻¹ᵁ V),
      (a.appLE V ⊤ ha).hom u = (b.appLE V ⊤ hb).hom u := by
    intro a b hab ha hb
    subst hab
    rfl
  have e1 : ((t' ≫ i' * g').left.appLE V' ⊤ h₁).hom ((F.appLE V V' hV).hom u) =
      (((t' ≫ i' * g').left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₁ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have e2 : (g'.left.appLE V' ⊤ h₂).hom ((F.appLE V V' hV).hom u) =
      ((g'.left ≫ F).appLE V ⊤ (by intro x _; exact hV (h₂ trivial))).hom u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hc : (t.left.appTop).hom (charUnit S X χ).val = (t'.left.appTop).hom (charUnit S' X χ).val := by
    show ((t'.left ≫ τ).appTop).hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hχ]
  rw [e1, e2]
  exact (hcong _ _ hmul.symm _ h₁').trans (key.trans (congrArg₂ (· * ·) hc (hcong _ _ rfl h₂' _)))

theorem exists_tq_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ Q : TQ G X, ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i := by
  intro S S' f X _ G _ G' _ F hF Q
  letI := Q.grp
  letI := Q.comm
  haveI := Q.q_hom
  haveI := Q.i_hom
  obtain ⟨i', hi', -⟩ := existsUnique_torusCompat hF.1 Q.i
  haveI : IsMonHom i' := TorusCompat.isMonHom hF hi'
  have hB := isGrpPullback_pullback Q.B f
  let q' : G' ⟶ (Over.pullback f).obj Q.B :=
    Over.homMk (pullback.lift (F ≫ Q.q.left) G'.hom (by rw [Category.assoc, Over.w Q.q, hF.1.w]))
      (by exact pullback.lift_snd _ _ _)
  have hq'fst : q'.left ≫ pullback.fst Q.B.hom f = F ≫ Q.q.left := pullback.lift_fst _ _ _
  haveI : IsMonHom q' := isMonHom_of_over_isMonHom hF hB Q.q q' hq'fst
  have hBsq : IsPullback F q'.left Q.q.left (pullback.fst Q.B.hom f) := by
    refine IsPullback.of_bot ?_ hq'fst.symm (IsPullback.of_hasPullback Q.B.hom f)
    have e1 : q'.left ≫ pullback.snd Q.B.hom f = G'.hom := pullback.lift_snd _ _ _
    rw [e1, Over.w Q.q]
    exact hF.1
  have hAb : IsAbelianScheme ((Over.pullback f).obj Q.B) := by
    haveI := Q.isAb.smooth
    haveI := Q.isAb.proper
    haveI := Q.isAb.geomConnected
    exact ⟨inferInstance, by simp only [Over.pullback_obj_hom]; infer_instance,
      by simp only [Over.pullback_obj_hom]; infer_instance, by simp only [Over.pullback_obj_hom]; infer_instance⟩
  have hη : (η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f = f ≫ (η[Q.B]).left :=
    eSec_comp_of_isGrpPullback hB
  have hT' : (toUnit (splitTorus S' X)).left = (splitTorus S' X).hom := by
    have := Over.w (toUnit (splitTorus S' X))
    simpa using this
  have hT : (toUnit (splitTorus S X)).left = (splitTorus S X).hom := by
    have := Over.w (toUnit (splitTorus S X))
    simpa using this
  have hker0 : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left := by
    have h0 : IsPullback Q.i.left (toUnit (splitTorus S X)).left Q.q.left (η[Q.B]).left :=
      Q.isKernel.map (Over.forget S)
    rw [hT] at h0
    exact h0
  have hcomp : IsPullback (i'.left ≫ F) (splitTorus S' X).hom Q.q.left
      ((η[(Over.pullback f).obj Q.B]).left ≫ pullback.fst Q.B.hom f) := by
    rw [← torusCompat_iff.mp hi', hη]
    exact (SplitTorus.isGrpPullback_bcMap f X).1.paste_horiz hker0
  have hcommA : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[(Over.pullback f).obj Q.B]).left := by
    apply hB.1.hom_ext
    · simpa only [Category.assoc, hq'fst] using hcomp.w
    · rw [Category.assoc, Over.w q', Over.w i', Category.assoc, Over.w η[(Over.pullback f).obj Q.B]]
      simp
  have hA : IsPullback i'.left (splitTorus S' X).hom q'.left (η[(Over.pullback f).obj Q.B]).left :=
    IsPullback.of_right hcomp hcommA hBsq
  have hker : IsPullback i' (toUnit (splitTorus S' X)) q' η := by
    apply IsPullback.of_map (Over.forget S')
    · apply Over.OverMorphism.ext
      show i'.left ≫ q'.left = (toUnit (splitTorus S' X)).left ≫ (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hcommA
    · show IsPullback i'.left (toUnit (splitTorus S' X)).left q'.left (η[(Over.pullback f).obj Q.B]).left
      rw [hT']
      exact hA
  have hloc : ∀ (b : ((Over.pullback f).obj Q.B).left) (χ : X),
      ∃ V, b ∈ V ∧ ∃ u : (Γ(G'.left, q'.left ⁻¹ᵁ V))ˣ, IsWt i' (q'.left ⁻¹ᵁ V) (↑u) χ := by
    intro b χ
    obtain ⟨V, hbV, u, hu⟩ := Q.loc ((pullback.fst Q.B.hom f).base b) χ
    have hle : q'.left ⁻¹ᵁ (pullback.fst Q.B.hom f ⁻¹ᵁ V) ≤ F ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hq'fst]
    refine ⟨pullback.fst Q.B.hom f ⁻¹ᵁ V, hbV, Units.map (F.appLE _ _ hle).hom.toMonoidHom u, ?_⟩
    exact IsWt.pull hF hi' hle hu
  exact ⟨TQ.mk _ hAb q' i' inferInstance inferInstance
    (MorphismProperty.of_isPullback (P := @Flat) hBsq Q.q_flat)
    (MorphismProperty.of_isPullback (P := @Surjective) hBsq Q.q_surj)
    (MorphismProperty.of_isPullback (P := @IsAffineHom) hBsq Q.q_affine) hker hloc, hi'⟩

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem TQ.exists_affine_weight_units [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ V : Q.B.left.Opens, IsAffineOpen V ∧ b ∈ V ∧
      ∃ u : Multiplicative X →* Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ, ∀ χ : X, IsWt Q.i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let e := Module.Free.chooseBasis ℤ X
  choose W hW v hv using fun k => Q.loc b (e k)
  have ho : IsOpen (⋂ k, (W k : Set Q.B.left)) := isOpen_iInter_of_finite fun k => (W k).isOpen
  obtain ⟨V, hV, hbV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Q.B.left.isBasis_affineOpens
    (show b ∈ (⟨_, ho⟩ : Q.B.left.Opens) from Set.mem_iInter.2 hW)
  have hk : ∀ k, Q.q.left ⁻¹ᵁ V ≤ Q.q.left ⁻¹ᵁ W k := fun k =>
    Q.q.left.preimage_mono fun x hx => Set.mem_iInter.1 (hle hx) k
  let w : _ → Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := fun k =>
    Units.map (G.left.presheaf.map (homOfLE (hk k)).op).hom.toMonoidHom (v k)
  let l : X →ₗ[ℤ] Additive Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := e.constr ℤ fun k => Additive.ofMul (w k)
  let H : AddSubgroup X :=
    { carrier := {χ | IsWt Q.i _ (Additive.toMul (l χ)).val χ}
      zero_mem' := by
        show IsWt Q.i _ (Additive.toMul (l 0)).val 0
        rw [map_zero]; exact isWt_one
      add_mem' := fun {a c} ha hc => by
        show IsWt Q.i _ (Additive.toMul (l (a + c))).val (a + c)
        rw [map_add (f := _)]; exact IsWt.mul ha hc
      neg_mem' := fun {a} ha => by
        show IsWt Q.i _ (Additive.toMul (l (-a))).val (-a)
        rw [map_neg]; exact IsWt.inv ha }
  have hH : Submodule.span ℤ (Set.range e) ≤ H.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show IsWt Q.i _ (Additive.toMul (l (e k))).val (e k)
    rw [Module.Basis.constr_basis]
    exact (hv k).res (hk k)
  refine ⟨V, hV, hbV, AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => ?_⟩
  exact hH (e.mem_span χ)

theorem TQ.exists_local_section [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ (V : Q.B.left.Opens) (hV : IsAffineOpen V), b ∈ V ∧
      ∃ s : Spec Γ(Q.B.left, V) ⟶ G.left, s ≫ Q.q.left = hV.fromSpec := by
  obtain ⟨V, hV, hb, u, hu⟩ := Q.exists_affine_weight_units b
  have := Q.q_affine
  obtain ⟨hU, hbij⟩ := isAffineOpen_and_bijective_of_weight_units S X G Q.B Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V hV u hu
  let φ := RingEquiv.ofBijective _ hbij
  let ε : AddMonoidAlgebra Γ(Q.B.left, V) X →+* Γ(Q.B.left, V) :=
    (AddMonoidAlgebra.lift Γ(Q.B.left, V) Γ(Q.B.left, V) X 1).toRingHom
  let r : Γ(G.left, Q.q.left ⁻¹ᵁ V) ⟶ Γ(Q.B.left, V) := CommRingCat.ofHom (ε.comp φ.symm.toRingHom)
  have hr : Q.q.left.appLE V _ le_rfl ≫ r = 𝟙 _ := by
    rw [← Scheme.Hom.app_eq_appLE]
    ext a
    have h : φ (AddMonoidAlgebra.single 0 a) = (Q.q.left.app V).hom a :=
      (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans
        ((congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    change ε (φ.symm ((Q.q.left.app V).hom a)) = a
    rw [← h, RingEquiv.symm_apply_apply]
    simp [ε]
  refine ⟨V, hV, hb, Spec.map r ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Q.q.left hV hU le_rfl, ← Category.assoc,
    ← Spec.map_comp, hr, Spec.map_id, Category.id_comp]

theorem TQ.exists_lift [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A : Type} [CommRing A] [IsLocalRing A] {p : Spec (CommRingCat.of A) ⟶ S} (b : Over.mk p ⟶ Q.B) :
    ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b := by
  let b' : Spec (CommRingCat.of A) ⟶ Q.B.left := b.left
  obtain ⟨V, hV, hb, s, hs⟩ := Q.exists_local_section (b' (IsLocalRing.closedPoint A))
  have hr : Set.range b' ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) b' hb).ge (Set.mem_univ y)
  have h : (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ≫ Q.q.left = b' := by
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
  refine ⟨Over.homMk (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w Q.q, ← Category.assoc]
  exact (congrArg (· ≫ Q.B.hom) h).trans (Over.w b)

theorem exists_pow_eq_splitTorus [Module.Free ℤ X] {Z : Over S} {N : ℕ}
    (h : ∀ a : Γ(Z.left, ⊤)ˣ, ∃ r, r ^ N = a) (t : Z ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, t' ^ N = t := by
  let e := Module.Free.chooseBasis ℤ X
  let E := splitTorusPointsEquiv S X Z
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := (MonoidHom.toAdditiveRight (E t)).toIntLinearMap
  have hl : N • l = m := e.ext fun k => by
    rw [LinearMap.smul_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (hr _)
  refine ⟨E.symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom), E.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact MonoidHom.ext fun χ => congrArg Additive.toMul (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem torusQuotient_points_lift :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G]
      [IsCommMonObj G] (Q : TQ G X) (A : Type) [CommRing A] [IsLocalRing A] (p : Spec (CommRingCat.of A) ⟶ S),
      (∀ b : Over.mk p ⟶ Q.B, ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b) ∧
      ∀ N : ℕ, (∀ a : Aˣ, ∃ r : Aˣ, r ^ N = a) → ∀ b : Over.mk p ⟶ Q.B, b ^ N = 1 →
        ∃ g : Over.mk p ⟶ G, g ^ N = 1 ∧ g ≫ Q.q = b := by
  intro S X _ _ _ G _ _ Q A _ _ p
  refine ⟨Q.exists_lift, fun N hN b hb => ?_⟩
  have := Q.q_hom
  have := Q.i_hom
  obtain ⟨g, rfl⟩ := Q.exists_lift b
  have h₁ : (g ^ N) ≫ Q.q = toUnit _ ≫ η[Q.B] := by rw [MonObj.pow_comp, hb, Hom.one_def]
  let e : Aˣ ≃* Γ(Spec (CommRingCat.of A), ⊤)ˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨t, ht⟩ := exists_pow_eq_splitTorus (Z := Over.mk p) (N := N) (fun a => by
    obtain ⟨r, hr⟩ := hN (e.symm a)
    exact ⟨e r, (map_pow e r N).symm.trans ((congrArg e hr).trans (e.apply_symm_apply a))⟩)
    (Q.isKernel.lift _ _ h₁)
  have h₂ : (t ≫ Q.i) ^ N = g ^ N := by rw [← MonObj.pow_comp, ht, IsPullback.lift_fst]
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  refine ⟨(t ≫ Q.i)⁻¹ * g, ?_, ?_⟩
  · rw [mul_pow, inv_pow, h₂, inv_mul_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, h₃, inv_one, _root_.one_mul]

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_cp_pull : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) → ∀ P : CP G, ∃ (P' : CP G') (w : _), P'.L.L = P.L.L.pull F ∧ IsCPMap P' P f F hw w) := by
  intro S S' f G _ _ G' _ _ F hw mul P
  obtain ⟨_, _, _, _, _, _, _, h⟩ :=
    exists_isCPMap P mul _ (pull_isLB P.L.isLB F) _ (pullIso_isGen P.L.isLB F)
  exact ⟨_, _, rfl, h⟩

end GlobalTheory.UU
end

