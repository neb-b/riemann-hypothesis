module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0107
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesCubeValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartCube

theorem exists_move {X₁ X₂ B Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : B ⟶ X₁} {f₂ : B ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y ⟶ B)) {φ₁ : K → (Y ⟶ X₁)} (e : ∀ k, φ' k ≫ f₁ = φ₁ k) {ε : K → ℤ}
    (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε)) (ht : t₁.IsGen) :
    ∃ t₂ : LB.Gen (LB.LinComb L₂ (fun k => φ' k ≫ f₂) ε), t₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ → val t₂ r z J₂ =
        (∏ k, gw w (r ≫ φ' k) z (J₂ ((r ≫ φ' k) ≫ f₂)) (fun _ => J₁ ((r ≫ φ' k) ≫ f₁)) ^ ε k) * val t₁ r z J₁ := by
  obtain rfl : (fun k => φ' k ≫ f₁) = φ₁ := funext e
  have le : ∀ j : K → PUnit → L₁.ι, LB.wchart (L₁.pull f₁) φ' j ≤
      LB.wchart L₁ (fun k => φ' k ≫ f₁) (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull (x := φ' k y).1 (Set.mem_iInter.1 hy k)
  let a : LB.Gen (LB.LinComb (L₁.pull f₁) φ' ε) := ⟨fun j => res (le j) (t₁.s fun k => j k PUnit.unit)⟩
  have ha : a.IsGen := isGen_of_gm a fun y j j' hj hj' => by
    refine (gm_res (𝟙 Y) y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res (𝟙 Y) y (le j') hj' _).symm))
    refine Eq.trans ?_ (gm_pull_g L₁ f₁ (𝟙 Y ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
      (Set.mem_iInter.1 hj' k)).symm
    rw [Category.assoc]
  obtain ⟨t, ht', hv⟩ := exists_up ((isGen_iff w).1 hw) h₂ (pull_isLB h₁ f₁) a ha
  refine ⟨t, ht', fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have m : r z ∈ LB.wchart (L₁.pull f₁) φ' (fun k _ => J₁ (r ≫ φ' k ≫ f₁)) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (hJ₁ (r ≫ φ' k ≫ f₁))
  refine (hv Z r z _ _ (hJ₂.mem _ r) m).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_)
    (gm_res r z (le _) m _))
  rw [Category.assoc, Category.assoc]

variable {S : Scheme.{0}} {A A' T : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']

theorem prod_cub_pt {Z : Over S} (x x' y : Z ⟶ A) {U : Type} [CommGroup U] (h : (Z ⟶ A) → U) :
    ∏ I : thK, h (lift x (lift x' y) ≫ psum A (x3 A) I.down) ^ thε I =
      h (x * x' * y) * (h (x * x'))⁻¹ * (h (x * y))⁻¹ * (h (x' * y))⁻¹ * h x * h x' * h y * (h 1)⁻¹ := by
  classical
  let h' : (Z.left ⟶ A.left) → U := fun q => if hq : q ≫ A.hom = Z.hom then h (Over.homMk q hq) else 1
  have e : ∀ q : Z ⟶ A, h' q.left = h q := fun q => dif_pos (Over.w q)
  have p := prod_cub x x' y h'
  simp only [e] at p
  exact (Finset.prod_congr rfl fun I _ => congrArg (· ^ thε I) (e _).symm).trans p

theorem cubV_move (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} {L' : RigLB A'} (c : CubicalStr A L)
    (c' : CubicalStr A' L') (g : T ⊗ A ⟶ A')
    (hg : ∀ (Z : Over S) (t : Z ⟶ T) (x y : Z ⟶ A), lift t (x * y) ≫ g = (lift t x ≫ g) * (lift t y ≫ g))
    (w : LB.Iso (L.L.pull (snd T A).left) (L'.L.pull g.left)) (hw : w.IsGen) {Z : Over S} (σ : Z ⟶ T) (z : Z.left)
    {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (Ω : (Z ⟶ A) → (Z.left.presheaf.stalk z)ˣ)
    (hΩ : ∀ q, Ω q = gw w (lift σ q).left z (J' (lift σ q ≫ g).left) (fun _ => J q.left)) (x y u : Z ⟶ A) :
    cubV c' z J' (lift σ x ≫ g) (lift σ y ≫ g) (lift σ u ≫ g) =
      Ω (x * y * u) * (Ω (x * y))⁻¹ * (Ω (x * u))⁻¹ * (Ω (y * u))⁻¹ * Ω x * Ω y * Ω u * (Ω 1)⁻¹ * cubV c z J x y u := by
  have g1 : ∀ (Z : Over S) (t : Z ⟶ T), lift t (1 : Z ⟶ A) ≫ g = 1 := fun Z t =>
    mul_eq_left.1 ((hg Z t 1 1).symm.trans (by rw [_root_.mul_one]))
  let Y : Over S := A ⊗ A ⊗ A ⊗ T
  let t : Y ⟶ T := snd _ _ ≫ snd _ _ ≫ snd _ _
  let x₁ : Y ⟶ A := fst _ _
  let x₂ : Y ⟶ A := snd _ _ ≫ fst _ _
  let x₃ : Y ⟶ A := snd _ _ ≫ snd _ _ ≫ fst _ _
  obtain ⟨t₂, ht₂, hv⟩ := exists_move w hw L.isLB L'.isLB
    (fun I : thK => (lift t (lift x₁ (lift x₂ x₃) ≫ psum A (x3 A) I.down)).left)
    (φ₁ := fun I => (lift x₁ (lift x₂ x₃)).left ≫ thφ A (x3 A) I)
    (fun I => by rw [← Over.comp_left, lift_snd]; rfl)
    (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x₁ (lift x₂ x₃)).left) (DVR.pullGen_isGen _ _ _ _ c.isGen _)
  have ev : ∀ {Z : Over S} (σ : Z ⟶ T) (z : Z.left) {J J'}, Good L.L z J → Good L'.L z J' →
      ∀ (Ω : (Z ⟶ A) → (Z.left.presheaf.stalk z)ˣ),
      (∀ q, Ω q = gw w (lift σ q).left z (J' (lift σ q ≫ g).left) (fun _ => J q.left)) → ∀ x y u : Z ⟶ A,
      val t₂ (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' =
        Ω (x * y * u) * (Ω (x * y))⁻¹ * (Ω (x * u))⁻¹ * (Ω (y * u))⁻¹ * Ω x * Ω y * Ω u * (Ω 1)⁻¹ * cubV c z J x y u ∧
      val (LB.pullGen L'.L (thφ A' (x3 A')) thε c'.t (lift (lift t x₁ ≫ g) (lift (lift t x₂ ≫ g) (lift t x₃ ≫ g))).left)
        (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' =
        cubV c' z J' (lift σ x ≫ g) (lift σ y ≫ g) (lift σ u ≫ g) := by
    intro Z σ z J J' hJ hJ' Ω hΩ x y u
    have r₀ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ t = σ := by simp [t, Y]
    have r₁ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₁ = x := by simp [x₁, Y]
    have r₂ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₂ = y := by simp [x₂, Y]
    have r₃ : (lift x (lift y (lift u σ)) : Z ⟶ Y) ≫ x₃ = u := by simp [x₃, Y]
    refine ⟨(hv _ _ z J J' hJ hJ').trans (congrArg₂ (· * ·) (Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (prod_cub_pt x y u Ω)) ((val_cub c _ hJ _ _ _).trans (by rw [r₁, r₂, r₃]))), (val_cub c' _ hJ' _ _ _).trans ?_⟩
    · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, comp_lift, r₀, ← Category.assoc, comp_lift, comp_lift,
        r₁, r₂, r₃, lift_snd, hΩ]
    · rw [comp_lift_assoc, comp_lift_assoc, comp_lift_assoc, r₀, r₁, r₂, r₃]
  have sj : Function.Surjective
      ((snd A (A ⊗ A ⊗ T)).left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
  have key := gen_unique' L'.isLB (fun V _ k => ?_) _ (lift 1 (lift 1 (lift 1 (𝟙 T))) : T ⟶ Y).left ?_ sj
    (DVR.pullGen_isGen L'.L (thφ A' (x3 A')) thε c'.t c'.isGen
      (lift (lift t x₁ ≫ g) (lift (lift t x₂ ≫ g) (lift t x₃ ≫ g))).left) ht₂ (fun y I' hI' => ?_) _
    (lift x (lift y (lift u σ)) : Z ⟶ Y).left z J' hJ'
  · exact (ev σ z hJ hJ' Ω hΩ x y u).2.symm.trans (key.trans (ev σ z hJ hJ' Ω hΩ x y u).1)
  · refine (prod_cub_pt x₁ x₂ x₃ (fun q => k (lift t q ≫ g).left)).trans (Eq.trans ?_ (prod_cub _ _ _ k).symm)
    simp only [hg, g1]
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, lift_snd_assoc, lift_snd_assoc, lift_snd]; rfl
  · choose I hI using fun χ : T.left ⟶ A.left => exists_chart L.isLB (χ y)
    have E := ev (𝟙 T) y hI hI' _ (fun _ => rfl) 1 1 1
    have E₂ := E.2
    rw [g1, (isCub_cubV c' hI').face] at E₂
    refine E₂.trans (Eq.trans ?_ E.1.symm)
    rw [(isCub_cubV c hI).face]
    have fin : ∀ {G U : Type} [Group G] [CommGroup U] (h : G → U), 1 = h (1 * 1 * 1) * (h (1 * 1))⁻¹ * (h (1 * 1))⁻¹ *
        (h (1 * 1))⁻¹ * h 1 * h 1 * h 1 * (h 1)⁻¹ * 1 := fun h => by simp
    exact fin fun q : T ⟶ A => gw w (lift (𝟙 T) q).left y (I' (lift (𝟙 T) q ≫ g).left) (fun _ => I q.left)

theorem theta_move : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x y u, (N'.θ (f x) (f y) (f u) : F) * wVal ν ν' w f (x * y) * wVal ν ν' w f (x * u) * wVal ν ν' w f (y * u) * wVal ν ν' w f 1 = (N.θ x y u : F) * wVal ν ν' w f (x * y * u) * wVal ν ν' w f x * wVal ν ν' w f y * wVal ν ν' w f u := by
  intro hG R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hf x y u
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  have hJ' : Good D'.P.L z ν'.J := fun ψ => ν'.good ψ trivial
  have im : ∀ a, lift (𝟙 _) (ν.eA a) ≫ φ.hom ≫ snd _ _ = ν'.eA (f a) := fun a => by
    rw [← Category.assoc, hf a, lift_snd]
  let Ω : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun q =>
    gw w (lift (𝟙 _) q).left z (ν'.J (lift (𝟙 _) q ≫ φ.hom ≫ snd _ _).left) (fun _ => ν.J q.left)
  have vw : ∀ a, toStk z (wVal ν ν' w f a) = (Ω (ν.eA a)).val := fun a => by
    have m₁ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 _) (ν.eA a)).left z) ∈ D.P.L.U (ν.J (ν.eA a).left) := by
      exact (congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left z ∈ D.P.L.U (ν.J (ν.eA a).left))
        (lift_snd (𝟙 _) (ν.eA a))).mpr (hJ _)
    have m₂ : (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left ((lift (𝟙 _) (ν.eA a)).left z) ∈
        D'.P.L.U (ν'.J (ν'.eA (f a)).left) := by
      exact (congrArg (fun q : TF (R := R) F ⟶ D'.P.A => q.left z ∈ D'.P.L.U (ν'.J (ν'.eA (f a)).left))
        (im a)).mpr (hJ' _)
    refine (toStk_valF (lift (𝟙 (TF (R := R) F)) (ν.eA a)).left _ z (by exact ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩) _).trans ?_
    simp only [Ω, im]
    rfl
  have v : toStk z (N.θ x y u : F) = (cubV D.cub (T := TF (R := R) F) z ν.J (ν.eA x) (ν.eA y) (ν.eA u)).val :=
    (congrArg (toStk z) (ν.θ_eq x y u)).trans (toStk_valF _ _ z (hJ.mem _ _) _)
  have v' : toStk z (N'.θ (f x) (f y) (f u) : F) =
      (cubV D'.cub (T := TF (R := R) F) z ν'.J (ν'.eA (f x)) (ν'.eA (f y)) (ν'.eA (f u))).val :=
    (congrArg (toStk z) (ν'.θ_eq _ _ _)).trans (toStk_valF _ _ z (hJ'.mem _ _) _)
  have key := cubV_move hG D.P.isAb D.cub D'.cub (φ.hom ≫ snd _ _) hφ.2 w hw (𝟙 (TF (R := R) F)) z hJ hJ' Ω
    (fun _ => rfl) (ν.eA x) (ν.eA y) (ν.eA u)
  rw [im, im, im] at key
  have alg : ∀ {U : Type} [CommRing U] {a b p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ : Uˣ},
      a = p₁ * p₂⁻¹ * p₃⁻¹ * p₄⁻¹ * p₅ * p₆ * p₇ * p₈⁻¹ * b →
      a.val * p₂.val * p₃.val * p₄.val * p₈.val = b.val * p₁.val * p₅.val * p₆.val * p₇.val := by
    rintro U _ a b p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ rfl
    simp only [← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  apply (toStk z).injective
  simp only [map_mul, vw, v, v', map_one]
  exact alg key

end GlobalTheory.Ex.AbPartCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesSymmetryValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.AbPartSym

theorem exists_move {X₁ X₂ B Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : B ⟶ X₁} {f₂ : B ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ B)) {φ : K → (Y ⟶ X₁)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ f₁ = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L₁ φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L₂ (fun k => φ' k ≫ f₂) ε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J₂ J₁,
      Good L₂ z J₂ → Good L₁ z J₁ → val u r z J₂ =
        (∏ k, gw w (r ≫ φ' k) z (J₂ ((r ≫ φ' k) ≫ f₂)) (fun _ => J₁ ((r ≫ φ' k) ≫ f₁)) ^ ε k) * val t (r ≫ h) z J₁ := by
  let c := chartPullLinComb L₁ f₁ φ' φ ε h hc
  let a : LB.Gen (LB.LinComb (L₁.pull f₁) φ' ε) := ⟨fun j => res (c.le j) (pullU h _ (t.s (c.idx j)))⟩
  have va : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) j, r z ∈ LB.wchart (L₁.pull f₁) φ' j →
      gm r z (LB.wchart (L₁.pull f₁) φ' j) (a.s j) =
        gm (r ≫ h) z (LB.wchart L₁ φ fun k => j k PUnit.unit) (t.s fun k => j k PUnit.unit) := fun Z r z j hj =>
    (gm_res r z (c.le j) hj _).trans (gm_pull r h z _ (c.le j hj) _)
  have ha : a.IsGen := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_of_gm a fun y j j' hj hj' => by
    rw [va _ _ y j hj, va _ _ y j' hj', Category.id_comp]
    refine (gen_trans ht h y (c.le j hj) (c.le j' hj')).trans (congrArg (· * _) ?_)
    exact ((gm_linComb L₁ φ ε h y _ _ (c.le j hj) (c.le j' hj')).symm.trans (c.g y j j' hj hj').symm).trans
      (gm_linComb (L₁.pull f₁) φ' ε (𝟙 Y') y j j' hj hj')
  obtain ⟨u, hu, hv⟩ := exists_up ((isGen_iff w).1 hw) h₂ (pull_isLB h₁ f₁) a ha
  refine ⟨u, hu, fun Z r z J₂ J₁ g₂ g₁ => ?_⟩
  have m : r z ∈ LB.wchart (L₁.pull f₁) φ' fun k _ => J₁ ((r ≫ φ' k) ≫ f₁) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (g₁ ((r ≫ φ' k) ≫ f₁))
  refine (hv Z r z _ _ (g₂.mem _ r) m).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_)
  · rw [Category.assoc]
  · exact (va Z r z _ m).trans (val_of t (r ≫ h) z J₁ _ fun k => by
      rw [Category.assoc, Category.assoc, hc]).symm

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem sym_one (D : DegPre R) {Z : Over (Sp R)} {z : Z.left} {J} (hJ : Good D.P.L z J) :
    val D.sym (1 : Z ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ D.sym (eSec D.P.A) Z.hom).symm.trans ((val_corr hJ D.sym_rig Z.hom).trans (val_one _))

theorem val_sym_move (hG : GlobalFnsSt) {T : Over (Sp R)} (g : T ⊗ D.P.A ⟶ D'.P.A)
    (hg : ∀ (Z : Over (Sp R)) (t : Z ⟶ T) (x y : Z ⟶ D.P.A), lift t (x * y) ≫ g = (lift t x ≫ g) * (lift t y ≫ g))
    (w : LB.Iso (D.P.L.pull (snd T D.P.A).left) (D'.P.L.pull g.left)) (hw : w.IsGen) {Z : Over (Sp R)} (t : Z ⟶ T)
    (x : Z ⟶ D.P.A) {z : Z.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D'.sym (lift t x ≫ g).left z J' =
      gw w (lift t x⁻¹).left z (J' (lift t x⁻¹ ≫ g).left) (fun _ => J (x⁻¹).left) *
        (gw w (lift t x).left z (J' (lift t x ≫ g).left) (fun _ => J x.left))⁻¹ * val D.sym x.left z J := by
  let ρ : ∀ {Z : Over (Sp R)} (t : Z ⟶ T), (Z ⟶ D.P.A) →* (Z ⟶ D'.P.A) := fun t =>
    MonoidHom.mk' (fun x => lift t x ≫ g) (hg _ t)
  let n : T ⊗ D.P.A ⟶ T ⊗ D.P.A := lift (fst _ _) (snd _ _)⁻¹
  have hn : ∀ {Z : Over (Sp R)} (t : Z ⟶ T) (x : Z ⟶ D.P.A), (lift t x).left ≫ n.left = (lift t x⁻¹).left :=
    fun t x => by rw [← Over.comp_left, comp_lift, lift_fst, GrpObj.comp_inv, lift_snd]
  have ng : n.left ≫ g.left = g.left ≫ (ι[D'.P.A]).left := by
    have e : n ≫ g = (lift (fst T D.P.A) (snd T D.P.A) ≫ g)⁻¹ := map_inv (ρ (fst T D.P.A)) (snd T D.P.A)
    rw [lift_fst_snd, Category.id_comp] at e
    exact congrArg (fun q => q.left) e
  obtain ⟨u, hu, hv⟩ := exists_move w hw D.P.isLB D'.P.isLB (K := Fin 2) ![n.left, 𝟙 _] (snd T D.P.A).left
    (fun k => by
      fin_cases k
      · exact congrArg (fun q => q.left) (lift_snd (fst T D.P.A) (snd T D.P.A)⁻¹)
      · exact (Category.id_comp _).trans (Category.comp_id _).symm) D.sym D.sym_gen
  have hv' : ∀ {Z : Over (Sp R)} (t : Z ⟶ T) (x : Z ⟶ D.P.A) (z : Z.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val u (lift t x).left z J' =
      gw w (lift t x⁻¹).left z (J' (lift t x⁻¹ ≫ g).left) (fun _ => J (x⁻¹).left) *
        (gw w (lift t x).left z (J' (lift t x ≫ g).left) (fun _ => J x.left))⁻¹ * val D.sym x.left z J :=
    fun t x z J J' hJ hJ' => by
      refine (hv _ _ z J' J hJ' hJ).trans ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hn, Category.comp_id, zpow_one, zpow_neg_one]
      simp only [← Over.comp_left, lift_snd]
  have key := gen_unique' D'.P.isLB
    (φ := fun k => g.left ≫ (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [ng, Category.id_comp, Category.comp_id])
    (fst T D.P.A).left (lift (𝟙 T) (1 : T ⟶ D.P.A)).left (by rw [← Over.comp_left, lift_fst, Over.id_left])
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_fst hG D.P.isAb T)
    (DVR.pullGen_isGen _ _ _ _ D'.sym_gen g.left) hu (fun y I' hI' => by
      choose I hI using fun χ : T.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
      have o : lift (𝟙 T) (1 : T ⟶ D.P.A) ≫ g = 1 := map_one (ρ (𝟙 T))
      rw [val_pull hI', hv' _ _ y I I' hI hI', ← Over.comp_left, inv_one, o, sym_one D hI, sym_one D' hI',
        mul_inv_cancel, _root_.one_mul]) _ (lift t x).left z J' hJ'
  exact (val_pull hJ' _ _ _).symm.trans (key.trans (hv' t x z J J' hJ hJ'))


open GlobalTheory.ThetaInValues in
theorem sym_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f =>
    ∀ x, (N'.σ (f x) : F) * wVal ν ν' w f x = (N.σ x : F) * wVal ν ν' w f x⁻¹ := by
  intro hG R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hf x
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have c : ∀ a, lift (𝟙 _) (ν.eA a) ≫ φ.hom ≫ snd _ _ = ν'.eA (f a) := fun a => by
    rw [← Category.assoc, hf a, lift_snd]
  have v : ∀ a, sR y (wVal ν ν' w f a) = (gw w (lift (𝟙 (TF (R := R) F)) (ν.eA a)).left y
      (ν'.J (ν'.eA (f a)).left) (fun _ => ν.J (ν.eA a).left)).val := fun a => by
    refine toStk_valF _ _ y ?_ _
    refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
    · have := good ν' y (ν'.eA (f a)).left
      conv at this => enter [2]; rw [← c a]
      exact this
    · have := good ν y (ν.eA a).left
      conv at this => enter [2]; rw [← lift_snd (𝟙 (TF (R := R) F)) (ν.eA a)]
      exact this
  have key := val_sym_move hG (φ.hom ≫ snd _ _) hφ.2 w hw (𝟙 _) (ν.eA x) (good ν y) (good ν' y)
  rw [← map_inv ν.eA, c, c, sym_eq, sym_eq] at key
  refine (sR (R := R) y).injective ?_
  rw [map_mul, map_mul, v, v, ← sU_val, ← sU_val, key, ← Units.val_mul, ← Units.val_mul]
  congr 1
  rw [mul_right_comm, inv_mul_cancel_right, mul_comm]

end GlobalTheory.AbPartSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.ArcPsiVal

theorem gm_const {K F : Type} [Field K] [Field F] (g : K →+* F) (z : Sp F) (U : (Sp K).Opens) (hz : spMap g z ∈ U)
    (C : Γ(Sp K, U)ˣ) (c : K) (hC : C.val = resTop _ (scal (𝟙 (Sp K)) c)) :
    (gm (spMap g) z U C).val = toStk z (g c) := by
  rw [gm_val _ _ _ hz, hC]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
    ((spMap g).naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  have e2 := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  refine (congrArg ((Sp F).presheaf.germ _ z hz).hom e).trans ?_
  refine (TopCat.Presheaf.germ_res_apply (Sp F).presheaf _ z hz _).trans ?_
  exact congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e2.symm

theorem value_of_qVal {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (P : DegPre R) (ϖ : R)
    (χ : P.X) (n : ℤ) (h : QForm.QVal P ϖ χ n) (F : Type) [Field F] [Algebra (FractionRing R) F] (z : Sp F)
    (j : P.P.L.ι) (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ c : FractionRing R, HasVal ϖ c n ∧
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val = toStk z (algebraMap (FractionRing R) F c) := by
  have exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}}
      (f : A →+* F) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
      (a : Γ(X, U)ˣ) (z : Sp F) :
      ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
    let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
    refine ⟨Units.map g.toMonoidHom a, ?_⟩
    have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
    rw [← toStk_valF _ U z hz]
    congr 1
    have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
    rw [valF, dite_eq_left ht]
    have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
    have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
    rw [e1]
    exact e3
  obtain ⟨e, -, c, hc, hC⟩ := genHasVal_units _ _ _ _ _ _ h
  obtain ⟨C, hCv, hCt⟩ := hC (fun _ => j)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hg : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
    simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have ht : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ LB.wchart P.P.L (K := PUnit) (fun _ => (P.c χ).left) (fun _ => j) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => hj)
  have hz' : Out.jK R (Out.jFK (R := R) F z) ∈ LB.wchart P.P.L (K := PUnit) (fun _ => (P.c χ).left) (fun _ => j) :=
    ht (show Out.jK R (Out.jFK (R := R) F z) ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz : Out.jFK (R := R) F z ∈ LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j) :=
    Set.mem_iInter.2 fun k => by
      rw [QForm.ptK_eq]; exact Set.mem_iInter.1 hz' k
  obtain ⟨v, hv⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g (𝟙 _) _ ht (e.s (fun _ => j)) z
  rw [Category.comp_id, hg] at hv
  refine ⟨_, hasVal_mul_unit hc v, ?_⟩
  have h2 := congrArg (gm (spMap (algebraMap (FractionRing R) F)) z
    (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))) hCt
  rw [map_mul, gm_res _ _ _ hz] at h2
  replace hv := (congrArg Units.val (gm_pull _ _ _ _ hz' (e.s (fun _ => j)))).trans hv
  rw [map_mul, map_mul]
  exact (congrArg Units.val h2).trans
    (congrArg₂ (· * ·) (gm_const (algebraMap (FractionRing R) F) z _ hz C c hCv) hv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem psi_value (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : O' →+* R) (u : R) (P : DegPre R) (φ : P.P.A.left ⟶ a.D₀.P.A.left)
    (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (y : a.D₀.X) (χ : P.X)
    (hc : (P.c χ).left ≫ φ = spMap f ≫ (a.D₀.c y).left)
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (hG : GenRel w (LB.pullGen _ _ _ (P.psi χ) (Out.jFK (R := R) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F))
        (algebraMap (FractionRing R) F (algebraMap R _ u) ^ (a.be y y / 2)))
    (z : Sp F) (j : P.P.L.ι) (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ v : Rˣ,
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing R) F (algebraMap R _ u)) ^ (a.be y y / 2) *
        algebraMap (FractionRing R) F (algebraMap R _ v.val)) := by
  have exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}}
      (f : A →+* F) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
      (a : Γ(X, U)ˣ) (z : Sp F) :
      ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
    let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
    refine ⟨Units.map g.toMonoidHom a, ?_⟩
    have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
    rw [← toStk_valF _ U z hz]
    congr 1
    have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
    rw [valF, dite_eq_left ht]
    have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
    have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
    rw [e1]
    exact e3
  obtain ⟨hp, hv⟩ := (genRel_iff w _ _ _ z).1 hG
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  let x : Sp R ⟶ P.P.A.left := (P.c χ).left
  have hx : Out.jFK (R := R) F ≫ Out.ptK (P.c χ) = spMap g ≫ x := by
    have : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt R)))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := R) F ≫ Out.ptK (P.c χ)) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by
    rw [hx]
    exact ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z
  have hpt : spMap f (cpt R) ∈ (a.D₀.c y).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
    have h1 : (x ≫ φ) (cpt R) ∈ a.D₀.P.L.U j₀ := hj₀
    rw [hc] at h1
    exact h1
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVle⟩ := (Sp O').isBasis_affineOpens.exists_subset_of_mem_open hpt
    ((a.D₀.c y).left ⁻¹ᵁ a.D₀.P.L.U j₀).isOpen
  have hle : Out.jK O' ⁻¹ᵁ V ≤ LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀) :=
    fun q hq => Set.mem_iInter.2 fun _ => hVle hq
  obtain ⟨r, ⟨r, rfl⟩, hr⟩ := a.gen y (fun _ => j₀) V hV (Set.subset_univ _) hVle hle
  have htV : ⊤ ≤ spMap f ⁻¹ᵁ V := (top_le_iff_cpt _ _).2 hpV
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g (spMap f) V htV r z
  have hcomp : Out.jFK (R := O') F ≫ Out.jK O' = spMap g ≫ spMap f := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  have hzV : Out.jK O' (Out.jFK (R := O') F z) ∈ V := by
    have h1 : (spMap g ≫ spMap f) z ∈ V := htV (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [← hcomp] at h1
    exact h1
  have hr' : pullU (Out.jK O') V r = res hle ((a.D₀.psi y).s (fun _ => j₀)) := Units.ext hr
  rw [← hcomp, ← gm_pull _ _ _ _ hzV, hr'] at hu₀
  replace hu₀ := (congrArg Units.val (gm_res (Out.jFK (R := O') F) z hle hzV _)).symm.trans hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * u₀, H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem q_eq_of_hasArcData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : O' →+* W) (u : W) (χ : Sp W ⟶ Y.X), Function.Injective f → Y.HasArcData a (maximalIdeal W) f u χ → ∃ (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t) (e : a.D₀.X ≃+ P.D.toPre.X), ∀ (ϖ : W) (Q : P.D.toPre.X → ℤ) (w : ℕ), Irreducible ϖ → QForm.IsQ P.D.toPre ϖ Q → HasVal ϖ (algebraMap W (FractionRing W) u) w → ∀ y, Q (e y) = w * (a.be y y / 2) := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ _ b a W _ _ _ f u χ hfi h
  obtain ⟨t, m, P, φ, he, w, e, -, -, -, -, hc, hG⟩ := h
  refine ⟨t, m, P, e.toAddEquiv, fun ϖ Q n hϖ hQ hu y => ?_⟩
  let F := AlgebraicClosure (FractionRing W)
  let g : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective _ _)
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing W) F (algebraMap W _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.D.toPre.P.isLB ((P.D.toPre.c (e y)).left (cpt W))
  obtain ⟨v, hv⟩ := psi_value a f u P.D.toPre φ w y (e y) (hc y) F hF ((hG F _ hF rfl).1 y) z j hj
  obtain ⟨d, hd, hd'⟩ := value_of_qVal P.D.toPre ϖ (e y) _ (hQ (e y)) F z j hj
  have e1 := (toStk z).injective (hd'.symm.trans hv)
  rw [← map_zpow₀, ← map_mul] at e1
  have e2 := (algebraMap (FractionRing W) F).injective e1
  obtain ⟨s, hs⟩ := hu
  refine hasVal_unique hϖ hd ⟨s ^ (a.be y y / 2) * v, ?_⟩
  rw [e2, hs, mul_zpow, ← zpow_mul, Units.val_mul, map_mul, _root_.mul_assoc]
  congr 2
  exact (map_zpow (((algebraMap W (FractionRing W)) : W →* FractionRing W).comp (Units.coeHom W)) s _).symm

end GlobalTheory.ArcPsiVal

end
end

