module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CubeDescent

section Descent

variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_comp (L : LB X) (F : X' ⟶ X) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb (L.pull F) φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), u.IsGen := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤
      LB.wchart (L.pull F) φ (fun k _ => j k) := fun j y hy =>
    Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (t.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  refine (gm_res (𝟙 Y) y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y (le j') hj' _).symm))
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  exact (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans (by rw [Category.assoc])

theorem gs_appLE {Z : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom a) = gs g z U a :=
  (gs_res (𝟙 Z) z h trivial ((g.app U).hom a)).trans
    ((gs_pull (𝟙 Z) g z U (h (x := z) trivial) a).trans (by rw [Category.id_comp]))

theorem exists_gen_descend {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y) [Flat π] [Surjective π]
    [QuasiCompact π] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (J), Good L z J → g₁ ≫ π = g₂ ≫ π →
      val u g₁ z J = val u g₂ z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := by
    intro j
    refine FunDescent.exists_app_eq π _ _ fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z _ => ?_
    rw [gs_appLE, gs_appLE, gs_unit _ _ _ (h₁ (x := z) trivial), gs_unit _ _ _ (h₂ (x := z) trivial)]
    choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu g₁ z (le j (h₁ (x := z) trivial)) (Good.mem hI _ g₁)
    have c₂ := gen_trans hu g₂ z (le j (h₂ (x := z) trivial)) (Good.mem hI _ g₂)
    have c₃ : trF (fun k => π ≫ φ k) ε g₁ z j (fun k => I (g₁ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε g₂ z j (fun k => I (g₂ ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : g₁ ≫ π ≫ φ k = g₂ ≫ π ≫ φ k := by rw [reassoc_of% e]
      show gm (g₁ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₁ ≫ π ≫ φ k))) (L.g (j k) (I (g₁ ≫ π ≫ φ k))) ^ _ =
        gm (g₂ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₂ ≫ π ≫ φ k))) (L.g (j k) (I (g₂ ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res g₁ z (le j) (h₁ (x := z) trivial) _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h Z g₁ g₂ z I hI e)).trans c₂.symm)).trans
        (gm_res g₂ z (le j) (h₂ (x := z) trivial) _).symm))
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := fun j =>
    FunDescent.isUnit_of_isUnit_app π _ _ (ha j ▸ Units.isUnit _)
  have hv : ∀ j (y : Y'), π y ∈ LB.wchart L φ j → gm π y (LB.wchart L φ j) (hun j).unit =
      gm (𝟙 Y') y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    refine Eq.trans ?_ ((gm_pull (𝟙 Y') π y _ hy _).symm.trans
      ((congrArg (gm (𝟙 Y') y _) e).trans (gm_res (𝟙 Y') y (le j) hy _)))
    rw [Category.id_comp]
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    (FunDescent.app_injective π (LB.wchart L φ j ⊓ LB.wchart L φ j') ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  rw [Category.id_comp]
  refine ((gm_res π y _ hy' _).trans ((hv j y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε π y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res π y _ hy' _).trans (hv j' y hy'.2)))
  simp only [trF, Category.id_comp]

end Descent

section Group

variable {S X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {Q : Over S}
  {φ : K → (Q.left ⟶ X)} {ε : K → ℤ}

theorem val_eq_of_section (hL : L.IsLB) {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {P T : Over S} (p : P ⟶ T) (e : T ⟶ P) (he : e ≫ p = 𝟙 T)
    (hp : Function.Surjective p.left.appTop.hom) (a a' : P ⟶ Q)
    (hF : FormEq (fun k => a'.left ≫ φ k) ε (fun k => a.left ≫ φ k) ε)
    (h : ∀ y J, Good L y J → val u (e ≫ a).left y J = val u (e ≫ a').left y J)
    {T' : Over S} (ρ : T' ⟶ P) (z : T'.left) (J) (hJ : Good L z J) :
    val u (ρ ≫ a).left z J = val u (ρ ≫ a').left z J := by
  have := gen_unique' hL hF p.left e.left (congrArg (fun q => q.left) he) hp
    (DVR.pullGen_isGen _ _ _ _ hu a.left) (DVR.pullGen_isGen _ _ _ _ hu a'.left)
    (fun y J hJ => by rw [val_pull hJ, val_pull hJ]; exact h y J hJ) _ ρ.left z J hJ
  rw [val_pull hJ, val_pull hJ] at this
  exact this

variable {A : Over S} [GrpObj A]

theorem val_eq_of_axis (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (σ : A ⊗ A ⊗ A ⟶ Q)
    (H₁ : FormEq (fun k => (lift (1 : A ⟶ A) (lift 1 1) ≫ σ).left ≫ φ k) ε
      (fun k => (lift (𝟙 A) (lift 1 1) ≫ σ).left ≫ φ k) ε)
    {T : Over S} (x x' : T ⟶ A)
    (H₂ : ∀ (T' : Over S) (ρ : T' ⟶ T) (y w : T' ⟶ A) (k : K),
      (lift (ρ ≫ x') (lift y w) ≫ σ).left ≫ φ k = (lift (ρ ≫ x) (lift y w) ≫ σ).left ≫ φ k)
    (y w : T ⟶ A) (z : T.left) (J) (hJ : Good L z J) :
    val u (lift x (lift y w) ≫ σ).left z J = val u (lift x' (lift y w) ≫ σ).left z J := by
  have face : ∀ (v : T ⟶ A) (z : T.left) (J), Good L z J →
      val u (lift v (lift 1 1) ≫ σ).left z J = val u (lift (1 : T ⟶ A) (lift 1 1) ≫ σ).left z J := by
    intro v z J hJ
    have := val_eq_of_section hL hu (toUnit A) η[A] (toUnit_unique _ _) (hG _ _ hA).2
      (lift (𝟙 A) (lift 1 1) ≫ σ) (lift (1 : A ⟶ A) (lift 1 1) ≫ σ) H₁ (fun y J _ => by
        congr 2
        simp [comp_lift_assoc, Hom.one_def]) v z J hJ
    simpa only [comp_lift_assoc, comp_lift, Category.comp_id, MonObj.comp_one] using this
  have := val_eq_of_section hL hu (snd A (A ⊗ T) ≫ snd A T) (lift 1 (lift 1 (𝟙 T))) (by simp)
    (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x) (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x') (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (H₂ _ _ _ _ k))
    (fun z J hJ => by
      have e := (face x z J hJ).trans (face x' z J hJ).symm
      simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
        Category.id_comp] using e)
    (lift y (lift w (𝟙 T))) z J hJ
  simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
    Category.id_comp] using this

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem exists_gen_theta [IsCommMonObj A] (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (ψ : A ⟶ B) [IsMonHom ψ] [Flat ψ.left] [Surjective ψ.left] [QuasiCompact ψ.left]
    {M : LB B.left} (hM : M.IsLB) (t : LB.Gen (Theta A (M.pull ψ.left))) (ht : t.IsGen) :
    ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have := AbelianQuotient.flat_tensorHom ψ ψ
  have := AbelianQuotient.surjective_tensorHom ψ ψ
  have := AbelianQuotient.quasiCompact_tensorHom ψ ψ
  have := AbelianQuotient.flat_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.surjective_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.quasiCompact_tensorHom ψ (ψ ⊗ₘ ψ)
  let π : G3 A ⟶ G3 B := ψ ⊗ₘ ψ ⊗ₘ ψ
  have hπ : ∀ {T : Over S} (x y w : T ⟶ A),
      lift x (lift y w) ≫ π = lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ)) := fun x y w => by
    simp [π, lift_map]
  obtain ⟨u₀, hu₀⟩ := exists_gen_comp M ψ.left (thφ A (x3 A)) thε t ht
  have hφ : ∀ I, thφ A (x3 A) I ≫ ψ.left = π.left ≫ thφ B (x3 B) I := fun I => by
    let ρ : (G3 A ⟶ A) →* (G3 A ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ
    exact congrArg (fun q => q.left) ((psum_hom ρ (x3 A) I.down).trans
      ((congrArg (fun q => psum B q I.down) (funext fun i => by
        fin_cases i <;> simp [ρ, π, preHom, x3])).trans (psum_hom (preHom π) (x3 B) I.down).symm))
  obtain ⟨u, hu, -⟩ := exists_gen hM (φ' := fun I => π.left ≫ thφ B (x3 B) I) (ε' := thε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hφ I)) u₀ hu₀
  have hc : ∀ {T : Over S} (x y w : T ⟶ A) (I : thK),
      (lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I =
        (lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ))).left ≫ thφ B (x3 B) I := fun x y w I => by
    rw [← Category.assoc, ← Over.comp_left, hπ]
  have hp : ∀ (x y w : A ⟶ A), (y = 1 ∧ w = 1 ∨ x = 1 ∧ w = 1 ∨ x = 1 ∧ y = 1) →
      ∀ (U : Type) [CommGroup U] (h : (A.left ⟶ B.left) → U),
      ∏ I, h ((lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I) ^ thε I = 1 := by
    intro x y w H U _ h
    refine (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hc x y w I)).trans
      ((prod_cub _ _ _ h).trans ?_)
    apply Additive.ofMul.injective
    rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [MonObj.one_comp, _root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;>
      abel
  refine exists_gen_descend hM π.left (thφ B (x3 B)) thε u hu fun Z g₁ g₂ z J hJ e => ?_
  let T : Over S := Over.mk (g₂ ≫ (G3 A).hom)
  let k₂ : T ⟶ G3 A := Over.homMk g₂ rfl
  let k₁ : T ⟶ G3 A := Over.homMk g₁ (by
    change g₁ ≫ (G3 A).hom = g₂ ≫ (G3 A).hom
    rw [← Over.w π, reassoc_of% e])
  have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
  obtain ⟨x, y, w, h₁⟩ : ∃ x y w, k₁ = lift x (lift y w) :=
    ⟨k₁ ≫ fst _ _, k₁ ≫ snd _ _ ≫ fst _ _, k₁ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  obtain ⟨x', y', w', h₂⟩ : ∃ x y w, k₂ = lift x (lift y w) :=
    ⟨k₂ ≫ fst _ _, k₂ ≫ snd _ _ ≫ fst _ _, k₂ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  rw [h₁, h₂, hπ, hπ] at e'
  have ex : x ≫ ψ = x' ≫ ψ := by simpa using e' =≫ fst _ _
  have ey : y ≫ ψ = y' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ fst _ _
  have ew : w ≫ ψ = w' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ snd _ _
  change val u k₁.left z J = val u k₂.left z J
  rw [h₁, h₂]
  let σ₁ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (fst _ _) (snd _ _ ≫ snd _ _))
  let σ₂ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  have s₁ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₁ = lift b (lift a c) :=
    fun a b c => by simp [σ₁]
  have s₂ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₂ = lift b (lift c a) :=
    fun a b c => by simp [σ₂]
  have v₀ := val_eq_of_axis hG hA hM hu (𝟙 _) (fun U _ h => by
      simp only [Category.comp_id]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).symm) x x'
    (fun T' ρ a b I => by
      rw [Category.comp_id, Category.comp_id]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ex]) (hc _ _ _ I).symm)) y w z J hJ
  have v₁ := val_eq_of_axis hG hA hM hu σ₁ (fun U _ h => by
      simp only [s₁]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inl ⟨rfl, rfl⟩)) U h).symm) y y'
    (fun T' ρ a b I => by
      rw [s₁, s₁]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ey]) (hc _ _ _ I).symm)) x' w z J hJ
  have v₂ := val_eq_of_axis hG hA hM hu σ₂ (fun U _ h => by
      simp only [s₂]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inr ⟨rfl, rfl⟩)) U h).symm) w w'
    (fun T' ρ a b I => by
      rw [s₂, s₂]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ew]) (hc _ _ _ I).symm)) x' y' z J hJ
  rw [Category.comp_id, Category.comp_id] at v₀
  rw [s₁, s₁] at v₁
  rw [s₂, s₂] at v₂
  exact v₀.trans (v₁.trans v₂)

end Group

end GlobalTheory.CubeDescent

namespace GlobalTheory

theorem cube_descends_along_etale_isogeny :
    Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∃ t : LB.Gen (Theta A (M.pull ψ.left)), t.IsGen) → ∃ t : LB.Gen (Theta B M), t.IsGen := by
  intro hG k _ _ A B _ _ _ ψ M _ hA _ hM _ _ _ _ ⟨t, ht⟩
  exact CubeDescent.exists_gen_theta hG hA ψ hM t ht

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetSpread

theorem exists_factor {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (j : Sp R ⟶ S) [IsOpenImmersion j]
    (x : Sp K ⟶ S) (q : PrimeSpectrum R) (y : Sp K) (hy : x y = j q) :
    ∃ f : R →+* K, spMap f ≫ j = x ∧ RingHom.ker f = q.asIdeal := by
  have hsub : Set.range x ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact ⟨q, by rw [← hy, Subsingleton.elim z y]⟩
  have hx : IsOpenImmersion.lift j x hsub ≫ j = x := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift j x hsub)
  rw [← hg] at hx
  have hq : Spec.map g y = q := by
    apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hx, hy]
  refine ⟨g.hom, hx, ?_⟩
  rw [← hq]
  have hy0 : PrimeSpectrum.asIdeal y = ⊥ := by
    rcases Ideal.eq_bot_or_top (PrimeSpectrum.asIdeal (R := K) y) with e | e
    · exact e
    · exact absurd e (PrimeSpectrum.isPrime y).ne_top
  change _ = Ideal.comap g.hom (PrimeSpectrum.asIdeal y)
  rw [hy0]
  rfl

theorem eq_comp_of_spMap {S : Scheme.{0}} {o R K : Type} [CommRing o] [CommRing R] [CommRing K]
    {j : Sp R ⟶ S} {s : S ⟶ Sp o} {δ : o →+* R} (hδ : j ≫ s = spMap δ) {f : R →+* K} {β : o →+* K}
    (h : (spMap f ≫ j) ≫ s = spMap β) (a : o) : β a = f (δ a) := by
  rw [Category.assoc, hδ] at h
  have h' : CommRingCat.ofHom δ ≫ CommRingCat.ofHom f = CommRingCat.ofHom β :=
    Spec.map_injective ((Spec.map_comp _ _).trans h)
  exact (congrArg (fun z => z.hom a) h').symm

theorem detCond_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {o : Type} [CommRing o] (s : S ⟶ Sp o) (ρ : o)
    (hρ : ρ ^ 2 = -(H.d : o))
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)})
    {R : Type} [CommRing R] [IsReduced R] (j : Sp R ⟶ S) [IsOpenImmersion j]
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (act' : OAct (𝓞 E) G') (hs : Smooth G'.hom)
    {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (hv : IsLieBasis v)
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ Sp R) (τ : 𝓞 E →+* K) (N : ℕ),
      LieMult act' y τ N ↔ LieMult act (y ≫ j) τ N)
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (β : o →+* K)
    (hβ : (spMap f ≫ j) ≫ s = spMap β) : DetCond D act (spMap f ≫ j) (β ρ) := by
  obtain ⟨δ₀, hδ₀⟩ := Spec.map_surjective (j ≫ s)
  have hδ : j ≫ s = spMap δ₀.hom := hδ₀.symm
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff (𝓞 E) R G' act' n v hs hv
  obtain ⟨M', hM', e⟩ := hM K f
  have hr : (δ₀.hom ρ) ^ 2 = -(H.d : R) := by
    have := congrArg δ₀.hom hρ
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have main := _root_.GlobalTheory.eigenMult_of_dense E H D.p D.q n R M (δ₀.hom ρ) hr (by
    refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
    rintro q ⟨L, _, _, _, x, β', ⟨y, hy⟩, hx, hdet⟩
    obtain ⟨g, rfl, hg⟩ := exists_factor j x q y hy
    obtain ⟨N', hN', e'⟩ := hM L g
    refine ⟨L, inferInstance, inferInstance, inferInstance, g, N', hg, hN', fun τ => ?_⟩
    rw [← e', ← e', h, h, ← eq_comp_of_spMap hδ hx]
    exact hdet τ) K f M' hM'
  intro τ
  rw [← h, ← h, e, e, eq_comp_of_spMap hδ hβ]
  exact main τ

theorem detCond_of_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  intro E _ _ _ H D S _ G _ _ g act o _ s ρ hg hρ hd K _ _ _ x β hβ
  let y : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x y) trivial
  let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  obtain ⟨q, hq⟩ : x y ∈ Set.range j := hU.range_fromSpec.ge hs
  have hg₁ : SmoothOfRelativeDimension g ((Over.pullback j).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨r, hr, v, hv⟩ := GlobalTheory.LieLoc.lie_locally_free Γ(S, U) ((Over.pullback j).obj G) g hg₁ q
  let a : Sp (Localization.Away r) ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) (Localization.Away r))
  have : IsOpenImmersion a := IsOpenImmersion.of_isLocalization r
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(S, U) (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨f, rfl, -⟩ := exists_factor (a ≫ j) x q' y (by
    rw [← hq, ← hq']
    rfl)
  obtain ⟨a₁, h₁⟩ := GlobalTheory.DetExtend.exists_oAct_pullback j act
  obtain ⟨a₂, h₂⟩ := GlobalTheory.DetExtend.exists_oAct_pullback a a₁
  have hg₂ : SmoothOfRelativeDimension g ((Over.pullback a).obj ((Over.pullback j).obj G)).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg₁
  refine detCond_of_basis D act s ρ hρ hd (a ≫ j) a₂ (SmoothOfRelativeDimension.smooth g _) v hv
    (fun L _ z τ N => ?_) K f β hβ
  rw [LiePull.lieMult_pull _ _ _ _ _ a _ a₁ a₂ (isGrpPullback_pullback _ a)
    (fun c => by rw [h₂]; exact pullback.lift_fst _ _ _) L z τ N,
    LiePull.lieMult_pull _ _ _ _ _ j _ act a₁ (isGrpPullback_pullback _ j)
    (fun c => by rw [h₁]; exact pullback.lift_fst _ _ _) L (z ≫ a) τ N, Category.assoc]

end GlobalTheory.DetSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace RigidFunction

theorem not_mem_basicOpen_fibre {X P F : Scheme.{0}} {K : Type} [Field K] {p : P ⟶ X}
    {t : Spec (CommRingCat.of K) ⟶ X} {φ : F ⟶ P} {q : F ⟶ Spec (CommRingCat.of K)} (w : φ ≫ p = q ≫ t)
    [IsIntegral F] [UniversallyClosed q] (V : X.Opens) (hV : ∀ x, t x ∈ V) (s : Γ(P, p ⁻¹ᵁ V)) (a b : F)
    (ha : φ a ∉ P.basicOpen s) : φ b ∉ P.basicOpen s := by
  have hle : (⊤ : F.Opens) ≤ φ ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro c _
    change p (φ c) ∈ V
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    exact hV _
  have key : ∀ c : F, φ c ∈ P.basicOpen s ↔ c ∈ F.basicOpen ((φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s) := by
    intro c
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [key] at ha ⊢
  have hF := isField_of_universallyClosed K q
  by_cases hs : (φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s = 0
  · rw [hs, Scheme.basicOpen_zero]
    exact fun h => h
  · exfalso
    apply ha
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel hs
    rw [Scheme.basicOpen_of_isUnit _ (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)]
    trivial

end RigidFunction

theorem eq_one_of_appLE_section_eq_one :
    ∀ (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left), e ≫ P.hom = 𝟙 X → Smooth P.hom → GeometricallyIntegral P.hom → (IsReduced X ∧ genericPoints X ⊆ abLocus P) → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) := by
  intro X P e he hsm hgi hXg V u h hu
  obtain ⟨hred, hgen⟩ := hXg
  have := hsm
  have := hgi
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced P.hom

  have h0 : (e.appLE _ V h).hom (u - 1) = 0 := by rw [map_sub, map_one, hu, sub_self]
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  rw [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot, not_not] at hne

  have hopen := P.hom.isOpenMap _ (P.left.basicOpen (u - 1)).isOpen
  obtain ⟨x₀, ⟨y, hy, hyx₀⟩, hxg⟩ :=
    (dense_iff_closure_eq.mpr genericPoints.closure).inter_open_nonempty _ hopen (hne.image _)
  have hxV : x₀ ∈ V := by
    rw [← hyx₀]
    exact P.left.basicOpen_le _ hy
  have hxnot : e x₀ ∉ P.left.basicOpen (u - 1) := by
    intro hm
    have hmem : x₀ ∈ X.basicOpen ((e.appLE _ V h).hom (u - 1)) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨hxV, hm⟩
    rw [h0, Scheme.basicOpen_zero] at hmem
    exact hmem

  let K := AlgebraicClosure (X.residueField x₀)
  let t : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have ht : ∀ z, t z = x₀ := by
    intro z
    have hz : t z ∈ Set.range (X.fromSpecResidueField x₀) := ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at hz
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  have : IsProper (pullback.snd P.hom t) := hgen hxg K t ⟨pt, ht pt⟩
  have : IsIntegral (pullback P.hom t) :=
    hgi.geometrically_isIntegral t (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hpt : P.hom (e x₀) = t pt := by
    rw [ht, ← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback (e x₀) pt hpt
  obtain ⟨b, hb, -⟩ := Scheme.Pullback.exists_preimage_pullback y pt (hyx₀.trans (ht pt).symm)
  have hfib := RigidFunction.not_mem_basicOpen_fibre pullback.condition V
    (fun z => by rw [ht z]; exact hxV) (u - 1) a b (by rw [ha]; exact hxnot)
  rw [hb] at hfib
  exact hfib hy

end GlobalTheory
end

