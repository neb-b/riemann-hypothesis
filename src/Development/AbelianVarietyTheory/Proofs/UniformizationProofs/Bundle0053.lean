module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullMulValue
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullMul

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {Z : Scheme.{0}}

def rv (ρ : LB.Gen (L.pull (eSec A))) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ r z J

theorem val_rigPow (ρ : LB.Gen (L.pull (eSec A))) (k : ℤ) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : val (rigPow A L ρ k) r z J = rv ρ r z J ^ k :=
  map_zpow _ _ _

theorem val_rigT (ρ : LB.Gen (L.pull (eSec A))) (T : Over S) (k : ℤ) (r : Z ⟶ T.left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (rigT A L ρ T k) r z J = rv ρ (r ≫ T.hom) z J ^ k := by
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  refine Eq.trans ?_ (val_of (L := L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => congrArg J (Category.assoc _ _ _))).symm
  exact (gm_res r z _ hm _).trans (gm_pull r T.hom z
    (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _)

omit [GrpObj A] in
theorem val_powFrame {T : Over S} (x : T ⟶ A) (e) (k : ℤ) (r : Z ⟶ T.left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : val (powFrame A L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem val_powGen {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb M φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) :
    val (GeneratorPullback.powGen M φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

theorem one_left (T : Over S) : (1 : T ⟶ A).left = T.hom ≫ eSec A := by
  rw [Hom.one_def, Over.comp_left]; rfl

theorem pull_mul (P : PolAV S) (T : Over S) (ρ : LB.Gen (P.L.pull (eSec P.A))) (n k k' : ℕ) (hk : k' = k * n ^ 2)
    (x : T ⟶ P.A) (e) (hx : IsTorsFrame P ρ n x e) (ψ : T ⊗ P.A ⟶ T ⊗ P.A) (m : T ⊗ P.A ⟶ P.A)
    (hm : ψ ≫ snd _ _ = m) (hψ : ψ ≫ fst _ _ = fst _ _) (hmn : m = snd _ _ ≫ (𝟙 P.A ^ n)) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, m.left] ![(k' : ℤ), -(k : ℤ)]), α.IsGen ∧
      LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L ρ T ((k' : ℤ) - k)) ∧
      ∀ (t : LB.Sec (LPow P.A P.L (k : ℤ) T)) (c : ∀ z : T.left, T.left.presheaf.stalk z),
        (∀ z J, Good P.L z J → VVRank.sv P.A t (ptSecT P.A 1).left z J =
          c z * (val (rigT P.A P.L ρ T (k : ℤ)) (𝟙 _) z J).val) →
        ∃ t' : LB.Sec (LPow P.A P.L (k' : ℤ) T), IsTwistPull P.A P.L ψ m hm k' k α t t' ∧
          ∀ z J, Good P.L z J → VVRank.sv P.A t' (ptSecT P.A x).left z J =
            c z * (val (powFrame P.A P.L x e k') (𝟙 _) z J).val := by
  obtain ⟨hxn, -, α₀, hα₀, hN, hC⟩ := hx
  have em : (snd T P.A).left ≫ (mulA P.A n).left = m.left := by rw [hmn, Over.comp_left]
  obtain ⟨α, hα, hv⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, m.left]) (ε' := ![(k' : ℤ), -(k : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, em, hk]
      congr 2 <;> push_cast <;> ring)
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L _ _ α₀ (snd T P.A).left) k)
    (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hα₀ _) k)
  have hv' : ∀ (y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      val α (ptSecT P.A y).left z J = val α₀ y.left z J ^ k := fun y z J hJ => by
    rw [hv _ _ z J hJ, val_powGen, val_pull hJ, ← Over.comp_left, ptSecT, lift_snd]
  refine ⟨α, hα, corr_of_val P.isLB fun z J hJ => ?_, fun t c ht => ?_⟩
  · have a := val_corr hJ hN T.hom
    rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow] at a
    rw [val_pull hJ, Category.id_comp, hv' 1 z J hJ, one_left, val_rigT ρ T _ _ z hJ, Category.id_comp]
    refine (congrArg (· ^ k) a).trans ?_
    change (rv ρ T.hom z J ^ ((n : ℤ) ^ 2) * (rv ρ T.hom z J)⁻¹) ^ k = rv ρ T.hom z J ^ _
    rw [← zpow_sub_one, ← zpow_natCast, ← zpow_mul, hk]
    congr 1; push_cast; ring
  · obtain ⟨t', ht'⟩ := VVRank.exists_isTwistPull P.A (ψ := ψ) (hm := hm) P.isLB hα t
    refine ⟨t', ht', fun z J hJ => ?_⟩
    have e₁ : ptSecT P.A x ≫ ψ = ptSecT P.A 1 := by
      ext1
      · rw [Category.assoc, hψ, ptSecT, ptSecT, lift_fst, lift_fst]
      · rw [Category.assoc, hm, hmn, ptSecT, ptSecT, lift_snd_assoc, lift_snd, MonObj.comp_pow,
          Category.comp_id, hxn]
    have a := val_corr hJ hC (𝟙 _)
    rw [val_powFrame, val_mul hJ, val_pull hJ, val_rigT ρ T _ _ z hJ, Category.id_comp, zpow_one] at a
    rw [VVRank.sv_of_isTwistPull P.A ht' _ z hJ, ← Over.comp_left, e₁, ht z J hJ, hv' x z J hJ,
      val_rigT ρ T _ _ z hJ, val_powFrame, mul_left_comm, ← Units.val_mul, zpow_natCast, ← mul_pow, ← a,
      ← zpow_natCast, ← zpow_mul, hk]
    congr 3; push_cast; ring

theorem pull_mul_value : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (n k k' : ℕ), k' = k * n ^ 2 → ∀ (x : TFK (R := R) F ⟶ A.A) e, IsTorsFrame A ρ n x e → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ (𝟙 A.A ^ n) → ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)]), α.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) ∧ ∀ (t : SecA A F k) (c : F), (∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) → ∃ t' : SecA A F k', IsTwistPull A.A A.L ψ m hm k' k α t t' ∧ (∀ z J, Good A.L z J → sA t' (ptSecT A.A x).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k') (𝟙 _) z J).val) :=
  fun R _ _ A F _ _ ρ _ n k k' hk x e hx ψ m hm hψ hmn => by
    obtain ⟨α, h₁, h₂, h₃⟩ := pull_mul A (TFK (R := R) F) ρ n k k' hk x e hx ψ m hm hψ hmn
    exact ⟨α, h₁, h₂, fun t c ht => h₃ t (fun z => cst (R := R) F z c) ht⟩

end GlobalTheory.UT.PullMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumVOfConvolution
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT

theorem sumV_tail {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) (q : ℚ) (S : Finset Ix) (hS : ∀ i, i ∉ S → (q : WithTop ℚ) ≤ v (x i)) :
    (q : WithTop ℚ) ≤ v (s - ∑ i ∈ S, x i) := by
  classical
  obtain ⟨S', hS'⟩ := h q
  have h1 := hS' (S ∪ S') Finset.subset_union_right
  have h2 : (q : WithTop ℚ) ≤ v (∑ i ∈ (S ∪ S') \ S, x i) :=
    v.map_le_sum fun i hi => hS i (Finset.mem_sdiff.1 hi).2
  have h3 := Finset.sum_sdiff (f := x) (Finset.subset_union_left (s₁ := S) (s₂ := S'))
  have h4 : s - ∑ i ∈ S, x i = (s - ∑ i ∈ S ∪ S', x i) + ∑ i ∈ (S ∪ S') \ S, x i := by
    rw [← h3]; ring
  rw [h4]
  exact v.map_le_add h1 h2

theorem nullV_bdd {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F}
    (h : NullV v x) : ∃ m : ℚ, ∀ i, (m : WithTop ℚ) ≤ v (x i) := by
  have hf := (h 0).image (fun i => (v (x i)).untopD 0)
  obtain ⟨m, hm⟩ := hf.bddBelow
  refine ⟨min m 0, fun i => ?_⟩
  by_cases hi : v (x i) < ((0 : ℚ) : WithTop ℚ)
  · have h1 := hm ⟨i, hi, rfl⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hi)
    simp only [← hr, WithTop.untopD_coe] at h1
    rw [← hr]
    exact WithTop.coe_le_coe.2 ((min_le_left _ _).trans h1)
  · exact (WithTop.coe_le_coe.2 (min_le_right _ _)).trans (not_lt.1 hi)

theorem le_v_mul {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {x y : F} {p r q : ℚ}
    (hx : (p : WithTop ℚ) ≤ v x) (hy : (r : WithTop ℚ) ≤ v y) (h : q = p + r) : (q : WithTop ℚ) ≤ v (x * y) := by
  rw [v.map_mul, h, WithTop.coe_add]
  exact add_le_add hx hy

theorem sumV_of_convolution : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] (a b c : X → F), NullV v a → NullV v b → (∀ α, SumV v (fun χ => a χ * b (α - χ)) (c α)) → ∀ sb sc : F, SumV v b sb → SumV v c sc → sb ≠ 0 → SumV v a (sc / sb) := by
  classical
  intro F _ v X _ a b c ha hb hc sb sc hsb hsc h0 q
  obtain ⟨ma, hma⟩ := nullV_bdd v ha
  obtain ⟨mb, hmb⟩ := nullV_bdd v hb
  have hinv : v sb⁻¹ ≠ ⊤ := v.ne_top_iff.2 (inv_ne_zero h0)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hinv
  set q' : ℚ := q - r with hq'
  refine ⟨(ha (q' - mb)).toFinset, fun T hT => ?_⟩
  set Sb := (hb (q' - ma)).toFinset with hSb
  have hTa : ∀ χ, χ ∉ T → ((q' - mb : ℚ) : WithTop ℚ) ≤ v (a χ) := fun χ hχ =>
    not_lt.1 fun h => hχ (hT ((Set.Finite.mem_toFinset _).2 h))
  have hSb' : ∀ β, β ∉ Sb → ((q' - ma : ℚ) : WithTop ℚ) ≤ v (b β) := fun β hβ =>
    not_lt.1 fun h => hβ ((Set.Finite.mem_toFinset _).2 h)
  set U : Finset X := Finset.image₂ (· + ·) T Sb with hU
  have h1 : ∀ α, (q' : WithTop ℚ) ≤ v (c α - ∑ χ ∈ T, a χ * b (α - χ)) := fun α =>
    sumV_tail v (hc α) q' T fun χ hχ => le_v_mul v (hTa χ hχ) (hmb _) (by ring)
  have h2 : ∀ α, α ∉ U → (q' : WithTop ℚ) ≤ v (c α) := by
    intro α hα
    have : (q' : WithTop ℚ) ≤ v (∑ χ ∈ T, a χ * b (α - χ)) := by
      refine v.map_le_sum fun χ hχ => le_v_mul v (hma _) (hSb' _ fun h => hα ?_) (by ring)
      exact Finset.mem_image₂.2 ⟨χ, hχ, α - χ, h, by simp⟩
    have h3 := v.map_le_add (h1 α) this
    rwa [sub_add_cancel] at h3
  have h3 := sumV_tail v hsc q' U h2
  have h4 : (q' : WithTop ℚ) ≤ v (∑ α ∈ U, (c α - ∑ χ ∈ T, a χ * b (α - χ))) :=
    v.map_le_sum fun α _ => h1 α
  have h5 : ∀ χ ∈ T, ((q' - ma : ℚ) : WithTop ℚ) ≤ v (sb - ∑ α ∈ U, b (α - χ)) := by
    intro χ hχ
    have e : ∑ α ∈ U, b (α - χ) = ∑ β ∈ U.image (· - χ), b β :=
      (Finset.sum_image (f := b) (g := (· - χ)) fun x _ y _ h => sub_left_injective h).symm
    rw [e]
    refine sumV_tail v hsb _ _ fun β hβ => hSb' β fun h => hβ ?_
    exact Finset.mem_image.2 ⟨χ + β, Finset.mem_image₂.2 ⟨χ, hχ, β, h, rfl⟩, by simp⟩
  have h6 : (q' : WithTop ℚ) ≤ v (∑ χ ∈ T, a χ * (sb - ∑ α ∈ U, b (α - χ))) :=
    v.map_le_sum fun χ hχ => le_v_mul v (hma χ) (h5 χ hχ) (by ring)
  have h7 := v.map_le_sub (v.map_le_add h3 h4) h6
  have e : sc / sb - ∑ i ∈ T, a i =
      (sc - ∑ i ∈ U, c i + ∑ α ∈ U, (c α - ∑ χ ∈ T, a χ * b (α - χ)) -
        ∑ χ ∈ T, a χ * (sb - ∑ α ∈ U, b (α - χ))) * sb⁻¹ := by
    simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_comm (s := U) (t := T)]
    field_simp
    ring
  rw [e]
  exact le_v_mul v h7 hr.le (by rw [hq']; ring)

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecComb
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

def secComb {X : Scheme.{0}} {L : LB X} {n : ℕ} (b : Fin n → Γ(X, ⊤)) (t : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (b i) * (t i).f j
  compat := fun i j => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, (t _).compat, DVR.SecOps.resTop_res, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _

theorem sval_secComb {X Y T Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {n : ℕ} (p : Y ⟶ T) (c : Fin n → Γ(T, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (secComb (fun i => p.appTop.hom (c i)) t) r z J = ∑ i, gs (r ≫ p) z ⊤ (c i) * sval (t i) r z J := by
  rw [DVR.SectionScalarValuation.sval_lin (s := secComb (fun i => p.appTop.hom (c i)) t) (fun i => p.appTop.hom (c i)) t
    (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r p z ⊤ trivial (c i))

theorem sum_comb {S X : Type} [CommRing S] [DecidableEq X] {n : ℕ} (w : S) (c a : Fin n → S) (s : Fin n → Finset X)
    (b : Fin n → X → S) (t : X → S) (h₀ : ∀ i, ∀ α ∉ s i, b i α = 0) (h : ∀ i, w * a i = ∑ α ∈ s i, b i α * t α) :
    w * ∑ i, c i * a i = ∑ α ∈ Finset.univ.biUnion s, (∑ i, c i * b i α) * t α := by
  simp only [Finset.sum_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, h i, Finset.mul_sum]
  simp only [_root_.mul_assoc]
  refine Finset.sum_subset (Finset.subset_biUnion_of_mem s (Finset.mem_univ i)) fun α _ hα => ?_
  rw [h₀ i α hα, zero_mul, mul_zero]

theorem expT_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k n : ℕ) (c : Fin n → Γ(T.left, ⊤)) (σ : Fin n → U.SecGT T k) (f : Fin n → ∀ α, SecBT D T k α), (∀ i, U.ExpT T k (σ i) (f i)) → ∃ (σ' : U.SecGT T k) (f' : ∀ α, SecBT D T k α), U.ExpT T k σ' f' ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ' r z J = ∑ i, gs (r ≫ (fst T G).left) z ⊤ (c i) * sval (σ i) r z J) ∧ ∀ α (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J → sval (f' α) r z J = ∑ i, gs (r ≫ (fst T D.P.A).left) z ⊤ (c i) * sval (f i α) r z J := by
  classical
  intro R _ _ I D A G _ _ U T k n c σ f h
  refine ⟨secComb (fun i => (fst T G).left.appTop.hom (c i)) σ,
    fun α => secComb (fun i => (fst T D.P.A).left.appTop.hom (c i)) (fun i => f i α), fun e => ?_,
    fun Z r z J hJ => sval_secComb _ c σ r z hJ, fun α Z r z J hJ => sval_secComb _ c (fun i => f i α) r z hJ⟩
  choose s hs using fun i => h i e
  refine ⟨Finset.univ.biUnion s, fun Z x rG rB h₁ h₂ h₃ z JG J hG hJ => ⟨fun α hα => ?_, ?_⟩⟩
  · rw [sval_secComb _ c (fun i => f i α) rB z hJ]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1 α
      (fun hi => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)), mul_zero]
  · rw [sval_secComb _ c σ rG z hG]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun α _ =>
      (congrArg (· * _) (sval_secComb (fst T D.P.A).left c (fun i => f i α) rB z hJ)).symm)
    rw [h₃]
    exact sum_comb _ _ _ s (fun i α => sval (f i α) rB z J) _
      (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).1) (fun i => (hs i Z x rG rB h₁ h₂ h₃ z JG J hG hJ).2)

end GlobalTheory.UU.ExpLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorsProjectiveRepresentation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PhiProj

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

def cUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := R) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

theorem phiRel_of_ratio (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen)
    (hw' : w'.IsGen) (c : F) (hc : c ≠ 0)
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val)
    (s t : Fam D F k) (h : PhiRel D F k p w s t) : PhiRel D F k p w' s (c • t) := by
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ w' (scaleGen (cUnit (R := R) c hc) w) :=
    corr_of_val D.P.isLB fun z J hJ => Units.ext (by
      rw [hv z J hJ, val_scale hJ, Units.val_mul]
      exact congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)) rfl)
  refine (phiRel_iff hG p w' hw' s _).2 fun a β hβ T ρ z J hJ => ?_
  have h1 := (phiRel_iff hG p w hw s t).1 h a β hβ T ρ z J hJ
  have hu : gs (ρ.left ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      (gm (ρ ≫ fst (TF (R := R) F) D.P.A).left z ⊤ (cUnit (R := R) c hc)).val :=
    gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)
  rw [sval_smul c t β ρ.left z hJ, h1, val_mul hJ, val_mul hJ, val_corr hJ hcorr, val_scale hJ, hu]
  simp only [Units.val_mul]
  ring

theorem exists_scaled {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} (hw : w.IsGen) (c : F) (hc : c ≠ 0) :
    ∃ w' : Frm D F k b, w'.IsGen ∧
      ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  refine ⟨scaleGen (cUnit (R := R) c hc) w, scaleGen_isGen _ w hw, fun z J hJ => ?_⟩
  rw [val_scale hJ, Units.val_mul]
  exact congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)).symm rfl

theorem phiRel_of_equiv (hG : GlobalFnsSt) {k : ℕ} {p p' : QkPt D F k} (he : QkPt.Equiv D F p p')
    {w : Frm D F k p.g.b} (hw : w.IsGen) : ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧
      ∀ s t, PhiRel D F k p w s t → PhiRel D F k p' w' s t := by
  obtain ⟨z, hy, h, hι, ha⟩ := he
  obtain ⟨w', hw', hv⟩ := GlobalTheory.exists_shifted_normalisation k p.g z p'.g.b
    (ha.1.trans (congrArg (p.g.b * ·) hι.1)) w hw
  refine ⟨w', hw', fun s t => ?_⟩
  rw [phiRel_iff hG p w hw, phiRel_iff hG p' w' hw']
  intro H α β hβ T ρ x J hJ
  rw [← GlobalTheory.phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
  exact H (α + k • z) β (by rw [← hβ, hy]; abel) T ρ x J hJ

theorem phiRel_zero (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) (w : Frm D F k p.g.b) (hy : p.y = 0)
    (hg : p.g.IsZero) (hw : FrmOne w) (s : Fam D F k) : PhiRel D F k p w s s := by
  have hb : p.g.b = 1 := hg.1
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ w (LB.oneGen D.P.L) :=
    corr_of_val D.P.isLB fun z J hJ => (hw.2 z J hJ).trans (val_one _).symm
  refine (phiRel_iff hG p w hw.1 s s).2 fun α β hβ T ρ z J hJ => ?_
  obtain rfl : α = β := by rw [← hβ, hy, add_zero]
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e₁ : ρ ≫ DegPre.trPt D F p.g.b = ρ := by rw [hb, H1.trPt_one, Category.comp_id]
  have e₂ : uVal D F k α p.g.b ρ z J = 1 := by
    have e : ρ ≫ fst (TF (R := R) F) D.P.A ≫ p.g.b = 1 := by rw [hb, MonObj.comp_one, MonObj.comp_one]
    rw [uVal, e, C.face₃, inv_one, _root_.mul_one]
    exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  rw [e₁, e₂, val_mul hJ, val_corr hJ (hg.2 α), val_corr hJ hcorr, val_one, _root_.mul_one, _root_.mul_one,
    Units.val_one, _root_.mul_one]

theorem bijective_of_pow {F V : Type} [Field F] [AddCommGroup V] [Module F V] (Φ : V →ₗ[F] V) {k : ℕ} (hk : 1 ≤ k)
    {c : F} (hc : c ≠ 0) (h : ∀ s, (Φ ^ k) s = c • s) : Function.Bijective Φ := by
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  constructor
  · intro a b hab
    have : (Φ ^ (k + 1)) a = (Φ ^ (k + 1)) b := by
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hab]
    rw [h, h] at this
    exact smul_right_injective V hc this
  · intro b
    refine ⟨(Φ ^ k) (c⁻¹ • b), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', h, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem phi_projective : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ Φ : ∀ (p : QkPt D.toPre F k), Frm D.toPre F k p.g.b → (Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ p w, w.IsGen → Function.Bijective (Φ p w) ∧ ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ p w s) ∧ (∀ p w, w.IsGen → ∀ c : F, c ≠ 0 → ∃ w', w'.IsGen ∧ Φ p w' = c • Φ p w) ∧ (∀ p w w', w.IsGen → w'.IsGen → ∃ c : F, c ≠ 0 ∧ Φ p w' = c • Φ p w) ∧ (∀ p p' w, w.IsGen → QkPt.Equiv D.toPre F p p' → ∃ w', w'.IsGen ∧ Φ p' w' = Φ p w) ∧ (∀ p p' p'' w w', w.IsGen → w'.IsGen → QkAdd p p' p'' → ∃ w'', w''.IsGen ∧ Φ p'' w'' = Φ p w ∘ₗ Φ p' w') ∧ ∀ p w, p.y = 0 → p.g.IsZero → FrmOne w → Φ p w = LinearMap.id := by
  intro hL R _ _ _ I _ D F _ _ _ k hk
  have hG : GlobalFnsSt := hL.1.globalFns
  have ex : ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k,
      w.IsGen → ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s := fun p w => by
    by_cases hw : w.IsGen
    · obtain ⟨Φ, h⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
      exact ⟨Φ, fun _ => h⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose Φ hΦ using ex
  have rel : ∀ p w, w.IsGen → ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun p w hw s => (hΦ p w hw s _).2 rfl
  refine ⟨Φ, fun p w hw => ⟨?_, hΦ p w hw⟩, fun p w hw c hc => ?_, fun p w w' hw hw' => ?_,
    fun p p' w hw he => ?_, fun p p' p'' w w' hw hw' hadd => ?_, fun p w hy hg hw => ?_⟩
  · obtain ⟨c, hc, hcs⟩ := H1.phiPow_core hG p w hw
    refine bijective_of_pow (Φ p w) hk hc fun s => ?_
    have h := hcs (fun i => (Φ p w ^ (i : ℕ)) s) (fun i => by
      rw [hΦ p w hw]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at h
    simpa only [Fin.val_last, Fin.val_zero, pow_zero, Module.End.one_apply] using h
  · obtain ⟨w', hw', hv⟩ := exists_scaled hw c hc
    exact ⟨w', hw', LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨c, hc, hv⟩ := CoefBasic.exists_frame_ratio hw hw'
    exact ⟨c, hc, LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨w', hw', h⟩ := phiRel_of_equiv hG he hw
    exact ⟨w', hw', LinearMap.ext fun s => ((hΦ p' w' hw' s _).1 (h s _ (rel p w hw s))).symm⟩
  · obtain ⟨q, hy, hg, he⟩ := hadd
    obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.ThetaMul.phi_mul_core hG p p' q hy hg w w' hw hw'
    obtain ⟨w'', hw'', h⟩ := phiRel_of_equiv hG he hw₂
    exact ⟨w'', hw'', LinearMap.ext fun s =>
      ((hΦ p'' w'' hw'' s _).1 (h s _ (h₂ s _ _ (rel p' w' hw' s) (rel p w hw _)))).symm⟩
  · exact LinearMap.ext fun s => ((hΦ p w hw.1 s s).1 (phiRel_zero hG p w hy hg hw s)).symm

end GlobalTheory.UT.PhiProj
end
end

