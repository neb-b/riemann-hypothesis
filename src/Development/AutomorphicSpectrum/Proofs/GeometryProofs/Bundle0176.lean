module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TheoremOfCubeSectionValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem exists_lin_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x a : T ⟶ G) (m : ℕ) (hx : x ^ m = 1) :
    ∃ v : FG L.L T.left, (∀ (U : Type) [CommGroup U] (h : (T.left ⟶ G.left) → U),
        v.sum U h = h (x * a ^ m).left * (h (a ^ m).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left) ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → ρ ≫ a = 1 → v.v ρ.left z J = 1 := by
  obtain ⟨t₂, ht₂, v₂⟩ := exists_cubN c (1 : T ⟶ G) a x m
  obtain ⟨t₁, ht₁, v₁⟩ := exists_cubN c (1 : T ⟶ G) x a m
  refine ⟨FG.mul ⟨Fin 8, _, _, t₂, ht₂⟩ (FG.inv ⟨Fin 8, _, _, t₁, ht₁⟩), fun U _ h => ?_, fun T' ρ z J hJ hρ => ?_⟩
  · rw [FG.sum_mul, FG.sum_inv]
    simp only [FG.sum, Fin.prod_univ_succ, Fin.prod_univ_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hx,
      _root_.one_mul, _root_.mul_one, mul_comm a x, mul_comm (a ^ m) x]
    apply Additive.ofMul.injective
    simp [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rw [FG.v_mul hJ, FG.v_inv]
    show val t₂ ρ.left z J * (val t₁ ρ.left z J)⁻¹ = 1
    rw [v₂ T' ρ z J hJ, v₁ T' ρ z J hJ, hρ, (isCub_cubV c hJ).N_one]
    have : cubN (cubV c z J) m (ρ ≫ (1 : T ⟶ G)) 1 (ρ ≫ x) = 1 :=
      Finset.prod_eq_one fun _ _ => (isCub_cubV c hJ).face₂ _ _ |>.symm ▸ rfl
    rw [this]
    simp

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

theorem alg {R : Type*} [CommRing R] (t s : R) (g g' a r v : Rˣ) (N n : ℕ)
    (h : t * ((g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2)) ^ n =
      ((g' ^ (n : ℤ)).val * s) ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) :
    t * (a.val * r.val ^ (N ^ 2)) ^ n = s ^ (N ^ 2) * v.val ^ n := by
  have hz : ∀ u : Rˣ, u ^ (-((N : ℤ) ^ 2)) = (u ^ (N ^ 2))⁻¹ := fun u => by
    rw [zpow_neg, ← zpow_natCast]; push_cast; rfl
  have e₁ : g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a * (g * r) ^ (N ^ 2) = g * (a * r ^ (N ^ 2)) := by
    rw [hz, zpow_one, mul_pow]
    calc g * (g ^ (N ^ 2))⁻¹ * a * (g ^ (N ^ 2) * r ^ (N ^ 2))
        = g * (a * r ^ (N ^ 2)) * ((g ^ (N ^ 2))⁻¹ * g ^ (N ^ 2)) := by ac_rfl
      _ = _ := by rw [inv_mul_cancel, _root_.mul_one]
  have e₂ : ((g' ^ (n : ℤ)) ^ (N ^ 2)) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v) ^ n = g ^ n * v ^ n := by
    rw [hz, zpow_one, zpow_natCast, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n]
    calc g' ^ (N ^ 2 * n) * (g ^ n * (g' ^ (N ^ 2 * n))⁻¹ * v ^ n)
        = g ^ n * v ^ n * (g' ^ (N ^ 2 * n) * (g' ^ (N ^ 2 * n))⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, _root_.mul_one]
  have l : (g ^ (1 : ℤ) * g ^ (-((N : ℤ) ^ 2)) * a).val * (g * r).val ^ (N ^ 2) = g.val * (a.val * r.val ^ (N ^ 2)) := by
    have := congrArg Units.val e₁
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have m : (g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n = g.val ^ n * v.val ^ n := by
    have := congrArg Units.val e₂
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  rw [l] at h
  apply (g ^ n).isUnit.mul_right_inj.1
  simp only [Units.val_pow_eq_pow_val]
  calc g.val ^ n * (t * (a.val * r.val ^ (N ^ 2)) ^ n)
      = t * (g.val * (a.val * r.val ^ (N ^ 2))) ^ n := by rw [mul_pow g.val]; ring
    _ = _ := h
    _ = ((g' ^ (n : ℤ)).val ^ (N ^ 2) * (g ^ (1 : ℤ) * g' ^ (-((N : ℤ) ^ 2)) * v).val ^ n) * s ^ (N ^ 2) := by
        rw [mul_pow (g' ^ (n : ℤ)).val]; ring
    _ = g.val ^ n * v.val ^ n * s ^ (N ^ 2) := by rw [m]
    _ = _ := by ring

variable {F : Type} [Field F] {X S : Scheme.{0}}

theorem charts {L : LB X} {q : X ⟶ X} {e : S ⟶ X} {b : Sp F ⟶ S} {o y : Sp F ⟶ X}
    (hbe : b ≫ e = o) (hoq : o ≫ q = o) (hyq : y ≫ q = o) {n N : ℕ}
    (w : LB.Gen (LB.LinComb L (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => e) (fun _ => 1))) (hr : rig.IsGen)
    (s : Out.H0 L n) (T : F) (i₀ i : L.ι) (h₀ : ⊤ ≤ o ⁻¹ᵁ L.U i₀) (hi : ⊤ ≤ y ⁻¹ᵁ L.U i)
    (hE : T * (valF o _ (w.s ![i₀, i₀]).val * valF b _ (rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n =
      valF y _ (s.f fun _ => i) ^ (N ^ 2) * valF y _ (w.s ![i₀, i]).val ^ n)
    (z : Sp F) (J : (Sp F ⟶ X) → L.ι) (hJ : Good L z J) :
    toStk z T * ((val w o z J).val * (val rig b z J).val ^ (N ^ 2)) ^ n =
      sval s y z J ^ (N ^ 2) * (val w y z J).val ^ n := by
  have m₀ : o z ∈ L.U i₀ := (top_le_iff_mem _ _ z).1 h₀
  have mi : y z ∈ L.U i := (top_le_iff_mem _ _ z).1 hi
  have mo : o z ∈ L.U (J o) := hJ o
  have my : y z ∈ L.U (J y) := hJ y
  have wm : ∀ (r : Sp F ⟶ X), r ≫ q = o → ∀ a c : L.ι, o z ∈ L.U a → r z ∈ L.U c →
      r z ∈ LB.wchart L (K := Fin 2) ![q, 𝟙 X] ![a, c] := by
    intro r hr' a c ha hc
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show q (r z) ∈ L.U a
      have : q (r z) = o z := by rw [← hr']; rfl
      rw [this]; exact ha
    · exact hc
  have rm : ∀ a : L.ι, o z ∈ L.U a → b z ∈ LB.wchart L (K := PUnit) (fun _ => e) (fun _ => a) := by
    intro a ha
    refine Set.mem_iInter.2 fun _ => ?_
    show e (b z) ∈ L.U a
    have : e (b z) = o z := by rw [← hbe]; rfl
    rw [this]; exact ha
  have sm : ∀ a : L.ι, y z ∈ L.U a → y z ∈ LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a) :=
    fun a ha => Set.mem_iInter.2 fun _ => ha
  have a₁ : toStk z (valF o _ (w.s ![i₀, i₀]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] *
        gm o z (LB.wchart L ![q, 𝟙 X] ![J o, J o]) (w.s ![J o, J o])).val :=
    (toStk_valF o _ z (wm o hoq _ _ m₀ m₀) _).trans
      (congrArg Units.val (gen_trans hw o z (wm o hoq _ _ m₀ m₀) (wm o hoq (J o) (J o) mo mo)))
  have a₂ : toStk z (valF b _ (rig.s fun _ => i₀).val) =
      (trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) *
        gm b z (LB.wchart L (fun _ => e) (fun _ => J o)) (rig.s fun _ => J o)).val :=
    (toStk_valF b _ z (rm _ m₀) _).trans (congrArg Units.val (gen_trans hr b z (rm _ m₀) (rm (J o) mo)))
  have a₃ : toStk z (valF y _ (s.f fun _ => i)) =
      (trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y)).val *
        gs y z (LB.wchart L (fun _ => 𝟙 X) (fun _ => J y)) (s.f fun _ => J y) :=
    (GlobalTheory.ThetaInValues.toStk_valF' y _ z (sm _ mi) _).trans (sec_trans s y z (sm _ mi) (sm (J y) my))
  have a₄ : toStk z (valF y _ (w.s ![i₀, i]).val) =
      (trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] *
        gm y z (LB.wchart L ![q, 𝟙 X] ![J o, J y]) (w.s ![J o, J y])).val :=
    (toStk_valF y _ z (wm y hyq _ _ m₀ mi) _).trans
      (congrArg Units.val (gen_trans hw y z (wm y hyq _ _ m₀ mi) (wm y hyq (J o) (J y) mo my)))
  have hE' := congrArg (toStk z) hE
  simp only [map_mul, map_pow] at hE'
  rw [a₁, a₂, a₃, a₄] at hE'
  have f₁ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] o z ![i₀, i₀] ![J o, J o] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm o z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (o ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (o ≫ 𝟙 X) z _ (L.g i₀ (J o)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hoq, Category.comp_id]
  have f₂ : trF (L := L) (K := PUnit) (fun _ => e) (fun _ => 1) b z (fun _ => i₀) (fun _ => J o) =
      gm o z _ (L.g i₀ (J o)) := by
    rw [trF, Fintype.prod_unique]
    show gm (b ≫ e) z _ (L.g i₀ (J o)) ^ (1 : ℤ) = _
    rw [hbe, zpow_one]
  have f₃ : trF (L := L) (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) y z (fun _ => i) (fun _ => J y) =
      gm y z _ (L.g i (J y)) ^ (n : ℤ) := by
    rw [trF, Fintype.prod_unique]
    show gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (n : ℤ) = _
    rw [Category.comp_id]
  have f₄ : trF (L := L) (K := Fin 2) ![q, 𝟙 X] ![1, -((N : ℤ) ^ 2)] y z ![i₀, i] ![J o, J y] =
      gm o z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm y z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) := by
    rw [trF, Fin.prod_univ_two]
    show gm (y ≫ q) z _ (L.g i₀ (J o)) ^ (1 : ℤ) * gm (y ≫ 𝟙 X) z _ (L.g i (J y)) ^ (-((N : ℤ) ^ 2)) = _
    rw [hyq, Category.comp_id]
  rw [f₁, f₂, f₃, f₄] at hE'
  rw [val_of w o z J ![J o, J o] (Fin.forall_fin_two.2 ⟨congrArg J hoq, congrArg J (Category.comp_id _)⟩),
    val_of rig b z J (fun _ => J o) (fun _ => congrArg J hbe),
    sval_of s y z J (fun _ => J y) (fun _ => congrArg J (Category.comp_id _)),
    val_of w y z J ![J o, J y] (Fin.forall_fin_two.2 ⟨congrArg J hyq, congrArg J (Category.comp_id _)⟩)]
  exact alg _ _ _ _ _ _ _ N n hE'

end GlobalTheory.CompanionTheory.Ar.Sl.Transl.TorsChart

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem torsVal_charts : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F), TorsVal P s y N T → ∀ (z : Sp F) (J : (Sp F ⟶ G.left) → P.L.ι), Good P.L z J → ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen ∧ toStk z T * ((val (Z := Sp F) w (1 : Over.mk b ⟶ G).left z J).val * (val (Z := Sp F) P.rig b z J).val ^ (N ^ 2)) ^ n = sval (Z := Sp F) s y.left z J ^ (N ^ 2) * (val (Z := Sp F) w y.left z J).val ^ n := by
  intro S G _ _ P n s F _ b y N T hT z J hJ
  obtain ⟨-, hy, w, i₀, i, hw, h₀, hi, hE⟩ := hT
  have key : ∀ t : Over.mk b ⟶ G, t ^ N = 1 →
      t.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    intro t ht
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ht]
  have hbe : b ≫ eSec G = (1 : Over.mk b ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl
  refine ⟨w, hw, TorsChart.charts (e := eSec G) hbe (key 1 (one_pow N)) (key y hy) w hw P.rig P.rigGen
    s T i₀ i h₀ hi hE z J hJ⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesIdentityPowerRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem values_units_identity {G : Type*} [CommGroup G] (m N : ℕ)
    (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : G)
    (h3 : A = bo * (bz ^ (N ^ 2))⁻¹ * Wy)
    (h4 : B = bo * (bo ^ (N ^ 2))⁻¹ * Wo)
    (h5 : R = bo * R')
    (h7 : Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ =
      Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹)
    (h8 : Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2))
    (h9 : u0 = e0 * (R ^ (m ^ 2))⁻¹)
    (h10 : e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1) :
    (Wo * R' ^ (N ^ 2)) ^ ((m ^ 2) ^ 2) * bz ^ (m ^ 2 * (N * m) ^ 2) =
      Wk1 * R ^ ((N * m) ^ 2) * Wkz⁻¹ * (up ^ ((N * m) ^ 2))⁻¹ * Wy ^ ((m ^ 2) ^ 2) := by
  apply Additive.ofMul.injective
  have e3 := congrArg Additive.ofMul h3
  have e4 := congrArg Additive.ofMul h4
  have e5 := congrArg Additive.ofMul h5
  have e7 := congrArg Additive.ofMul h7
  have e8 := congrArg Additive.ofMul h8
  have e9 := congrArg Additive.ofMul h9
  have e10 := congrArg Additive.ofMul h10
  first
    | (simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, ← natCast_zsmul, Nat.cast_pow,
          Nat.cast_mul] at e3 e4 e5 e7 e8 e9 e10 ⊢
       linear_combination (norm := module) e7 + (((m : ℤ) ^ 2) ^ 2) • e3
         - (((m : ℤ) ^ 2) ^ 2) • e4 - ((N : ℤ) ^ 2 * ((m : ℤ) ^ 2) ^ 2) • e5
         + ((N : ℤ) ^ 2 * (m : ℤ) ^ 2) • e9 + e8 + ((N : ℤ) ^ 2) • e10)
    | (simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e3 e4 e5 e7 e8 e9 e10 ⊢
       linear_combination (norm := module) e7 + (((m : ℤ) ^ 2) ^ 2) • e3
         - (((m : ℤ) ^ 2) ^ 2) • e4 - ((N : ℤ) ^ 2 * ((m : ℤ) ^ 2) ^ 2) • e5
         + ((N : ℤ) ^ 2 * (m : ℤ) ^ 2) • e9 + e8 + ((N : ℤ) ^ 2) • e10)

theorem values_cancel_of_unit_identity {C : Type*} [CommRing C] (T2 T' s t D : C) (X Z Y V c K : Cˣ)
    (a : T2 * (X : C) = s * (Y : C)) (b : (Z : C) * s = D * (t * (V : C)))
    (c1 : T' * (c : C) = t * (K : C)) (hU : X * Z = c * K⁻¹ * V * Y) :
    T2 = D * T' := by
  have hU' : (X : C) * (Z : C) = (c : C) * ((K⁻¹ : Cˣ) : C) * (V : C) * (Y : C) := by
    simpa only [Units.val_mul] using congrArg Units.val hU
  have hK : ((K⁻¹ : Cˣ) : C) * (K : C) = 1 := Units.inv_mul K
  refine (Units.mul_left_inj (X * Z)).mp ?_
  rw [Units.val_mul]
  linear_combination (Z : C) * a + (Y : C) * b - D * T' * hU'
    - D * (V : C) * (Y : C) * ((K⁻¹ : Cˣ) : C) * c1 - D * t * (V : C) * (Y : C) * hK

theorem values_identity_units : ∀ {C : Type} [CommRing C] (m N : ℕ) (T T' th sv d : C) (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : Cˣ), T' * ((Wk1 : C) * (R : C) ^ ((N * m) ^ 2)) = th ^ ((N * m) ^ 2) * (Wkz : C) → T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2) = sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2) → A = bo * (bz ^ (N ^ 2))⁻¹ * Wy → B = bo * (bo ^ (N ^ 2))⁻¹ * Wo → R = bo * R' → ((bz ^ (m ^ 2) : Cˣ) : C) * sv = d * (th * ((up⁻¹ : Cˣ) : C)) → Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ = Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹ → Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2) → u0 = e0 * (R ^ (m ^ 2))⁻¹ → e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1 → T ^ (m ^ 2) = d ^ ((N * m) ^ 2) * T' := by
  intro C _ m N T T' th sv d Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz e1 e2 h3 h4 h5 e6 h7
    h8 h9 h10
  have hU := GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_units_identity m N Wk1 Wkz Wkx Wm1 Wmx A B up u0
    e0 R R' Wo Wy bo bz h3 h4 h5 h7 h8 h9 h10
  rw [← inv_pow] at hU
  have e2' : (T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2)) ^ (m ^ 2) =
      (sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2)) ^ (m ^ 2) := by rw [e2]
  have e6' : (((bz ^ (m ^ 2) : Cˣ) : C) * sv) ^ ((N * m) ^ 2) =
      (d * (th * ((up⁻¹ : Cˣ) : C))) ^ ((N * m) ^ 2) := by rw [e6]
  refine GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_cancel_of_unit_identity (T ^ (m ^ 2)) T' (sv ^ ((N * m) ^ 2))
    (th ^ ((N * m) ^ 2)) (d ^ ((N * m) ^ 2)) ((Wo * R' ^ (N ^ 2)) ^ ((m ^ 2) ^ 2))
    (bz ^ (m ^ 2 * (N * m) ^ 2)) (Wy ^ ((m ^ 2) ^ 2)) (up⁻¹ ^ ((N * m) ^ 2))
    (Wk1 * R ^ ((N * m) ^ 2)) Wkz ?_ ?_ ?_ hU
  · push_cast at e2' ⊢
    linear_combination e2'
  · push_cast at e6' ⊢
    linear_combination e6'
  · push_cast
    exact e1

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end

