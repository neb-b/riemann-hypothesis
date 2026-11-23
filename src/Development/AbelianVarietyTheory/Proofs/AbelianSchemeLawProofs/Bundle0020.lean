module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescentPairing

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem interchange (p q r s x : A) :
    θ (p * q) (r * s) x * θ p q x * θ r s x = θ (p * r) (q * s) x * θ p r x * θ q s x := by
  have a := h.coc p q (r * s) x
  have b := h.coc q r s x
  have c := h.coc r q s x
  have d := h.coc p r (q * s) x
  rw [mul_comm r q, h.s01 r q] at c
  rw [mul_left_comm r q s] at d
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a' := E a; have b' := E b; have c' := E c; have d' := E d
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a' - b' + c' - d'

theorem cubN_mul (k : ℕ) (a b x : A) :
    cubN θ k 1 (a * b) x * θ a b x ^ k = θ (a ^ k) (b ^ k) x * cubN θ k 1 a x * cubN θ k 1 b x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := interchange h (a ^ k) (b ^ k) a b x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ a, pow_succ b, pow_succ (θ a b x), mul_pow a b k]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem cubN_transl (k : ℕ) (y w x : A) (hy : y ^ k = 1) :
    cubN θ k 1 (y * w) x * cubN θ k 1 y w = cubN θ k 1 w x * cubN θ k 1 y (x * w) := by
  have a := cubN_mul h k y w x
  have b := h.N_add k 1 y x w
  rw [hy, h.face, _root_.one_mul] at a
  rw [hy, _root_.mul_one (1 : A), h.face, _root_.one_mul, _root_.mul_one, h.s12 y x w] at b
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  simp only [ofMul_mul] at a' b' ⊢
  linear_combination (norm := abel) a' - b'

end Alg

theorem exists_frame {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (y₀ : Y) (hY : ∀ y : Y, y = y₀) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen := by
  choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y₀)
  have m₀ : ∀ y : Y, y ∈ LB.wchart M φ (fun k => I (φ k)) := fun y => by
    rw [hY y]; exact Set.mem_iInter.2 fun k => hI _
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ (fun k => I (φ k)) := fun j y hy => ⟨hy, m₀ y⟩
  have v : ∀ j (y : Y), y ∈ LB.wchart M φ j →
      gm (𝟙 Y) y _ (res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))) = trF φ ε (𝟙 Y) y j (fun k => I (φ k)) :=
    fun j y hy => (gm_res (𝟙 Y) y (le j) hy _).trans (gm_linComb M φ ε (𝟙 Y) y j _ hy (m₀ y))
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M φ ε).g j (fun k => I (φ k)))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j y hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) y j j' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (v j' y hy.2))).trans ?_)
  exact trF_trans hM φ ε (𝟙 Y) y hy.1 hy.2 (m₀ y)

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem exists_theta {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ A) (hy : y ^ n = 1) :
    ∃ θ : ThetaGrp A L.L n T, θ.pt = y ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, thetaVal θ t a z J = cubN (cubV c z J) n 1 (t ≫ y) a * s := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, y.left] ![(n : ℤ), -n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ y) (snd T A) n
  have e₁ : (fst T A ≫ y) ^ n = 1 :=
    (map_pow (preHom (fst T A)) y n).symm.trans (by rw [hy]; exact map_one _)
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A y).left])
    (ε' := ![(n : ℤ), -n]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A y = (fst T A ≫ y) * snd T A := rfl
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.pullGen L.L _ _ σ (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨⟨y, u, hu⟩, rfl, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

theorem exists_triv {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (θ : ThetaGrp A L.L n T) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (Z : Over S) (t : Z ⟶ T) (z : Z.left) (J), Good L.L z J →
      ∃ s, ∀ a : Z ⟶ A, val u (lift t a).left z J =
        cubN (cubV c z J) n 1 a (t ≫ θ.pt) * ((thetaVal θ t a z J)⁻¹ * s) := by
  obtain ⟨σ, hσ⟩ := exists_frame L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, θ.pt.left] ![(n : ℤ) - 1, 1 - n] p₀ hT
  obtain ⟨N, hN, vN⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (snd T A) (fst T A ≫ θ.pt) n
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (K' := Fin 2)
    (φ' := ![(mulT A T n ≫ translPt A θ.pt).left, (snd T A ^ n).left]) (ε' := ![1, -1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₁ : mulT A T n ≫ translPt A θ.pt = snd T A ^ n * (fst T A ≫ θ.pt) :=
        (lift_translPt θ.pt _ _).trans (mul_comm _ _)
      have e₂ : (fst T A).left ≫ (1 : T ⟶ A).left = (1 : T ⊗ A ⟶ A).left :=
        congrArg (fun q => q.left) (MonObj.comp_one (M := A) (fst T A))
      have e₃ : translPt A θ.pt = snd T A * (fst T A ≫ θ.pt) := mul_comm (fst T A ≫ θ.pt) (snd T A)
      rw [e₁, e₃]
      apply Additive.ofMul.injective
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one, e₂,
        ← Over.comp_left, _root_.one_mul]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![(n : ℤ), -n] θ.φ)
      (LB.pullGen L.L _ _ σ (fst T A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ.isGen)
      (DVR.pullGen_isGen _ _ _ _ hσ _)))
  refine ⟨u, hu, fun Z t z J hJ => ⟨val σ t.left z J, fun a => ?_⟩⟩
  refine (vu _ (lift t a).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN Z (lift t a) z J hJ).trans ?_) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_pull hJ _ _ _).trans ?_)))))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

theorem exists_gen_transl_eq_pairing : GlobalFnsSt → CubeSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → WeilSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε))) := by
  intro _ hC hW _ K _ _ P n x hx
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let p₀ : (baseOver (Spec (CommRingCat.of K))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hT : ∀ p : (baseOver (Spec (CommRingCat.of K))).left, p = p₀ := fun p =>
    Subsingleton.elim (α := PrimeSpectrum K) p p₀
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, 1, hu, Or.inl rfl, fun y c hy hc => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff P.isLB θx θy c).1 (((hW _ P n _).1 θx θy c).1 hc)
  refine corr_of_val P.isLB fun z J hJ => ?_
  have e : 𝟙 (baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left = (lift (fst _ P.A) (snd _ P.A)).left := by
    rw [lift_fst_snd]; rfl
  rw [e]
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg (_ * ·) (val_const (c ^ (1 : ℤ)) _ _ z J))).symm)
  rw [← Over.comp_left, lift_translT, zpow_one]
  obtain ⟨s, hs⟩ := vu _ (fst _ P.A) z J hJ
  obtain ⟨s', hs'⟩ := vy _ (fst _ P.A) z J hJ
  have k₁ := hcm _ (fst _ P.A) (snd _ P.A) z J hJ
  have C : IsCub (cubV cb z J) := by
    as_aux_lemma =>
      refine {
        face x y := by
          have := val_corr hJ (cb.face 0) (lift x y).left
          rw [val_one] at this
          refine Eq.trans ?_ this
          refine Eq.trans ?_ (val_cub cb (lift x y) hJ (pzero P.A _) (x2 P.A 0) (x2 P.A 1)).symm
          congr 1 <;> simp [x2, pzero, Hom.one_def]
        s01 x y w := by
          have := (val_corr hJ cb.cubeSymmetric_swap_first (lift x (lift y w)).left).trans (val_cub cb (lift x (lift y w)) hJ _ _ _)
          refine Eq.trans this ?_
          congr 1 <;> simp [x3]
        s12 x y w := by
          have := (val_corr hJ cb.cubeSymmetric_swap_last (lift x (lift y w)).left).trans (val_cub cb (lift x (lift y w)) hJ _ _ _)
          refine Eq.trans this ?_
          congr 1 <;> simp [x3]
        coc x x' x'' y := by
          have := val_corr hJ cb.cocycle (lift x (lift x' (lift x'' y))).left
          have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb _ hJ _ _ _) (val_cub cb _ hJ _ _ _))).symm.trans
            (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb _ hJ _ _ _) (val_cub cb _ hJ _ _ _))))
          have a₀ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 0 = x := by simp [x4]
          have a₁ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 1 = x' := by simp [x4]
          have a₂ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 2 = x'' := by simp [x4]
          have a₃ : lift x (lift x' (lift x'' y)) ≫ x4 P.A 3 = y := by simp [x4]
          have b₀ : lift x (lift x' (lift x'' y)) ≫ padd P.A (x4 P.A 0) (x4 P.A 1) = x * x' :=
            (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
          have b₁ : lift x (lift x' (lift x'' y)) ≫ padd P.A (x4 P.A 1) (x4 P.A 2) = x' * x'' :=
            (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
          rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
      }
  have k₂ := cubN_transl C n (fst _ P.A ≫ θy.pt) (snd _ P.A) (fst _ P.A ≫ θx.pt)
    ((map_pow (preHom (fst _ P.A)) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' (snd _ P.A)
  have t₂ := hs' ((fst _ P.A ≫ θx.pt) * snd _ P.A)
  apply Additive.ofMul.injective
  have E := fun {p q : ((baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left.presheaf.stalk z)ˣ} (e : p = q) =>
    congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

end GlobalTheory.DescentPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GeneratorSchemeProperties
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory

namespace GenScheme

def pb {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (f.appLE U W h).hom

section Calc

variable {X Y Z : Scheme.{0}}

theorem res_pb (f : Y ⟶ X) (U : X.Opens) (W W' : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W)
    (a : Γ(X, U)ˣ) : res h' (pb f U W h a) = pb f U W' (h'.trans h) a :=
  Units.ext (congr($(f.appLE_map h (homOfLE h').op).hom a.val))

theorem pb_res (f : Y ⟶ X) (U U' : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U') (h' : U' ≤ U)
    (a : Γ(X, U)ˣ) : pb f U' W h (res h' a) = pb f U W (h.trans (f.preimage_mono h')) a :=
  Units.ext (congr($(f.map_appLE h (homOfLE h').op).hom a.val))

theorem pb_pb (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    pb g V W h' (pb f U V h a) = pb (g ≫ f) U W (h'.trans (g.preimage_mono h)) a :=
  Units.ext (congr($(Scheme.Hom.appLE_comp_appLE g f U V W h h').hom a.val))

theorem pullU_eq (f : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)ˣ) :
    pullU f U a = pb f U _ le_rfl a :=
  Units.ext (congr($(f.app_eq_appLE (U := U)).hom a.val))

theorem res_res {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a :=
  Units.ext (congr($((X.presheaf.map_comp (homOfLE h).op (homOfLE h').op).symm).hom a.val))

theorem res_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a :=
  Units.ext (congr($(X.presheaf.map_id (Opposite.op U)).hom a.val))

theorem pb_top_val (f : Y ⟶ X) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) (a : Γ(X, ⊤)ˣ) :
    (pb f ⊤ ⊤ h a).val = f.appTop.hom a.val := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl

end Calc

section One

variable {B Z : Scheme.{0}} (L : LB B) (b : Z ⟶ B)

def Compat (s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ) : Prop :=
  ∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_right : L.U i ⊓ L.U i' ≤ L.U i')) (s i') =
    pullU b _ (L.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : L.U i ⊓ L.U i' ≤ L.U i)) (s i)

variable (j : L.ι) (hj : ⊤ ≤ b ⁻¹ᵁ L.U j)

def extend (t : Γ(Z, ⊤)ˣ) (i : L.ι) : Γ(Z, b ⁻¹ᵁ L.U i)ˣ :=
  pb b (L.U j ⊓ L.U i) _ (fun x hx => ⟨hj trivial, hx⟩) (L.g j i) * res le_top t

variable {L}

theorem compat_extend (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : Compat L b (extend L b j hj t) := by
  intro i i'
  have h := congrArg (pb b (L.U j ⊓ L.U i ⊓ L.U i') (b ⁻¹ᵁ (L.U i ⊓ L.U i'))
    (fun x hx => ⟨⟨hj trivial, hx.1⟩, hx.2⟩)) (hL.cocycle j i i')
  rw [map_mul, pb_res, pb_res, pb_res] at h
  simp only [extend, map_mul, res_pb, res_res, pullU_eq]
  rw [← h, ← _root_.mul_assoc, _root_.mul_comm (pb b _ _ _ (L.g i i'))]

theorem res_extend_self (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : res hj (extend L b j hj t j) = t := by
  have h := congrArg (pb b (L.U j) ⊤ hj) (hL.g_self j)
  rw [pb_res, map_one] at h
  simp only [extend, map_mul, res_pb, res_res, res_self]
  rw [h, _root_.one_mul]

theorem eq_extend {s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ} (hs : Compat L b s) (i : L.ι) :
    s i = extend L b j hj (res hj (s j)) i := by
  have h := congrArg (res (show b ⁻¹ᵁ L.U i ≤ b ⁻¹ᵁ (L.U j ⊓ L.U i) from
    fun x hx => ⟨hj trivial, hx⟩)) (hs j i)
  rw [map_mul, res_res, res_res, res_self, pullU_eq, res_pb] at h
  rw [h, extend, res_res]

theorem compat_pb {G : Scheme.{0}} {q : G ⟶ B} {u : ∀ i : L.ι, Γ(G, q ⁻¹ᵁ L.U i)ˣ}
    (hu : Compat L q u) (g : Z ⟶ G) (hg : g ≫ q = b) :
    Compat L b fun i => pb g (q ⁻¹ᵁ L.U i) (b ⁻¹ᵁ L.U i) (by rw [← hg]; exact le_rfl) (u i) := by
  subst hg
  intro i i'
  have h := congrArg (pb g (q ⁻¹ᵁ (L.U i ⊓ L.U i')) ((g ≫ q) ⁻¹ᵁ (L.U i ⊓ L.U i')) le_rfl) (hu i i')
  rw [map_mul, pb_res, pb_res, pullU_eq, pb_pb] at h
  rw [res_pb, res_pb, pullU_eq]
  exact h

end One

section Many

variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}


variable (N q u) in
def Univ : Prop :=
  ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ),
    (∀ k, Compat (N k) b (s k)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i,
      (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val =
        (s k i).val

theorem exists_hom (hN : ∀ k, (N k).IsLB) (hU : Univ N q u) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (t : κ → Γ(Z, ⊤)ˣ) :
    ∃ (g : Z ⟶ G) (hg : g ≫ q = b), ∀ k,
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (by subst hg; exact hj k) (u k (j k)) = t k := by
  obtain ⟨g, ⟨hg, h⟩, -⟩ := hU Z b (fun k => extend (N k) b (j k) (hj k) (t k))
    fun k => compat_extend b (j k) (hj k) (hN k) (t k)
  refine ⟨g, hg, fun k => ?_⟩
  have e : pb g (q ⁻¹ᵁ (N k).U (j k)) (b ⁻¹ᵁ (N k).U (j k)) (by rw [← hg]; exact le_rfl) (u k (j k)) =
      extend (N k) b (j k) (hj k) (t k) (j k) := Units.ext (h k (j k))
  rw [← res_extend_self b (j k) (hj k) (hN k) (t k), ← e, res_pb]

theorem hom_ext (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) {Z : Scheme.{0}}
    (j : ∀ k, (N k).ι) (g g' : Z ⟶ G) (hg : g' ≫ q = g ≫ q)
    (hj : ∀ k, ⊤ ≤ g ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)) (hj' : ∀ k, ⊤ ≤ g' ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k))
    (h : ∀ k, pb g' (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj' k) (u k (j k)) =
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj k) (u k (j k))) : g' = g := by
  have c := fun k => compat_pb (g ≫ q) (hu k) g rfl
  have c' := fun k => compat_pb (g ≫ q) (hu k) g' hg
  refine (hU Z (g ≫ q) _ c).unique ⟨hg, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩
  have e := eq_extend (g ≫ q) (j k) (hj k) (c k) i
  have e' := eq_extend (g ≫ q) (j k) (hj k) (c' k) i
  simp only [res_pb] at e e'
  rw [h k, ← e] at e'
  exact congrArg Units.val e'

open SplitTorus in
theorem torus_hom_ext {S : Scheme.{0}} {T : Over S} {a a' : T ⟶ splitTorus S (κ →₀ ℤ)}
    (h : ∀ k, val a (Finsupp.single k 1) = val a' (Finsupp.single k 1)) : a = a' := by
  apply (pointsEquiv T (κ →₀ ℤ)).injective
  refine Finsupp.addHom_ext' fun k => AddMonoidHom.ext_int ?_
  exact Additive.toMul.injective (Units.ext (h k))

open SplitTorus in
theorem exists_torus_hom {S : Scheme.{0}} {T : Over S} (t : κ → Γ(T.left, ⊤)ˣ) :
    ∃ a : T ⟶ splitTorus S (κ →₀ ℤ), ∀ k, val a (Finsupp.single k 1) = (t k).val := by
  refine ⟨ofVal (Finsupp.liftAddHom fun k => zmultiplesHom _ (Additive.ofMul (t k))), fun k => ?_⟩
  rw [val_ofVal]
  simp


open SplitTorus in
theorem exists_isPullback (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u)
    {V : Scheme.{0}} (v : V ⟶ B) (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ v ⁻¹ᵁ (N k).U (j k)) :
    ∃ p : (splitTorus V (κ →₀ ℤ)).left ⟶ G, IsPullback p (splitTorus V (κ →₀ ℤ)).hom q v := by
  let T := splitTorus V (κ →₀ ℤ)
  have lands : ∀ {Z : Scheme.{0}} (c : Z ⟶ V) k, ⊤ ≤ (c ≫ v) ⁻¹ᵁ (N k).U (j k) :=
    fun c k => c.preimage_mono (hj k)
  have lands' : ∀ {Z : Scheme.{0}} (a : Z ⟶ G) (c : Z ⟶ V) (_ : a ≫ q = c ≫ v) k,
      ⊤ ≤ a ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := fun a c h k => by
    rw [← Scheme.Hom.comp_preimage, h]; exact lands c k
  obtain ⟨p, hp, hpu⟩ := exists_hom hN hU (T.hom ≫ v) j (lands T.hom)
    fun k => (isUnit_val (𝟙 T) (Finsupp.single k 1)).unit
  have key : ∀ {Z : Over V} (m : Z ⟶ T) k (h : ⊤ ≤ (m.left ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)),
      (pb (m.left ≫ p) (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k))).val = val m (Finsupp.single k 1) := by
    intro Z m k h
    rw [← pb_pb m.left p _ ⊤ ⊤ (lands' p T.hom hp k) le_rfl, hpu, pb_top_val]
    exact (val_eq m _).symm
  have ex : ∀ s : PullbackCone q v, ∃ l : s.pt ⟶ T.left, l ≫ p = s.fst ∧ l ≫ T.hom = s.snd := by
    intro s
    obtain ⟨l, hl⟩ := exists_torus_hom (T := Over.mk s.snd)
      fun k => pb s.fst (q ⁻¹ᵁ (N k).U (j k)) ⊤ (lands' _ _ s.condition k) (u k (j k))
    have w : l.left ≫ T.hom = s.snd := Over.w l
    have w' : (l.left ≫ p) ≫ q = s.snd ≫ v := by
      rw [Category.assoc, hp, ← Category.assoc, w]
    refine ⟨l.left, hom_ext hu hU j _ _ (w'.trans s.condition.symm) (lands' _ _ s.condition)
      (lands' _ _ w') fun k => Units.ext ?_, w⟩
    exact (key l k _).trans (hl k)
  refine ⟨p, ⟨hp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (ex s).choose)
    (fun s => (ex s).choose_spec.1) (fun s => (ex s).choose_spec.2) fun s m h₁ h₂ => ?_⟩⟩
  obtain ⟨h₃, h₄⟩ := (ex s).choose_spec
  generalize (ex s).choose = l at h₃ h₄
  have : (Over.homMk m h₂ : Over.mk s.snd ⟶ T) = Over.homMk l h₄ := by
    refine torus_hom_ext fun k => ?_
    have hm : ⊤ ≤ (m ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₁]; exact lands' _ _ s.condition k
    have hl : ⊤ ≤ (l ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₃]; exact lands' _ _ s.condition k
    rw [← key (Over.homMk m h₂ : Over.mk s.snd ⟶ T) k hm, ← key (Over.homMk l h₄ : Over.mk s.snd ⟶ T) k hl]
    have aux : ∀ (a a' : s.pt ⟶ G) (_ : a = a') h h',
        pb a (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k)) = pb a' (q ⁻¹ᵁ (N k).U (j k)) ⊤ h' (u k (j k)) := by
      rintro a _ rfl _ _; rfl
    exact congrArg Units.val (aux _ _ (h₁.trans h₃.symm) _ _)
  exact congrArg (·.left) this

theorem prop_of_torus [Fintype κ] (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V : Scheme.{0}, P (splitTorus V (κ →₀ ℤ)).hom)
    (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) : P q := by
  let W : (∀ k, (N k).ι) → B.Opens := fun j =>
    ⟨⋂ k, ((N k).U (j k) : Set B), isOpen_iInter_of_finite fun k => ((N k).U (j k)).isOpen⟩
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    have : ∀ k, ∃ i, x ∈ (N k).U i := fun k =>
      TopologicalSpace.Opens.mem_iSup.1 ((hN k).cover.ge trivial)
    choose j hj using this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun j => ?_
  obtain ⟨p, hp⟩ := exists_isPullback hN hu hU (W j).ι j
    fun k x _ => Set.mem_iInter.1 x.2 k
  have h := (isPullback_morphismRestrict q (W j)).flip
  rw [← h.isoIsPullback_hom_snd _ _ hp, MorphismProperty.cancel_left_of_respectsIso P]
  exact hP _

end Many

end GenScheme

theorem generatorScheme_properties :
    ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∀ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), ((∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val) → IsAffineHom q ∧ Smooth q ∧ Surjective q ∧ IsSeparated q ∧ GeometricallyConnected q := by
  intro B κ _ N hN G q u ⟨hu, hU⟩
  have hc : GeometricallyConnected q := by
    have : IsZariskiLocalAtTarget @GeometricallyConnected := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    exact GenScheme.prop_of_torus @GeometricallyConnected (fun V => inferInstance) hN hu hU
  have : IsZariskiLocalAtTarget @IsAffineHom :=
    HasAffineProperty.instIsZariskiLocalAtTarget (P := @IsAffineHom)
  have : IsZariskiLocalAtTarget @Smooth := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have ha : IsAffineHom q := GenScheme.prop_of_torus @IsAffineHom (fun V => inferInstance) hN hu hU
  refine ⟨ha, GenScheme.prop_of_torus @Smooth (fun V => ?_) hN hu hU, inferInstance, inferInstance, hc⟩
  have := H1.torus_dim V (κ →₀ ℤ)
  exact SmoothOfRelativeDimension.smooth (Module.finrank ℤ (κ →₀ ℤ)) _

end GlobalTheory
end
end

