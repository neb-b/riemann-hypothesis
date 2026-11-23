module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiValuesThroughBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section
namespace GlobalTheory.Mum.TensTor.PsiVal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem stalk_gm {Z Y : Scheme.{0}} (f : Z ⟶ Y) {X : Scheme.{0}} (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (f z) ∈ U)
    (a : Γ(X, U)ˣ) : (f.stalkMap z).hom (gm r (f z) U a).val = (gm (f ≫ r) z U a).val := by
  rw [gm_val r (f z) U h, gm_val (f ≫ r) z U h]
  have := Scheme.Hom.germ_stalkMap_apply f (r ⁻¹ᵁ U) z h ((r.app U).hom a.val)
  rw [this]
  rfl

theorem stalk_val {Z Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (h : f z ∈ LB.wchart L φ (fun k => J (f ≫ φ k))) :
    (f.stalkMap z).hom (val t (𝟙 Y) (f z) (fun ψ => J (f ≫ ψ))).val = (val t f z J).val := by
  rw [val_of t (𝟙 Y) (f z) _ (fun k => J (f ≫ φ k)) (fun k => by simp only [Category.id_comp])]
  refine (stalk_gm f (𝟙 Y) z _ h _).trans ?_
  rw [Category.comp_id]
  rfl

theorem toStk_vF {F : Type} [Field F] {Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (z : Sp F) (J : (Sp F ⟶ X) → L.ι) (hJ : Good L z J) :
    toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem φ r) _

theorem toUnit_left {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem stalkU {Z Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    Units.map (f.stalkMap z).hom.toMonoidHom (val t (𝟙 Y) (f z) (fun ψ => J (f ≫ ψ))) = val t f z J :=
  Units.ext (stalk_val t f z J (hJ.mem φ f))

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem good_of (ν : NumOf D F N) (z : Sp F) : Good D.P.L z ν.J := fun ψ => (top_le_iff_mem ψ _ z).1 (ν.good ψ)

theorem goodK_of (ν : NumOf D F N) (z : Sp F) : Good D.P.L (jFK (R := R) F z) (fun ψ => ν.J (jFK (R := R) F ≫ ψ)) :=
  fun ψ => (top_le_iff_mem (jFK (R := R) F ≫ ψ) _ z).1 (ν.good _)

theorem wv_toStk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) (z : Sp F)
    (p : Sp F ⟶ D'.P.A.left) (hp : (ν'.eA x).left = p) :
    toStk z (wv T ν ν' x) = (gm p z _ (T.w.s (fun k => ν.J (p ≫ tensφ T.pr k), ν'.J p))).val := by
  subst hp
  exact toStk_valF _ _ z (show (ν'.eA x).left z ∈ LB.wchart D.P.L (tensφ T.pr) (fun k => ν.J ((ν'.eA x).left ≫ tensφ T.pr k)) ⊓
    D'.P.L.U (ν'.J (ν'.eA x).left) from ⟨(good_of ν z).mem _ _, good_of ν' z _⟩) _

theorem rig_val (ν : NumOf D F N) (z : Sp F) :
    val (LB.pullGen D.P.L _ _ D.rig (toUnit (TK R)).left) (jFK (R := R) F) z ν.J = val D.rig (jFK (R := R) F ≫ jK R) z ν.J := by
  rw [val_pull (good_of ν z), toUnit_left]
  rfl

theorem psi_m (ν : NumOf D F N) (z : Sp F) (χ : N.X) :
    Units.map (toStk z).toMonoidHom (N.ψ χ) = val (D.psi (ν.eX χ)) (jFK (R := R) F) z ν.J * val D.rig (jFK (R := R) F ≫ jK R) z ν.J := by
  apply Units.ext
  change toStk z (N.ψ χ : F) = _
  rw [ν.ψ_eq χ, map_mul, toStk_vF _ _ z _ (good_of ν z), toStk_vF _ _ z _ (good_of ν z)]
  rfl

theorem tau_m (ν : NumOf D F N) (z : Sp F) (a b : N.X) :
    val (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) z ν.J = Units.map (toStk z).toMonoidHom (N.τ a b) := by
  have hG := good_of ν z
  unfold DegPre.tau DegPre.rigK
  rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv, rig_val ν z]
  rw [NumD.τ, map_div, map_div, psi_m ν z, psi_m ν z, psi_m ν z, map_add (f := _)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

theorem pt_eq (ν' : NumOf D' F N') (χ : N'.X) : (ν'.eA (N'.c χ)).left = jFK (R := R) F ≫ D'.xK (ν'.eX χ) := by
  rw [ν'.c_eq]
  simp only [DegPre.cF, DegPre.xK, ptK, Over.comp_left, toUnit_left]
  rfl

theorem w_stalk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (z : Sp F) (y : D'.X) :
    Units.map (Scheme.Hom.stalkMap (jFK (R := R) F) z).hom.toMonoidHom
      (gm (D'.xK y) (jFK (R := R) F z) _ (T.w.s (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k),
        ν'.J (jFK (R := R) F ≫ D'.xK y)))) =
    gm (jFK (R := R) F ≫ D'.xK y) z _ (T.w.s (fun k => ν.J ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k),
        ν'.J (jFK (R := R) F ≫ D'.xK y))) := by
  have e : (fun k => ν.J ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k)) =
      (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k)) := funext fun k => by rw [Category.assoc]
  rw [e]
  apply Units.ext
  refine stalk_gm (jFK (R := R) F) (D'.xK y) z _ ?_ _
  exact (show (jFK (R := R) F ≫ D'.xK y) z ∈ LB.wchart D.P.L (tensφ T.pr) (fun k => ν.J (jFK (R := R) F ≫ D'.xK y ≫ tensφ T.pr k)) ⊓
    D'.P.L.U (ν'.J (jFK (R := R) F ≫ D'.xK y)) from ⟨Set.mem_iInter.2 fun k => by
      have := good_of ν z ((jFK (R := R) F ≫ D'.xK y) ≫ tensφ T.pr k)
      rwa [Category.assoc] at this, good_of ν' z _⟩)

theorem psi_stk (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (z : Sp F) (χ' : N'.X) :
    toStk z (N'.ψ χ' : F) = toStk z (wv T ν ν' (N'.c χ')) *
      toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) *
      (val D'.rig (jFK (R := R) F ≫ jK R) z ν'.J).val := by
  have key := T.psi (ν'.eX χ') (jFK (R := R) F z) (fun ψ => ν.J (jFK (R := R) F ≫ ψ)) (fun ψ => ν'.J (jFK (R := R) F ≫ ψ))
    (goodK_of ν z) (goodK_of ν' z)
  have key2 := congrArg (Units.map (Scheme.Hom.stalkMap (jFK (R := R) F) z).hom.toMonoidHom) key
  rw [map_mul, stalkU _ _ z _ (good_of ν' z), w_stalk] at key2
  simp only [map_prod, map_zpow, stalkU _ _ z ν.J (good_of ν z)] at key2
  have hL : toStk z (N'.ψ χ' : F) = (Units.map (toStk z).toMonoidHom (N'.ψ χ')).val := rfl
  have hP : toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) =
      (∏ i, ∏ j, val (D.tau (T.xe (ν'.eX χ') i) (T.xe (ν'.eX χ') j)) (jFK (R := R) F) z ν.J ^ W i j).val := by
    change (Units.map (toStk z).toMonoidHom _).val = _
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, ← tau_m ν z, show ν.eX (chi T ν ν' χ' i) = T.xe (ν'.eX χ') i from ν.eX.apply_symm_apply _,
      show ν.eX (chi T ν ν' χ' j) = T.xe (ν'.eX χ') j from ν.eX.apply_symm_apply _]
  rw [hL, psi_m ν' z χ', hP, wv_toStk T ν ν' _ z _ (pt_eq ν' χ'), key2]
  simp only [Units.val_mul]
  try ring

theorem psi_main (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ' : N'.X) :
    (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  obtain ⟨z⟩ : Nonempty (Sp F) := ⟨(default : PrimeSpectrum F)⟩
  have h0 := psi_stk T ν ν' z 0
  have hc : chi T ν ν' 0 = 0 := funext fun i => by
    show ν.eX.symm (T.xe (ν'.eX 0) i) = 0
    rw [map_zero, map_zero, Pi.zero_apply, map_zero]
  have hp : (∏ i, ∏ j, N.τ (chi T ν ν' 0 i) (chi T ν ν' 0 j) ^ W i j : Fˣ) = 1 := by
    rw [hc]
    exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [Pi.zero_apply, NumD.τ_zero_left, one_zpow]
  rw [NumD.ψ_zero, NumD.c_zero, hp, Units.val_one, map_one, _root_.mul_one] at h0
  apply (toStk z).injective
  rw [map_mul, map_mul, psi_stk T ν ν' z χ']
  linear_combination (-(toStk z (wv T ν ν' (N'.c χ')) *
      toStk z ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F))) * h0

end GlobalTheory.Mum.TensTor.PsiVal


open GlobalTheory.Mum.TensTor.PsiVal in
theorem GlobalTheory.Mum.TensTor.tensFacts_psi : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ χ', (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' χ'
  exact psi_main T ν ν' χ'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPairingEqProdFactorPairings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.PairVal

theorem cubN_succ {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (k : ℕ) (m x : A) :
    cubN θ (k + 1) 1 m x = cubN θ k 1 m x * θ (m ^ k) m x := by
  simp [cubN, Finset.prod_range_succ]

theorem comp_one {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (j : Fin r) : φ 1 j = 1 := by
  have := h 1 1 j
  rw [_root_.one_mul] at this
  exact mul_eq_left.1 this.symm

theorem comp_pow {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (x : B) (m : ℕ) (j : Fin r) : φ (x ^ m) j = φ x j ^ m := by
  induction m with
  | zero => simp [comp_one h]
  | succ m ih => rw [pow_succ, h, ih, pow_succ]

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem cube_prod (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (U : N'.A → Fˣ)
    (hφ : ∀ x y j, φ (x * y) j = φ x j * φ y j)
    (hc : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1) (k : ℕ) (b a : N'.A) :
    cubN N'.θ k 1 b a * U (b ^ k * a) * U 1 * (U b * U a) ^ k =
      (∏ i, ∏ j, (cubN N.θ k 1 (φ b i * φ b j) (φ a i * φ a j) /
        (cubN N.θ k 1 (φ b i) (φ a i) * cubN N.θ k 1 (φ b j) (φ a j))) ^ W i j) *
      U (b ^ k) * U a * (U (b * a) * U 1) ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have h := hc (b ^ k) b a
    simp only [comp_pow hφ, ← mul_pow] at h
    have split : ∀ P p Q q R s : Fˣ, P * p / (Q * q * (R * s)) = P / (Q * R) * (p / (q * s)) := by
      intro P p Q q R s
      rw [_root_.mul_mul_mul_comm, div_mul_div_comm]
    simp only [cubN_succ, split, mul_zpow, Finset.prod_mul_distrib, pow_succ]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_mul, ofMul_pow] at ih' h' ⊢
    linear_combination (norm := abel) ih' + h'

theorem torusExtensionPair_correction_eq_value_quotient (N : NumD F) (g g' : N.Gt) (z z' : N.X) (C C₁ C₂ : Fˣ) :
    g'.s z * g.s z' / (N.θ (N.c z') g'.b (N.c z) * N.θ (N.c z') g'.b g.b * N.θ (N.c z) g.b (N.c z' * g'.b)) *
      (C / (C₁ * C₂)) = (g * g').s (z + z') * C / (g.s z * C₁ * (g'.s z' * C₂)) := by
  rw [NumD.Gt.mul_s, N.c_add]
  have m1 := g.mult z z'
  have m2 := g'.mult z z'
  have co := N.cub.coc (N.c z) (N.c z') g'.b g.b
  rw [N.cub.s12 (N.c z * N.c z') g'.b g.b] at co
  rw [N.cub.s12 (N.c z') g'.b (N.c z), N.cub.s01 (N.c z') (N.c z), N.cub.s12 (N.c z) g.b]
  apply Additive.ofMul.injective
  replace m1 := congrArg Additive.ofMul m1
  replace m2 := congrArg Additive.ofMul m2
  replace co := congrArg Additive.ofMul co
  simp only [ofMul_mul, ofMul_div] at m1 m2 co ⊢
  linear_combination (norm := abel) -m1 - m2 + co

end GlobalTheory.Mum.TensTor.PairVal

namespace GlobalTheory.Mum.TensTor.PairVal

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem tk_tens (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (hT : TensFacts W φ e wv) (U : N'.A → Fˣ) (hU : ∀ x, wv x = (U x : F)) {k : ℕ} (q' p' : N'.QT k)
    (qs ps : Fin r → N.QT k) (hq : QRelV W φ e wv q' qs) (hp : QRelV W φ e wv p' ps) :
    N'.tk q' p' * (U p'.1.2.b * U q'.1.2.b) ^ k =
      (∏ i, ∏ j, (N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j))) ^ W i j) *
      (U (p'.1.2.b * q'.1.2.b) * U 1) ^ k := by
  obtain ⟨hφ, -, -, -, -, -, hcube, -⟩ := hT
  have hcU : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1 := by
    intro x y u
    apply Units.ext
    simp only [Units.val_mul, ← hU]
    exact hcube x y u
  have hA := cube_prod W φ U hφ hcU k p'.1.2.b q'.1.2.b
  simp only [hp.2.1, hq.2.1] at hA
  have hG := hq.2.2 p'.1.1.toAdd
  simp only [hU, ← Units.val_mul] at hG
  replace hG := Units.ext hG
  simp only [hp.1, hq.2.1, ← N'.QT_pow_b p'] at hG
  have hX : ∀ i j, N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) =
      (qs j).1.2.s (ps i).1.1.toAdd * (qs i).1.2.s (ps j).1.1.toAdd /
        (N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (N.c (ps i).1.1.toAdd) *
          N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (qs i).1.2.b *
          N.θ (N.c (ps i).1.1.toAdd) (qs i).1.2.b (N.c (ps j).1.1.toAdd * (qs j).1.2.b)) *
      (cubN N.θ k 1 ((ps i).1.2.b * (ps j).1.2.b) ((qs i).1.2.b * (qs j).1.2.b) /
        (cubN N.θ k 1 (ps i).1.2.b (qs i).1.2.b * cubN N.θ k 1 (ps j).1.2.b (qs j).1.2.b)) :=
    fun i j => (torusExtensionPair_correction_eq_value_quotient N (qs i).1.2 (qs j).1.2 (ps i).1.1.toAdd (ps j).1.1.toAdd _ _ _).symm
  simp only [hX, mul_zpow, Finset.prod_mul_distrib]
  rw [NumD.tk]
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hG' := congrArg Additive.ofMul hG
  simp only [ofMul_mul, ofMul_pow] at hA' hG' ⊢
  linear_combination (norm := abel) hA' + hG'

theorem wp_eq_prod : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  intro F _ N N' r W φ e wv hT k _ q' p' qs ps hq hp
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hT.2.2.2.2.2.1 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  have h1 := tk_tens W φ e wv hT U hU q' p' qs ps hq hp
  have h2 := tk_tens W φ e wv hT U hU p' q' ps qs hp hq
  rw [mul_comm q'.1.2.b p'.1.2.b] at h2
  have hper : ∀ i j, N.wp (qs i) (ps j) * N.wp (qs j) (ps i) =
      N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) /
        (N.tk (ps i * ps j) (qs i * qs j) / (N.tk (ps i) (qs i) * N.tk (ps j) (qs j))) := by
    intro i j
    have e1 := WpPairing.wp_mul_left N (qs i) (qs j) (ps i * ps j)
    have e2 := WpPairing.wp_mul_right N (qs i) (ps i) (ps j)
    have e3 := WpPairing.wp_mul_right N (qs j) (ps i) (ps j)
    simp only [NumD.wp] at e1 e2 e3 ⊢
    apply Additive.ofMul.injective
    replace e1 := congrArg Additive.ofMul e1
    replace e2 := congrArg Additive.ofMul e2
    replace e3 := congrArg Additive.ofMul e3
    simp only [ofMul_mul, ofMul_div] at e1 e2 e3 ⊢
    linear_combination (norm := abel) -e1 - e2 - e3
  have hR : ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j =
      ∏ i, ∏ j, (N.wp (qs i) (ps j) * N.wp (qs j) (ps i)) ^ W i j := by
    simp only [Matrix.add_apply, Matrix.transpose_apply, zpow_add, Finset.prod_mul_distrib, mul_zpow]
    congr 1
    rw [Finset.prod_comm]
  have hD : ∀ f g : Fin r → Fin r → Fˣ, ∏ i, ∏ j, (f i j / g i j) ^ W i j =
      (∏ i, ∏ j, f i j ^ W i j) / ∏ i, ∏ j, g i j ^ W i j := by
    intro f g
    simp only [div_zpow, Finset.prod_div_distrib]
  rw [hR]
  simp only [hper]
  rw [hD]
  rw [NumD.wp]
  apply Additive.ofMul.injective
  have h1' := congrArg Additive.ofMul h1
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_div] at h1' h2' ⊢
  linear_combination (norm := abel) h1' - h2'

end GlobalTheory.Mum.TensTor.PairVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem cube_corr {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (xi xj yi yj ui uj : A) (sji sij tji tij : U) :
    sji * tji / θ xi yj uj * (sij * tij / θ xj yi ui) /
        (θ xj (yj * uj) xi * θ xj (yj * uj) (yi * ui) * θ xi (yi * ui) (xj * (yj * uj))) *
      (θ (xi * xj) (yi * yj) (ui * uj) / (θ xi yi ui * θ xj yj uj)) =
    sji * sij / (θ xj yj xi * θ xj yj yi * θ xi yi (xj * yj)) *
      (tji * tij / (θ xj uj xi * θ xj uj ui * θ xi ui (xj * uj))) := by
  have hp : ∀ x y z, θ x y z = θ y x z ∧ θ x y z = θ x z y ∧ θ x y z = θ z x y ∧ θ x y z = θ y z x ∧
      θ x y z = θ z y x := fun x y z =>
    ⟨h.s01 x y z, h.s12 x y z, (h.s12 x y z).trans (h.s01 x z y), (h.s01 x y z).trans (h.s12 y x z),
      ((h.s01 x y z).trans (h.s12 y x z)).trans (h.s01 y z x)⟩
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have c0 := E (show θ (xi * xj) (yi * yj) (ui * uj) * θ xi xj (ui * uj) = θ xi (xj * yi * yj) (ui * uj) * θ xj (yi * yj) (ui * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * yj) (ui * uj))
  have c1 := E (show θ (xj * ui) uj (yi * yj) * θ xj ui (yi * yj) = θ xj (ui * uj) (yi * yj) * θ ui uj (yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui uj (yi * yj))
  have c2 := E (show θ (xj * ui) (yi * yj) uj * θ xj ui uj = θ xj (yi * yj * ui) uj * θ ui (yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui (yi * yj) uj)
  have c3 := E (show θ (xj * yj) uj (yi * ui) * θ xj yj (yi * ui) = θ xj (yj * uj) (yi * ui) * θ yj uj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj uj (yi * ui))
  have c4 := E (show θ (xj * yj) (yi * ui) uj * θ xj yj uj = θ xj (yi * yj * ui) uj * θ yj (yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj (yi * ui) uj)
  have c5 := E (show θ (xj * yi) ui yj * θ xj yi yj = θ xj (yi * ui) yj * θ yi ui yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi ui yj)
  have c6 := E (show θ (xj * yi) yj ui * θ xj yi ui = θ xj (yi * yj) ui * θ yi yj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi yj ui)
  have c7 := E (show θ (xi * xj) (yj * uj) (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj * uj) (yi * ui) * θ xj (yj * uj) (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yj * uj) (yi * ui))
  have c8 := E (show θ (xi * xj) (yi * ui) (yj * uj) * θ xi xj (yj * uj) = θ xi (xj * yi * ui) (yj * uj) * θ xj (yi * ui) (yj * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) (yj * uj))
  have c9 := E (show θ (xi * ui) uj (xj * yi * yj) * θ xi ui (xj * yi * yj) = θ xi (ui * uj) (xj * yi * yj) * θ ui uj (xj * yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj (xj * yi * yj))
  have c10 := E (show θ (xi * ui) (xj * yi * yj) uj * θ xi ui uj = θ xi (xj * yi * yj * ui) uj * θ ui (xj * yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui (xj * yi * yj) uj)
  have c11 := E (show θ (xi * yj) uj (xj * yi * ui) * θ xi yj (xj * yi * ui) = θ xi (yj * uj) (xj * yi * ui) * θ yj uj (xj * yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj uj (xj * yi * ui))
  have c12 := E (show θ (xi * yj) (xj * yi * ui) uj * θ xi yj uj = θ xi (xj * yi * yj * ui) uj * θ yj (xj * yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj (xj * yi * ui) uj)
  have c13 := E (show θ (xi * ui) uj xj * θ xi ui xj = θ xi (ui * uj) xj * θ ui uj xj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj xj)
  have c14 := E (show θ (xi * ui) xj uj * θ xi ui uj = θ xi (xj * ui) uj * θ ui xj uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui xj uj)
  have c15 := E (show θ (xi * xj) uj ui * θ xi xj ui = θ xi (xj * uj) ui * θ xj uj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj uj ui)
  have c16 := E (show θ (xi * xj) ui uj * θ xi xj uj = θ xi (xj * ui) uj * θ xj ui uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj ui uj)
  have c17 := E (show θ (xi * yi) ui (xj * yj) * θ xi yi (xj * yj) = θ xi (yi * ui) (xj * yj) * θ yi ui (xj * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi ui (xj * yj))
  have c18 := E (show θ (xi * yi) (xj * yj) ui * θ xi yi ui = θ xi (xj * yi * yj) ui * θ yi (xj * yj) ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi (xj * yj) ui)
  have c19 := E (show θ (xi * xj) (yi * ui) yj * θ xi xj yj = θ xi (xj * yi * ui) yj * θ xj (yi * ui) yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) yj)
  have c20 := E (show θ (xi * xj) yj (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj) (yi * ui) * θ xj yj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj yj (yi * ui))
  have p0 := E (hp xj (yj * uj) xi).2.2.1
  have p1 := E (hp xj yj xi).2.2.1
  have p2 := E (hp xj yj yi).2.1
  have p3 := E (hp xj uj xi).2.2.1
  have p4 := E (hp (xj * ui) uj (yi * yj)).2.2.1
  have p5 := E (hp xj ui (yi * yj)).2.1
  have p6 := E (hp xj (ui * uj) (yi * yj)).2.1
  have p7 := E (hp ui uj (yi * yj)).2.2.1
  have p8 := E (hp (xj * ui) (yi * yj) uj).1
  have p9 := E (hp ui (yi * yj) uj).1
  have p10 := E (hp (xj * yj) uj (yi * ui)).2.1
  have p11 := E (hp yj uj (yi * ui)).2.1
  have p12 := E (hp (xj * yi) ui yj).2.1
  have p13 := E (hp xj (yi * ui) yj).2.1
  have p14 := E (hp yi ui yj).2.1
  have p15 := E (hp (xi * xj) (yj * uj) (yi * ui)).2.1
  have p16 := E (hp xi (xj * yj * uj) (yi * ui)).2.1
  have p17 := E (hp xj (yj * uj) (yi * ui)).2.1
  have p18 := E (hp (xi * ui) uj (xj * yi * yj)).2.2.1
  have p19 := E (hp xi ui (xj * yi * yj)).2.1
  have p20 := E (hp xi (ui * uj) (xj * yi * yj)).2.1
  have p21 := E (hp ui uj (xj * yi * yj)).2.2.1
  have p22 := E (hp (xi * ui) (xj * yi * yj) uj).1
  have p23 := E (hp ui (xj * yi * yj) uj).1
  have p24 := E (hp (xi * yj) uj (xj * yi * ui)).2.1
  have p25 := E (hp xi (yj * uj) (xj * yi * ui)).2.1
  have p26 := E (hp yj uj (xj * yi * ui)).2.1
  have p27 := E (hp (xi * ui) uj xj).2.2.1
  have p28 := E (hp xi ui xj).2.1
  have p29 := E (hp xi (ui * uj) xj).2.1
  have p30 := E (hp ui uj xj).2.2.1
  have p31 := E (hp (xi * ui) xj uj).1
  have p32 := E (hp ui xj uj).1
  have p33 := E (hp (xi * xj) uj ui).2.1
  have p34 := E (hp xi (xj * uj) ui).2.1
  have p35 := E (hp (xi * yi) ui (xj * yj)).2.1
  have p36 := E (hp xi (yi * ui) (xj * yj)).2.1
  have p37 := E (hp yi ui (xj * yj)).2.1
  have p38 := E (hp (xi * xj) (yi * ui) yj).2.1
  have p39 := E (hp xi (xj * yi * ui) yj).2.1
  rw [← mul_assoc xj yj uj]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) c0 - c1 + c2 + c3 - c4 + c5 - c6 + c7 - c8 - c9 + c10 + c11 - c12 + c13 - c14 - c15 + c16 + c17 - c18 + c19 - c20 - p0 + p1 + p2 + p3 + p4 + p5 - p6 - p7 - p8 + p9 - p10 + p11 - p12 + 2 • p13 + p14 - p15 + p16 + p17 + p18 + p19 - p20 - p21 - p22 + p23 - p24 + p25 + p26 - p27 - p28 + p29 + p30 + p31 - p32 + p33 - p34 - p35 + p36 + p37 - p38 + p39

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem vmul_comb {U : Type} [CommGroup U] (s1 s2 t P1 P2 P Q wc wb wb' wcb wcb' wbb' wcbb' w1 : U)
    (h1 : s1 * wc * wb = P1 * wcb * w1) (h2 : s2 * wc * wb' = P2 * wcb' * w1)
    (h3 : t * wcbb' * wc * wb * wb' = Q * wcb * wcb' * wbb' * w1) (h4 : P * Q = P1 * P2) :
    s1 * s2 / t * wc * wbb' = P * wcbb' * w1 := by
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a1 := E h1; have a2 := E h2; have a3 := E h3; have a4 := E h4
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) a1 + a2 - a3 - a4

theorem gtRelV_mul : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv →
    ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us) := by
  intro F _ N N' r W φ e wv hT v' u' vs us hv hu
  obtain ⟨hφ, -, -, -, hφc, hw0, hcub, -⟩ := hT
  refine ⟨fun j => ?_, fun χ' => ?_⟩
  · show φ (v'.b * u'.b) j = (vs j).b * (us j).b
    rw [hφ, hv.1, hu.1]
  · let w : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
    let Pf : (Fin r → N.Gt) → Fˣ := fun g => ∏ i, ∏ j, ((g j).s (e χ' i) * (g i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (g j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (g j).b (g i).b *
        N.θ (N.c (e χ' i)) (g i).b (N.c (e χ' j) * (g j).b))) ^ W i j
    let Qf : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) ((us i).b * (us j).b) /
      (N.θ (N.c (e χ' i)) (vs i).b (us i).b * N.θ (N.c (e χ' j)) (vs j).b (us j).b)) ^ W i j
    have h1 : v'.s χ' * w (N'.c χ') * w v'.b = Pf vs * w (N'.c χ' * v'.b) * w 1 := Units.ext (hv.2 χ')
    have h2 : u'.s χ' * w (N'.c χ') * w u'.b = Pf us * w (N'.c χ' * u'.b) * w 1 := Units.ext (hu.2 χ')
    have h3 := hcub (N'.c χ') v'.b u'.b
    rw [mul_assoc (N'.c χ') v'.b u'.b] at h3
    simp only [hφc, hv.1, hu.1] at h3
    have h3' : N'.θ (N'.c χ') v'.b u'.b * w (N'.c χ' * (v'.b * u'.b)) * w (N'.c χ') * w v'.b * w u'.b =
        Qf * w (N'.c χ' * v'.b) * w (N'.c χ' * u'.b) * w (v'.b * u'.b) * w 1 := Units.ext h3
    have h4 : Pf (vs * us) * Qf = Pf vs * Pf us := by
      simp only [Pf, Qf]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow]
      exact congrArg (· ^ W i j) (cube_corr N.cub (N.c (e χ' i)) (N.c (e χ' j)) (vs i).b (vs j).b (us i).b (us j).b
        ((vs j).s (e χ' i)) ((vs i).s (e χ' j)) ((us j).s (e χ' i)) ((us i).s (e χ' j)))
    exact congrArg Units.val (vmul_comb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3' h4)

end GlobalTheory.Mum.TensTor
end

