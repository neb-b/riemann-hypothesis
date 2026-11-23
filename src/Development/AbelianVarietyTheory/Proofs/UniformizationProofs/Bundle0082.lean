module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProdExpOppositeTranslates
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ProdTransl

theorem comp_inv_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G)
    (k : ℕ) : ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ :=
  (map_inv (preHom (G := G) ρ) (x ^ k)).trans (congrArg (·⁻¹) (map_pow (preHom (G := G) ρ) x k))

theorem value_identity {A A' B O : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommRing O] (Θ : B → B → B → Oˣ)
    (θ' : A' → A' → A' → Oˣ) (p : A →* B) (q : A →* A') (W : A → Oˣ) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * Θ (p x) (p y) (p u)) (k : ℕ) (x y : A) (hx : q x = 1) (X Y : B) (hX : X = p x)
    (hY : Y = p y) (n n' : Oˣ) (hn : n * W 1 = W x) (hn' : n' * W 1 = W (x ^ k)⁻¹) (s s' t : O)
    (ht : t = (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')).val * (s * s')) :
    (W y).val ^ (k + 1) * t = (W (x * y)).val ^ k * s * ((W ((x ^ k)⁻¹ * y)).val ^ 1 * s') := by
  have e := cubN_descent_opposite A A' Oˣ (fun a b c => Θ (p a) (p b) (p c)) θ' q W hc h k x y hx
  have c : cubN (fun a b c => Θ (p a) (p b) (p c)) k 1 x y = cubN Θ k 1 (p x) (p y) := by
    simp only [cubN, map_mul, map_one, map_pow]
  rw [c, map_inv, map_pow, ← hX, ← hY, ← hn, ← hn', mul_comm y, mul_pow] at e
  have e' : W y ^ (k + 1) * (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')) =
      W (x * y) ^ k * W ((x ^ k)⁻¹ * y) := by
    apply mul_right_cancel (b := W 1 ^ (k + 1))
    rw [← e, pow_succ (W 1)]
    generalize W y ^ (k + 1) = u₁
    generalize W 1 ^ k = u₂
    generalize n ^ k = u₃
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  have e'' := congrArg Units.val e'
  rw [Units.val_mul, Units.val_mul (W (x * y) ^ k), Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at e''
  rw [ht, ← _root_.mul_assoc, e'']
  ring

theorem exists_prod {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x : T ⟶ G) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => (k : ℤ))))
    (ϑ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((1 : ℕ) : ℤ))))
    (ν : LB.Gen (LB.LinComb L.L (K := Fin 2) ![x.left, (1 : T ⟶ G).left] ![-1, 1])) (hν : ν.IsGen)
    (ν' : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(x ^ k)⁻¹.left, (1 : T ⟶ G).left] ![-1, 1])) (hν' : ν'.IsGen) :
    ∃ τ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((k + 1 : ℕ) : ℤ))),
      ∀ (T' : Over S) (ρ : T' ⟶ T ⊗ G) (z : T'.left) (J), Good L.L z J →
        sval τ ρ.left z J =
          (cubN (cubV c z J) k 1 (ρ ≫ fst T G ≫ x) (ρ ≫ snd T G) *
            cubV c z J (ρ ≫ snd T G) ((ρ ≫ fst T G ≫ x) ^ k) ((ρ ≫ fst T G ≫ x) ^ k)⁻¹ *
            (val ν (ρ.left ≫ (fst T G).left) z J ^ k * val ν' (ρ.left ≫ (fst T G).left) z J)).val *
          (sval σ (ρ.left ≫ (translT G x).left) z J * sval ϑ (ρ.left ≫ (translT G (x ^ k)⁻¹).left) z J) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN c (1 : T ⊗ G ⟶ G) (fst T G ≫ x) (snd T G) k
  have hX : ∀ {T' : Over S} (ρ : T' ⟶ T), ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ := fun ρ => comp_inv_pow ρ x k
  have e₁ : ∀ u : T ⟶ G, (translT G u).left ≫ (snd T G).left = ((fst T G ≫ u) * snd T G).left := fun u =>
    congrArg (fun q => q.left) (lift_snd (fst T G) (translPt G u))
  have e₂ : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
    congrArg (fun q => q.left) (MonObj.comp_one (M := G) (fst T G) : fst T G ≫ (1 : T ⟶ G) = 1)
  have e₃ : (fst T G).left ≫ (x ^ k)⁻¹.left = ((fst T G ≫ x) ^ k)⁻¹.left := congrArg (fun q => q.left) (hX (fst T G))
  have e₄ : (fst T G).left ≫ x.left = (fst T G ≫ x).left := rfl
  have hu : (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ t (LB.pullGen L.L (thφ G (x3 G)) thε c.t
      (lift (snd T G) (lift ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹)).left))
      (LB.mulGen L.L _ _ _ _ (GeneratorPullback.powGen L.L _ _ (LB.pullGen L.L _ _ ν (fst T G).left) k)
        (LB.pullGen L.L _ _ ν' (fst T G).left))).IsGen :=
    DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ c.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hν _) k)
        (DVR.pullGen_isGen _ _ _ _ hν' _))
  obtain ⟨τ, hτ⟩ := exists_sec L.isLB (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => ((k + 1 : ℕ) : ℤ))
    (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
          ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl
            (prod_cub (snd T G) ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹ h)))
          (Fintype.prod_sum_type _))) (Fintype.prod_sum_type _))).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, e₁, e₂, e₃, e₄, hX, _root_.one_mul, mul_inv_cancel, mul_inv_cancel_right]
      rw [mul_comm (snd T G) ((fst T G ≫ x) ^ k), mul_comm (snd T G) ((fst T G ≫ x) ^ k)⁻¹]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (genSec _ hu) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec σ (translT G x).left)
      (H1.SectionArithmetic.pullSec ϑ (translT G (x ^ k)⁻¹).left)))
  refine ⟨τ, fun T' ρ z J hJ => (hτ _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val ?_))
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)
      (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)))))⟩
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((hv T' ρ z J hJ).trans ?_) ((val_cub c ρ hJ _ _ _).trans ?_)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((map_pow _ _ _).trans (congrArg (· ^ k) (val_pull hJ _ _ _)))
      (val_pull hJ _ _ _))))
  · rw [MonObj.comp_one]
  · have a : ρ ≫ (fst T G ≫ x) ^ k = (ρ ≫ fst T G ≫ x) ^ k := map_pow (preHom (G := G) ρ) _ _
    have b : ρ ≫ ((fst T G ≫ x) ^ k)⁻¹ = (ρ ≫ (fst T G ≫ x) ^ k)⁻¹ := map_inv (preHom (G := G) ρ) _
    rw [b, a]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

noncomputable def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun u => (Over.map (thick R I e)).map u ≫ fstG I e G) fun a b =>
    Over.OverMorphism.ext ((isGrpPullback_pullback G (thick R I e)).2 T a b _ _ rfl rfl).symm

theorem prodExp_of_normAt (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a a' : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (k : ℕ) (hx : U.TorPt a x) (hx' : U.TorPt a' (x ^ k)⁻¹)
    (ν) (hν : U.NormAt x ν) (ν') (hν' : U.NormAt (x ^ k)⁻¹ ν')
    (σ : U.SecGT (TA R W) k) (ϑ : U.SecGT (TA R W) 1) (f) (g) (hf : U.ExpT (TA R W) k σ f)
    (hg : U.ExpT (TA R W) 1 ϑ g) :
    ∃ τ : U.SecGT (TA R W) (k + 1), U.ProdExp (TA R W) (twist a f) (twist a' g) τ := by
  obtain ⟨τ, hτ⟩ := exists_prod U.P.c x k σ ϑ ν hν.1 ν' hν'.1
  refine ⟨τ, fun e => ?_⟩
  obtain ⟨s, hs⟩ := expansion_translate_torus hG R I D A G U W a x hx k σ f hf e
  obtain ⟨s', hs'⟩ := expansion_translate_torus hG R I D A G U W a' _ hx' 1 ϑ g hg e
  refine ⟨s, s', fun Z y rG rB h₁ h₂ h₃ z JG J hJG hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : (Over.map (thick R I e)).obj T ⟶ G := ρ ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxl : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hxe : ρ ≫ fst _ _ ≫ x = push I e G T xe := Over.OverMorphism.ext hxl.symm
  have hy : ρ ≫ snd _ _ = push I e G T yo := Over.OverMorphism.ext h₁
  have hxe' : ρ ≫ fst _ _ ≫ (x ^ k)⁻¹ = push I e G T (xe ^ k)⁻¹ := by
    rw [map_inv, map_pow, ← hxe, ← Category.assoc, ← Category.assoc]
    exact comp_inv_pow _ x k
  have tr : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      (ue * yo).left ≫ (fstG I e G).left = rG ≫ (translPt G u).left := fun u ue hu =>
    congrArg (fun q => q.left) ((map_mul (push I e G T) ue yo).trans
      ((congrArg₂ (· * ·) hu.symm hy.symm).trans (MonObj.comp_mul ρ (fst _ _ ≫ u) (snd _ _)).symm))
  have pt : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      ue.left ≫ (fstG I e G).left = (rG ≫ (fst (TA R W) G).left) ≫ u.left := fun u ue hu =>
    (congrArg (fun q => q.left) hu.symm).trans (Category.assoc _ _ _).symm
  have h1 : ρ ≫ fst _ _ ≫ (1 : TA R W ⟶ G) = push I e G T 1 := by
    rw [map_one, MonObj.comp_one, MonObj.comp_one]
  have hq : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ρ ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext (hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (pt x xe hxe)).1).trans this
  obtain ⟨a₁, a₂⟩ := hs Z y (xe * yo).left rG rB h₁ h₂ h₃ (tr x xe hxe) z JG J hJG hJ
  obtain ⟨b₁, b₂⟩ := hs' Z y ((xe ^ k)⁻¹ * yo).left rG rB h₁ h₂ h₃ (tr _ _ hxe') z JG J hJG hJ
  refine ⟨a₁, b₁, Eq.trans ?_ (congrArg₂ (· * ·) a₂ b₂)⟩
  exact value_identity (O := Z.presheaf.stalk z) (cubV U.P.c (T := (Over.map (thick R I e)).obj T) z JG)
    (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J) (push I e G T)
    (MonoidHom.mk' (fun u : T ⟶ thickObj R I e G => GlobalTheory.TorusCoord.im (U.gt e) u) (GlobalTheory.TorusCoord.im_mul (U.gt e)))
    (fun u => U.wv e u.left z JG J) (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ)
    (U.w_vals e T z JG J hJG hJ (fun u => U.wv e u.left z JG J) (fun _ => rfl)).2.2 k xe yo hq _ _ hxe hy _ _
    (hν.2 e Z (rG ≫ (fst (TA R W) G).left) xe.left (1 : T ⟶ thickObj R I e G).left (pt x xe hxe) (pt 1 1 h1)
      z JG J hJG hJ)
    (hν'.2 e Z (rG ≫ (fst (TA R W) G).left) (xe ^ k)⁻¹.left (1 : T ⟶ thickObj R I e G).left (pt _ _ hxe') (pt 1 1 h1)
      z JG J hJG hJ) _ _ _ (hτ _ ρ z JG hJG)

end GlobalTheory.UU.ProdTransl

theorem GlobalTheory.UU.prodExp_opposite_translates : GlobalFnsSt → AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA V W) k) (ϑ : U.SecGT (TA V W) 1) (f) (g), U.ExpT (TA V W) k σ f → U.ExpT (TA V W) 1 ϑ g → ∃ σ'' : U.SecGT (TA V W) (k + 1), U.ProdExp (TA V W) (twist a f) (twist (a ^ k)⁻¹ g) σ'' := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW a x hx k σ ϑ f g hf hg
  have hm := (GlobalTheory.UU.torPt_group hG V _ D A G U W).2
  have hx' : U.TorPt (a ^ k)⁻¹ (x ^ k)⁻¹ := (hm _ a _ x ((hm a a x x hx).2.2 k)).2.1
  obtain ⟨ν, hν⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW a x hx
  obtain ⟨ν', hν'⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW _ _ hx'
  exact ProdTransl.prodExp_of_normAt hG U a _ x k hx hx' ν hν ν' hν' σ ϑ f g hf hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionImage

open FieldBaseChange

theorem translT_translPt {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x y : T ⟶ A) :
    translT A x ≫ translPt A y = translPt A (y * x) := by
  show lift (fst T A) ((fst T A ≫ x) * snd T A) ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd, _root_.mul_assoc]

theorem translPt_one {S : Scheme.{0}} {A : Over S} [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ 1) * snd T A = _
  rw [MonObj.comp_one, _root_.one_mul]

theorem translT_inv {S : Scheme.{0}} {A T : Over S} [GrpObj A] (x : T ⟶ A) :
    translT A x⁻¹ ≫ translT A x = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, Category.id_comp]
    exact (congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((translT_translPt _ _).trans (by rw [mul_inv_cancel, translPt_one]))

theorem eq_of_gen {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F] (q : Spec (CommRingCat.of F) ⟶ S)
    (x x' : Over.mk q ⟶ P.A)
    (r : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(translPt P.A x).left, (translPt P.A x').left] ![1, -1]))
    (hr : r.IsGen) : x = x' := by
  refine mul_inv_eq_one.1 (P.ktriv F q (x * x'⁻¹) fun p => ⟨⊤, trivial, ?_⟩)
  obtain ⟨w, hw, -⟩ := VVRank.exists_gen_pullTo
    (φ' := ![(translPt P.A (x * x'⁻¹)).left, (snd (Over.mk q) P.A).left]) r hr (translT P.A x'⁻¹).left (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (translT_translPt x'⁻¹ x)
      · exact congrArg (fun q => q.left) ((translT_translPt x'⁻¹ x').trans
          (by rw [mul_inv_cancel, translPt_one])))
  exact exists_isGen_pull (translDiff P.A P.L (x * x'⁻¹)) w hw _

theorem exists_smul_of_phiVal {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ s t t' : Fam D F k, DVR.PhiVal p w s.s t.s → DVR.PhiVal p w' s.s t'.s → t' = c • t := by
  obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (𝟙 _) (fun a => ⟨a, rfl⟩)
    (LB.mulGen D.P.L _ _ _ _ w' (LB.invGen D.P.L _ _ w))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw' (DVR.invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      refine (DVR.prod_sum₂ _ (c := ∏ i, h (DegPre.lineφ D F p.g.b i) ^ DegPre.lineε k i) rfl
        (DVR.prod_neg _ _ rfl)).trans ?_
      exact mul_inv_cancel _)
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun s t t' h h' => DVR.phi_unique p w' h' fun α β e' T ρ z J hJ => ?_⟩
  · rintro rfl
    let z : (TF (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (𝟙 _) z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (gs_zero' _ z ⊤ trivial)
  · have e := ha _ (ρ ≫ fst _ _).left z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id] at e
    refine (DVR.sval_smul c t β ρ.left z hJ).trans ?_
    rw [h α β e' T ρ z J hJ, val_mul hJ, val_mul hJ]
    refine (congrArg (· * _) e.symm).trans ?_
    rw [mul_left_comm, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem pt_eq_of_proportional (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K)))
    {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) {n : ℕ} (hn : 1 ≤ n)
    (θ θ' : ThetaGrp P.A P.L (n : ℤ) (Over.mk q)) (c : Γ((Over.mk q).left, ⊤)ˣ)
    (H : ∀ t u u', IsActOf P.A P.L (n : ℤ) θ t u → IsActOf P.A P.L (n : ℤ) θ' t u' → ∀ y J, Good P.L y J →
      VVRank.sv P.A u' (𝟙 _) y J =
        (gm (𝟙 _ ≫ (fst (Over.mk q) P.A).left) y ⊤ c).val * VVRank.sv P.A u (𝟙 _) y J) : θ.pt = θ'.pt := by
  have hL := P.isLB
  let T := Over.mk q
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ P.A
  have : IsIntegral (T ⊗ P.A).left :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F _
  have hN : ∀ y : (T ⊗ P.A).left, IsIntegrallyClosed ((T ⊗ P.A).left.presheaf.stalk y) := fun y =>
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ (fst T P.A).left
      (inferInstanceAs (Smooth (pullback.fst q P.A.hom)))).2.1 y).2
  obtain ⟨b, hb, -⟩ := BoxSpan.exists_basis hS P 1 le_rfl F q
  have : Nontrivial Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := hb.ne_zero ⟨0, by simp⟩
  let th : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (snd T P.A).left) (fun _ => ((1 : ℕ) : ℤ))) :=
    SecM.toSec P.A (b ⟨0, by simp⟩)
  have tr : ∀ x : T ⟶ P.A, ∃ s : LB.Sec (LB.LinComb P.L (K := PUnit) (fun _ => (translPt P.A x).left) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = sval th (r ≫ (translT P.A x).left) z J := fun x => by
    have e : (translT P.A x).left ≫ (snd T P.A).left = (translPt P.A x).left :=
      congrArg (fun q => q.left) (lift_snd _ _ : translT P.A x ≫ snd T P.A = _)
    obtain ⟨s, hs⟩ := exists_sec hL (φ' := fun _ : PUnit => (translPt P.A x).left) (ε' := fun _ => 1)
      (fun U _ h => by simp only [e, Fintype.prod_unique, Nat.cast_one]) (H1.SectionArithmetic.pullSec th (translT P.A x).left)
    exact ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
  obtain ⟨s, hs⟩ := tr θ.pt
  obtain ⟨s', hs'⟩ := tr θ'.pt
  obtain ⟨t, ht⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T P.A).left) (ε' := fun _ => (n : ℤ))
    (fun U _ h => by simp) (H1.SectionArithmetic.powSec fun _ : Fin n => th)
  have ht' : ∀ (r : (T ⊗ P.A).left ⟶ (T ⊗ P.A).left) y J, Good P.L y J → sval t r y J = sval th r y J ^ n :=
    fun r y J hJ => by
      rw [ht _ r y J hJ, H1.SectionArithmetic.sval_powSec _ r y hJ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨u, hu⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ t u := VVRank.exists_isTwistPull P.A hL θ.isGen t
  obtain ⟨u', hu'⟩ : ∃ u, IsActOf P.A P.L (n : ℤ) θ' t u := VVRank.exists_isTwistPull P.A hL θ'.isGen t
  have hc : (constGen P.A P.L c).IsGen := isGen_of_gm _ fun y j j' _ _ => by
    obtain rfl : j = j' := Subsingleton.elim _ _
    rw [trF, Fintype.prod_empty, _root_.one_mul]
  obtain ⟨v, hv, hv'⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(translPt P.A θ'.pt).left, (translPt P.A θ.pt).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (LB.mulGen P.L _ _ _ _ (LB.invGen P.L ![(snd T P.A).left, (translPt P.A θ'.pt).left] ![(n : ℤ), -(n : ℤ)] θ'.φ)
      (LB.mulGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n : ℤ), -(n : ℤ)] _ _ θ.φ
        (constGen P.A P.L c)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ θ'.isGen)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen hc))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN P.L hL _ _ n hn s' s v hv (by
    by_contra h0
    have h0' : ∀ j, s.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    refine hne (Subtype.ext (funext fun j => sec_ext_val (s := th) (s' := H1.SectionArithmetic.secZero _) hL
      (fun y J hJ => ?_) j))
    have e := hs _ (translT P.A θ.pt⁻¹).left y J hJ
    rw [← Over.comp_left, translT_inv, Over.id_left] at e
    refine e.symm.trans (Eq.trans ?_ (gs_zero' _ y _ (hJ.mem _ _)).symm)
    exact (congrArg (gs _ y _) (h0' _)).trans (gs_zero' _ y _ (hJ.mem _ _))) (fun y J hJ => by
    have e := H t u u' hu hu' y J hJ
    rw [VVRank.sv_of_isTwistPull P.A hu _ y hJ, VVRank.sv_of_isTwistPull P.A hu' _ y hJ] at e
    have e₁ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs _ (𝟙 _) y J hJ).symm)
    have e₂ := (ht' _ y J hJ).trans (congrArg (· ^ n) (hs' _ (𝟙 _) y J hJ).symm)
    have e₃ := (congrArg _ e₂).symm.trans (e.trans (congrArg _ (congrArg _ e₁)))
    have e₄ := (hv' _ (𝟙 _) y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_inv _ _)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (H1.val_constGen _ c _ y J)))))
    rw [e₄, Units.val_mul, _root_.mul_assoc, Units.eq_inv_mul_iff_mul_eq, Units.val_mul, _root_.mul_assoc]
    exact e₃.trans (mul_left_comm _ _ _))
  exact (eq_of_gen P q _ _ r hr).symm

theorem qkToAkU_unique : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F n p x → QkToAkU U.toUnifPre F n p x' → x = x' := by
  intro hL _ R _ _ I _ D A G _ _ _ U F _ _ n hn p x x' hx hx'
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.globalFns U F hn w₀ hw₀
  obtain ⟨c, hc, hcs⟩ := exists_smul_of_phiVal p w w' hw hw'
  refine pt_eq_of_proportional hL.secBaseChange A _ hn θ θ'
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))
    fun t u u' hu hu' y J hJ => ?_
  have a := hcs _ _ _
    ((DVR.phiRel_iff hL.globalFns p w hw _ _).1 (h t u _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu))
    ((DVR.phiRel_iff hL.globalFns p w' hw' _ _).1 (h' t u' _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu'))
  obtain rfl := e.injective (a.trans (e.map_smul c u).symm)
  exact (sval_smul' hJ _ c _).trans (congrArg (· * _) (gs_unit _ y ⊤ trivial
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))))

end GlobalTheory.TorsionImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionFieldStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  first | exact @GlobalTheory.psiRel_of_pullB | exact GlobalTheory.psiRel_of_pullB | (intros; apply GlobalTheory.psiRel_of_pullB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.valueExpansion_of_chartExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  first | exact @GlobalTheory.UU.expF_of_expands | exact GlobalTheory.UU.expF_of_expands | (intros; apply GlobalTheory.UU.expF_of_expands <;> assumption)
end

