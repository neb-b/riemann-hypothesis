module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaFamilyOverOpenClosure
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfFlatDedekindTangentLe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatrices
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientOfOpenCoverReducedBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisationPrimePowerLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelFromSharp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

def restrictBase {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} (j : B →+* B') (hj : j ζ = ζ')
    {S : Scheme.{0}} {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) where
  A := c.A
  ab := c.ab
  P := c.P
  isLB := c.isLB
  rig₁ := c.rig₁
  rig₂ := c.rig₂
  symm := c.symm
  lev := c.lev
  lev_add := c.lev_add
  lev_tors := c.lev_tors
  geom := by
    intro K _ _ x β z hx hz
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s')
    refine c.geom K x φ.hom z hφ.symm ?_
    have : spMap (φ.hom.comp j) = spMap β := by
      rw [← spMap_comp, ← hx, ← Category.assoc, ← hφ]; rfl
    have e : φ.hom.comp j = β := congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    rw [hz, ← e, ← hj]; rfl

theorem finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem dirMap_base {o K : Type} [CommRing o] [Field K] {r : ℕ} (β : o →+* K) (lam : (Fin r → K) →ₗ[K] K) :
    spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      constPt (spMap (dirMap lam)) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) := by
  simp only [constPt, Category.assoc, spMap_comp]
  congr 1
  ext x <;> simp [dirMap]

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (f : X ⟶ Y) :
    constPt x ≫ f = constPt (x ≫ f) := by
  simp only [constPt, Category.assoc]

theorem nonempty_siegelFamily (L1 : Out.Laws) (L2 : Out.Laws2)
    (L3 : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    {h g p n N' : ℕ} (hh : 1 ≤ h) (hp : p.Prime) {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type} [Finite J]
    {a : J → Matrix (Fin 8) (Fin 8) ℤ} {w w' : J}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hW : IsE8 W) (hbas : IsSharpBasis W bas)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    (hu : ∀ u v, ∃ j, a j = Matrix.single u v 1) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (h3 : 3 ≤ N') (hodd : Odd N') {o : Type} [CommRing o] {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    (j : o →+* ZP p (N' ^ 2)) (har : ArBase em) (hj : j (b.ζ : o) = zetaZP p (N' ^ 2))
    (hconst : ∀ (K : Type) [Field K] (y : Sp (DualNumber K) ⟶ Sp (ZP p (N' ^ 2))), y = constPt y)
    (good : GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2))
    (F : WFam n em (SharpClass (b := b) W a bas em) Mat κ)
    (rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), IsReduced S →
      Dense (fromSet em (SharpClass (b := b) W a bas em) t) → t.FibShape Mat κ →
      ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f) :
    Nonempty (SiegelFamily h p (N' ^ 2)) := by
  have hk : Odd (N' ^ 2) := hodd.pow
  have hk3 : 3 ≤ N' ^ 2 := by nlinarith
  have hζ : b.ζ ^ N' ^ 2 = 1 := by
    refine Units.ext (har.2.2 ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, (b.prim ℂ em).pow_eq_one, Units.val_one, map_one]
  haveI : IsDedekindDomain o := har.1
  haveI : CharZero o := RingHom.charZero em
  obtain ⟨hq, hflat, hred, htan⟩ := _root_.GlobalTheory.ZM.WFam.qproj_flat_reduced_ext L1 L2 o g n N' J b em _ Mat κ F hodd
  obtain ⟨hqc, hft⟩ := finiteType_of_isQProjOver (hq.resolve_right (not_not.2 inferInstance))
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨c, hc, hsharp⟩ := GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense L1 L2 L3 h g W J a bas hW hbas hu _ o b em _ _ F.univ hk F.dense

  have pull : ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (c' : SiegPre h (N' ^ 2) (b.ζ : o) s) (t : TObj g (N' ^ 2) J b s)
      (f : S ⟶ F.U.toScheme), c'.Principal → IsSharp W a bas t c' → (SiegPB c' c f ↔ TMap t F.univ f) := by
    intro S s c' t f h1 h2
    have := _root_.GlobalTheory.PowerPullback.main L1 L2 h g W J a bas hW hbas _ o b _ _ _ _ c c' F.univ t f hc h1 hsharp h2
    exact ⟨this.1, this.2 hu⟩
  have hsm : SmoothOfRelativeDimension (h * (h + 1) / 2) (F.U.ι ≫ F.Y.s) := by
    refine _root_.GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le o _ _ _ har.2.1 hflat hft
      (_root_.GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre L1 L2 g n N' J Mat κ w w' o b em _ _ F h3 hodd har good) ?_
    intro K _ _ r β x hx hlam
    obtain ⟨p1, p2, -⟩ := _root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h (N' ^ 2) o o (b.ζ : o) (b.ζ : o) (RingHom.id o) _ _ _
      (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β)) x rfl (by rw [spMap_id, Category.comp_id, hx])
    obtain ⟨c', hc'⟩ := p1 c
    have hp' := p2 c c' hc' hc
    obtain ⟨t', ht'⟩ := _root_.GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h g W J a bas hW hbas _ o b _ _ c' hk hk3 hζ hp'
    have hm : TMap t' F.univ x := (pull _ _ c' t' x hp' ht').1 hc'
    refine _root_.GlobalTheory.PowerTangent.main L1 L2 L3 h g W J a bas hW hbas w w' hw hw' _ o b K r β t' c' hp' ht' ?_
    intro lam t'' m1 m2
    refine hlam lam ?_
    rw [← constPt_comp]
    refine htan (DualNumber K) _ _ _ t'' ?_ (((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m1)
      (((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t' t'').2 x _ hm).1 m2)
    rw [Category.assoc, Category.assoc, hx]
    exact dirMap_base β lam
  obtain ⟨q1, q2, -⟩ := _root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h (N' ^ 2) o _ (b.ζ : o) _ j _ _ (F.U.ι ≫ F.Y.s)
    (pullback.snd (F.U.ι ≫ F.Y.s) (spMap j)) (pullback.fst _ _) hj pullback.condition
  obtain ⟨u, hupb⟩ := q1 c
  have hup := q2 c u hupb hc
  refine ⟨⟨pullback (F.U.ι ≫ F.Y.s) (spMap j), pullback.snd _ _,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm, inferInstance, u, hup, ?_, ?_⟩⟩
  · intro C O _ _ _ _ _ _ _ _ hO hpC β c₁ hgen hamp
    have hp₁ : c₁.Principal := _root_.GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special L1 L2 h _ hk hk3 _ _ C O hO p hp hpC β c₁ hgen hamp
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := _root_.GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have hfrom := GlobalTheory.T.fromC_sharpClass_fibre_of_charZero L1 L2 h g W J a w w' bas hW hbas hw hw' hu N' o b em har _ _ t _ hp₀ ht C
      (spMap (algebraMap O C))
    haveI : IsDomain O := hO.1.isDomain _
    have hdense : Dense (fromSet em (SharpClass (b := b) W a bas em) t) := by
      have hd : DenseRange (PrimeSpectrum.comap (algebraMap O C)) := by
        rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).1 hO.1]
        exact bot_le
      exact Dense.mono (fun z hz => ⟨C, inferInstance, _, hz, hfrom⟩) hd
    have hshape : t.Shape Mat κ := by
      obtain ⟨_, _, _, _, _, _, _, tc, -, -, -, -, -, htc⟩ := hfrom
      have hs := (good.shape tc htc).1
      obtain ⟨cc, hcc, hcs⟩ := htc
      exact _root_.GlobalTheory.SharpShape.shape_of_isSharp L1 L2 h g W J a bas hW hbas _ o b Mat κ _ _ _ _ cc _ tc t hh inferInstance hcc hp₀ hcs ht hs
    obtain ⟨f, ⟨hf, hm⟩, -⟩ := rep _ _ t inferInstance hdense fun K _ _ x t' hx =>
      (_root_.GlobalTheory.shape_prim_pull_and_descend o g _ J b Mat κ w w' _ _ _ _ x t t' hx).1 hshape
    have hpb : SiegPB c₁ c f := (pull _ _ (restrictBase j hj c₁) t f hp₀ ht).2 hm
    refine ⟨pullback.lift f (spMap β) hf, pullback.lift_snd _ _ _, ?_⟩
    refine ((_root_.GlobalTheory.SiegelPullComp.id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).2 ?_
    rwa [pullback.lift_fst]
  · intro K _ x c₁ m1 m2
    have hp₁ : c₁.Principal := (_root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h (N' ^ 2) _ _ _ _ (RingHom.id _) _ _ _ _ x rfl
      (by rw [spMap_id, Category.comp_id])).2.1 u c₁ m1 hup
    have hp₀ : (restrictBase j hj c₁).Principal := hp₁
    obtain ⟨t, ht⟩ := _root_.GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h g W J a bas hW hbas _ o b _ _ (restrictBase j hj c₁) hk hk3 hζ hp₀
    have n1 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((_root_.GlobalTheory.SiegelPullComp.id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m1)
    have n2 := (pull _ _ (restrictBase j hj c₁) t _ hp₀ ht).1
      (((_root_.GlobalTheory.SiegelPullComp.id_comp_cancel h _ _ _ _ _ _ _ _ _ _ _ _ _ c u c₁ _ _).2 hupb).1 m2)
    have e : x ≫ pullback.snd _ _ = constPt x ≫ pullback.snd _ _ := by
      rw [constPt_comp]; exact hconst K _
    refine pullback.hom_ext (htan (DualNumber K) _ _ _ t ?_ n1 n2) e
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, e, Category.assoc]

theorem exists_siegelFamily : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N0 := by
  intro L1 L2 L3 L4 h p n hh hp hn hodd hnp
  obtain ⟨W, hW, hb⟩ := exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hb h
  have hinv : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [hW.2]; exact isUnit_one)
  let a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ :=
    Sum.elim (fun uv => Matrix.single uv.1 uv.2 1)
      (fun e => (W + W.transpose)⁻¹ * (if e then W else W.transpose))
  have hw : (W + W.transpose) * a (.inr true) = W := by
    change _ * (_ * W) = W
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hw' : (W + W.transpose) * a (.inr false) = W.transpose := by
    change _ * (_ * W.transpose) = W.transpose
    rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hu : ∀ u v, ∃ j, a j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_E8Sharp L1 L2 L3 L4 h _ W _ a _ _ bas hW hbas hw hw' hu
  obtain ⟨j₁, h₁⟩ := hcl n hn hodd
  obtain ⟨j₂, h₂⟩ := _root_.GlobalTheory.ZM.OpenFamily.nonempty_wFam L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨j₃, h₃⟩ := _root_.GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam L1 L2 _ _ Mat κ n (.inr true) (.inr false) hn hodd
  obtain ⟨m, hm⟩ : ∃ m, m = j₁ + j₂ + j₃ + 1 := ⟨_, rfl⟩
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨e, he⟩ := hodd
    omega
  have h3 : 3 ≤ n ^ m := hn3.trans (Nat.le_self_pow (by omega) n)
  obtain ⟨o, _, b, em, j, har, hj, -, hconst⟩ :=
    _root_.GlobalTheory.ZM.CycBase.exists_base n (m * 2) p ((n ^ m) ^ 2) hn hp hnp (by omega) (pow_mul n m 2).symm
  have good := h₁ m (by omega) _ rfl o b em
  obtain ⟨F⟩ := h₂ m (by omega) o b em _ _ har good
  refine ⟨m * 2, hn3.trans (Nat.le_self_pow (by omega) n), ?_⟩
  rw [pow_mul]
  exact nonempty_siegelFamily L1 L2 L3 hh hp hW hbas hw hw' hu h3 hodd.pow j har hj hconst good F
    (h₃ m (by omega) o b em _ _ har good F)

end GlobalTheory.SiegelFromSharp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientExistsListedKernelsSmoothBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSplit

theorem exists_affine_isDomain {Z : Scheme.{0}} [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (p : Z) :
    ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ IsDomain Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hC⟩) (x := p) mem_irreducibleComponent
  exact ⟨W, hW, hpW, (GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => hle hq⟩).1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (f : S' ⟶ S) (o : Ob D l s) :
    ∃ o' : Ob D l (f ≫ s), Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (f ≫ s) f rfl rfl
    (by rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id]) o

theorem hasQuot_image (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S] [IsNoetherian S']
    (s : S ⟶ Sp (KA l)) (g : S' ⟶ S) [Etale g] (o : Ob D l s) (s' : S' ⟶ Sp (KA l)) (hs : s' = g ≫ s)
    (o' : Ob D l s') (m : ObjMap o' o g) (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K)
    (hQ : HasQuot o' p (m.toSABMap.φ ⁻¹' K)) (q : S) (hq : q ∈ Set.range g) :
    ∃ (U : S.Opens) (o₁ : Ob D l (U.ι ≫ s)) (m₁ : ObjMap o₁ o U.ι), q ∈ U ∧ HasQuot o₁ p (m₁.toSABMap.φ ⁻¹' K) := by
  let U : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  obtain ⟨g', hg'⟩ : ∃ g' : S' ⟶ U.toScheme, g' ≫ U.ι = g :=
    ⟨IsOpenImmersion.lift U.ι g (by simp [U]), IsOpenImmersion.lift_fac _ _ _⟩
  have hU : ∀ x : S, x ∈ U → x ∈ Set.range g := fun _ h => h
  have hqU : q ∈ U := hq
  clear_value U
  subst hg'
  rw [Category.assoc] at hs
  subst hs
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull s U.ι o
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 U.ι g' m₁).2 m
  have he : Etale g' := Etale.of_comp g' U.ι
  have hsur : Surjective g' := ⟨fun y => by
    obtain ⟨x, hx⟩ := hU (U.ι y) y.2
    exact ⟨x, U.ι.isOpenEmbedding.injective (by simpa using hx)⟩⟩
  refine ⟨U, o₁, m₁, hqU, _root_.GlobalTheory.HkFam.hasQuot_descend E H D l Xo 𝔓 p i _ _ _ g' o₁ o' m' _ hA
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK) he hsur inferInstance ?_⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hQ
  exact hQ

end GlobalTheory.HkSplit

theorem GlobalTheory.hasQuot_of_lists_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i n S s o σ K hD hA hs hL hK
  obtain ⟨hr, hN, hn⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ S s hs
  refine _root_.GlobalTheory.hasQuot_of_openCover E H D l Xo 𝔓 p i S s o K hA hK fun q => ?_
  obtain ⟨W, hW, hq, hd⟩ := GlobalTheory.HkSplit.exists_affine_isDomain hN q
  have hR : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hj : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨x, hx⟩ : q ∈ Set.range j := by
    rw [show Set.range j = W from hW.range_fromSpec]; exact hq
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.HkSplit.exists_pull s j o
  obtain ⟨σ', -, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m₁.toSABMap.cart K _ n σ hL
  obtain ⟨R', _, π, o', m, he, ⟨y, hy⟩, hQ⟩ := _root_.GlobalTheory.exists_etale_hasQuot_of_lists E H D l 𝔓 p i n Γ(S, W) (j ≫ s) o₁ σ' _ x hD hA hL'
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK)
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 j π m₁).1 m
  have : IsLocallyNoetherian (Sp R') := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian (Sp R') := {}
  refine GlobalTheory.HkSplit.hasQuot_image Xo 𝔓 p i s (π ≫ j) o _ (Category.assoc _ _ _).symm o' m' K hA hK ?_ q
    ⟨y, by rw [Scheme.Hom.comp_apply, hy, hx]⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exact hQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelArithFamily

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [spMap, spMap, ← Spec.map_comp]; rfl

theorem comp_spMap_id {A : Type} [CommRing A] {S : Scheme.{0}} (s : S ⟶ Sp A) : s ≫ spMap (RingHom.id A) = s := by
  have : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _
  rw [this, Category.comp_id]

theorem locallyOfFiniteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  infer_instance

theorem charZero_residueField {o : Type} [CommRing o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) (p : S)
    (hp : (s p).asIdeal = ⊥) : CharZero (S.residueField p) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S.fromSpecResidueField p ≫ s)
  have h1 : (Spec.map φ) (⊥ : PrimeSpectrum (S.residueField p)) = s p := by
    rw [hφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg s (Scheme.fromSpecResidueField_apply p _))
  have h2 : Ideal.comap φ.hom ⊥ = ⊥ := by
    rw [← hp, ← h1]; rfl
  have h3 : Function.Injective φ.hom := (RingHom.injective_iff_ker_eq_bot _).2 h2
  exact charZero_of_injective_ringHom (R := o) h3

theorem dir_over {o K : Type} [CommRing o] [Field K] {r : ℕ} (β : o →+* K) (lam : (Fin r → K) →ₗ[K] K) :
    spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      constPt (spMap (dirMap lam)) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) := by
  rw [constPt, spMap_comp_spMap, spMap_comp_spMap, spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_matrices {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) :
    ∃ (a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ) (w w' : (Fin 8 × Fin 8) ⊕ Bool),
      (W + W.transpose) * a w = W ∧ (W + W.transpose) * a w' = W.transpose ∧
        ∀ u v, ∃ j, a j = Matrix.single u v 1 := by
  refine ⟨Sum.elim (fun uv => Matrix.single uv.1 uv.2 1)
    (fun c => (W + W.transpose).adjugate * (if c then W else W.transpose)), .inr true, .inr false, ?_, ?_,
    fun u v => ⟨.inl (u, v), rfl⟩⟩
  · simp only [Sum.elim_inr, if_true]
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hW.2, one_smul, Matrix.one_mul]
  · simp only [Sum.elim_inr, Bool.false_eq_true, if_false]
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hW.2, one_smul, Matrix.one_mul]

theorem nonempty_sFam : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ), ArBase em → Nonempty (SFam h ((n ^ j) ^ 2) (b.ζ : o)) := by
  intro L1 L2 hT hU h n hh hn hodd
  obtain ⟨W, hW, hbas⟩ := exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas h
  obtain ⟨a, w, w', hw, hw', hu⟩ := exists_matrices hW
  obtain ⟨Mat, κ, hgood⟩ := GlobalTheory.T.isGoodThetaComplexClass_E8Sharp L1 L2 hT hU h _ W _ a w w' bas hW hb hw hw' hu
  obtain ⟨j₁, hj₁⟩ := hgood n hn hodd
  obtain ⟨j₂, hj₂⟩ := _root_.GlobalTheory.ZM.OpenFamily.nonempty_wFam L1 L2 _ _ Mat κ n w w' hn hodd
  obtain ⟨j₃, hj₃⟩ := _root_.GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam L1 L2 _ _ Mat κ n w w' hn hodd
  refine ⟨max (max j₁ 1) (max j₂ j₃), fun j hj o _ b em hem => ?_⟩
  have hj1 : j ≥ j₁ := by omega
  have hj0 : j ≠ 0 := by omega
  have hj2 : j ≥ j₂ := by omega
  have hj3 : j ≥ j₃ := by omega
  have h3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have : n ≠ 2 := fun e => by rw [e] at hodd; exact absurd hodd (by decide)
    exact le_trans (by omega) (Nat.le_self_pow hj0 n)
  have hoN : Odd (n ^ j) := hodd.pow
  have hok : Odd ((n ^ j) ^ 2) := hoN.pow
  have h3k : 3 ≤ (n ^ j) ^ 2 := h3.trans (Nat.le_self_pow two_ne_zero _)
  have hζ : b.ζ ^ ((n ^ j) ^ 2) = 1 := by
    refine Units.ext (hem.2.2 ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, (b.prim ℂ em).pow_eq_one, Units.val_one, map_one]
  have hG := hj₁ j hj1 _ rfl o b em
  obtain ⟨F⟩ := hj₂ j hj2 o b em _ _ hem hG
  obtain ⟨hq, hflat, hred, hinj⟩ := _root_.GlobalTheory.ZM.WFam.qproj_flat_reduced_ext L1 L2 o _ n _ _ b em _ Mat κ F hoN
  haveI := hem.1
  haveI : CharZero o := em.charZero
  have hq : IsQProjOver (F.U.ι ≫ F.Y.s) := hq.resolve_right (not_not.2 inferInstance)
  have hft := locallyOfFiniteType_of_qproj hq
  haveI : IsLocallyNoetherian F.U.toScheme := LocallyOfFiniteType.isLocallyNoetherian (F.U.ι ≫ F.Y.s)
  obtain ⟨c, hc, hsc⟩ := GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense L1 L2 hT h _ W _ a bas hW hb hu _ o b em _ _ F.univ hok F.dense

  have pull : ∀ (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (f : S' ⟶ F.U.toScheme), f ≫ F.U.ι ≫ F.Y.s = s' →
      ∃ (c' : SiegPre h ((n ^ j) ^ 2) (b.ζ : o) s') (t : TObj (8 * h) ((n ^ j) ^ 2) _ b s'),
        SiegPB c' c f ∧ c'.Principal ∧ IsSharp W a bas t c' := by
    intro S' s' f hf
    obtain ⟨p1, p2, -⟩ := _root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h ((n ^ j) ^ 2) o o (b.ζ : o) (b.ζ : o) (RingHom.id o) _ S' _ s' f rfl
      (hf.trans (comp_spMap_id s').symm)
    obtain ⟨c', hc'⟩ := p1 c
    obtain ⟨t, ht⟩ := _root_.GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h _ W _ a bas hW hb _ o b S' s' c' hok h3k hζ (p2 c c' hc' hc)
    exact ⟨c', t, hc', p2 c c' hc' hc, ht⟩
  refine ⟨⟨F.U.toScheme, F.U.ι ≫ F.Y.s, ?_, hq, c, hc, ?_, ?_⟩⟩
  · refine _root_.GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le o _ _ _ hem.2.1 hflat hft
      (fun R _ _ x hx hs => _root_.GlobalTheory.ZM.GenericDim.le_ringKrullDim_genericFibre L1 L2 _ n _ _ Mat κ w w' o b em _ _ F h3 hoN hem hG R x hx hs) ?_
    intro K _ _ r β x hx hlam
    obtain ⟨c', t, hp, hc', ht⟩ := pull _ _ x hx
    have htx : TMap t F.univ x :=
      (_root_.GlobalTheory.PowerPullback.main L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t x hc hc' hsc ht).1 hp
    refine _root_.GlobalTheory.PowerTangent.main L1 L2 hT h _ W _ a bas hW hb w w' hw hw' _ o b K r β t c' hc' ht fun lam t' h1 h2 => hlam lam ?_
    have e : constPt (spMap (dirMap lam) ≫ x) = constPt (spMap (dirMap lam)) ≫ x := by
      simp only [constPt, Category.assoc]
    rw [e]
    refine hinj _ _ _ _ t' ?_ (((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o _ _ _ b _ _ _ _ _ _ F.univ t t').2 x _ htx).1 h1)
      (((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o _ _ _ b _ _ _ _ _ _ F.univ t t').2 x _ htx).1 h2)
    rw [Category.assoc, Category.assoc, hx]
    exact dir_over β lam
  · intro S s' c' hS hd hc'
    obtain ⟨t, ht⟩ := _root_.GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h _ W _ a bas hW hb _ o b S s' c' hok h3k hζ hc'
    have hfrom : ∀ p : S, (s' p).asIdeal = ⊥ →
        FromC em (SharpClass (b := b) W a bas em) t (K := S.residueField p) (S.fromSpecResidueField p) := by
      intro p hp
      haveI := charZero_residueField s' p hp
      exact GlobalTheory.T.fromC_sharpClass_fibre_of_charZero L1 L2 h _ W _ a w w' bas hW hb hw hw' hu _ o b em hem S s' t c' hc' ht _ _
    have hdense : Dense (fromSet em (SharpClass (b := b) W a bas em) t) :=
      hd.mono fun p hp => ⟨S.residueField p, inferInstance, S.fromSpecResidueField p,
        ⟨default, Scheme.fromSpecResidueField_apply p _⟩, hfrom p hp⟩
    have hshape : t.FibShape Mat κ := by
      intro K _ _ x t' ht'
      have : Nonempty S := ⟨x (⊥ : PrimeSpectrum K)⟩
      obtain ⟨p, hp⟩ := hd.nonempty
      obtain ⟨_, _, _, _, _, _, _, tc, -, -, -, -, -, htc⟩ := hfrom p hp
      have hsh := (hG.shape tc htc).1
      obtain ⟨cc, hcc, hscc⟩ := htc
      exact (_root_.GlobalTheory.shape_prim_pull_and_descend o _ _ _ b Mat κ w w' _ _ _ _ x t t' ht').1
        (_root_.GlobalTheory.SharpShape.shape_of_isSharp L1 L2 h _ W _ a bas hW hb _ o b Mat κ _ _ _ _ cc c' tc t hh ⟨(⊥ : PrimeSpectrum ℂ)⟩ hcc hc' hscc ht hsh)
    obtain ⟨f, ⟨hf, htf⟩, -⟩ := hj₃ j hj3 o b em _ _ hem hG F S s' t hS hdense hshape
    exact ⟨f, hf, (_root_.GlobalTheory.PowerPullback.main L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t f hc hc' hsc ht).2 hu htf⟩
  · intro R _ _ x y s' c₀ hxy hx hy
    obtain ⟨c', t, hp, hc', ht⟩ := pull _ _ x rfl
    have h1 : SiegPB c' c₀ (𝟙 _) :=
      ((GlobalTheory.SiegelPullComp.id_comp_cancel h _ o o o _ _ _ _ _ _ _ _ _ c c₀ c' x (𝟙 _)).2 hx).2
        (by rwa [Category.id_comp])
    have h2 : SiegPB c' c y := by
      have := ((GlobalTheory.SiegelPullComp.id_comp_cancel h _ o o o _ _ _ _ _ _ _ _ _ c c₀ c' y (𝟙 _)).2 hy).1 h1
      rwa [Category.id_comp] at this
    exact hinj R x y _ t hxy
      ((_root_.GlobalTheory.PowerPullback.main L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t x hc hc' hsc ht).1 hp)
      ((_root_.GlobalTheory.PowerPullback.main L1 L2 h _ W _ a bas hW hb _ o b _ _ _ _ c c' F.univ t y hc hc' hsc ht).1 h2)

end GlobalTheory.ZM.SiegelArithFamily
end

