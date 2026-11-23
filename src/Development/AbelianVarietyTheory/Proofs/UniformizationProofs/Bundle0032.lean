module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

namespace EndTorus

theorem idempotent_trivial {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) [IsAdicComplete I R]
    (e : ℕ) (x : R ⧸ I ^ (e + 1)) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hle : I ^ (e + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero e)
  have h0 : a₀ * a₀ - a₀ ∈ I := hle (Ideal.Quotient.eq.1 hx)
  have hm : (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by monicity!
  obtain ⟨a, ha, hI⟩ := HenselianRing.is_henselian (I := I) _ hm a₀ (by simpa [sq] using h0) (by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * a₀ - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    convert I.mul_mem_left 4 h0 using 1
    simp
    ring)
  have hnil : ∀ y ∈ I, IsNilpotent (Ideal.Quotient.mk (I ^ (e + 1)) y) := fun y hy =>
    ⟨e + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hy _)⟩
  have ha' : a * (a - 1) = 0 := by
    have := ha.eq_zero
    simp at this
    linear_combination this
  rcases mul_eq_zero.1 ha' with h | h
  · left
    refine hx.eq_zero_of_isNilpotent (hnil _ ?_)
    simpa [h] using hI
  · right
    have h1 : a = 1 := sub_eq_zero.1 h
    have := hx.one_sub.eq_zero_of_isNilpotent (by simpa [h1] using hnil _ hI)
    exact (sub_eq_zero.1 this).symm

theorem connectedSpace_thickening {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)
    [hC : IsAdicComplete I R] (e : ℕ) : ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨x, hx, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hU
    rcases idempotent_trivial I e x hx with rfl | rfl <;> simp
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

theorem torusEndOf_iff_appTop {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem isMonHom_of_mono {S : Scheme.{0}} {A B C : Over S} [MonObj A] [MonObj B] [MonObj C]
    (t : A ⟶ B) (i : B ⟶ C) [Mono i] [IsMonHom i] [IsMonHom (t ≫ i)] : IsMonHom t := by
  constructor
  · rw [← cancel_mono i, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end EndTorus


open EndTorus in
theorem gtCoord_end_torus_abelian : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G), IsMonHom a → (∃! h : D.X →+ D.X, ∃ t, TorusEndOf D.X h t ∧ g.i ≫ a = t ≫ g.i) ∧ ∃! b : thickObj R I e D.P.A ⟶ thickObj R I e D.P.A, IsMonHom b ∧ a ≫ g.q = g.q ≫ b := by
  intro _ R _ _ I hR D e G _ _ g a ha
  obtain ⟨hN, -, -, hC⟩ := hR
  have := connectedSpace_thickening I e
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hk := g.isKernel
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D.P.A) :=
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g.i ≫ a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D.X _ hB (g.i ≫ a ≫ g.q) inferInstance).trans (Hom.one_def)
  have : Mono g.i := by
    have : Mono (η[thickObj R I e D.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  constructor
  · let t := hk.lift (g.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
    have ht : t ≫ g.i = g.i ≫ a := hk.lift_fst _ _ _
    have : IsMonHom (t ≫ g.i) := ht ▸ inferInstance
    have : IsMonHom t := isMonHom_of_mono t g.i
    obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
    refine ⟨h, ⟨t, (torusEndOf_iff_appTop _ _).2 hh, ht.symm⟩, ?_⟩
    rintro h' ⟨t', h₁, h₂⟩
    obtain rfl : t' = t := by rw [← cancel_mono g.i, ht, h₂]
    ext χ
    exact SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (((torusEndOf_iff_appTop _ _).1 h₁ χ).symm.trans (hh χ))
  · obtain ⟨b, hb, hq⟩ := FlatQuotient.exists_desc g.q g.i (a ≫ g.q) hk h1
    have := FlatQuotient.epi_of_flat_surjective g.q
    refine ⟨b, ⟨hb, hq.symm⟩, ?_⟩
    rintro b' ⟨-, h⟩
    rw [← cancel_epi g.q, ← h, hq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefPhi
open GlobalTheory.UT.CoefBasic

theorem cubN_mul {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k n : ℕ) (a m x : A) :
    cubN θ (k * n) a m x = cubN θ n a (m ^ k) x * cubN θ k 1 m x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ (k * (n + 1)) a m x = cubN θ (k * n) a m x * cubN θ k (a * (m ^ k) ^ n) m x := by
      rw [Nat.mul_succ, cubN, Finset.prod_range_add, cubN, cubN]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, _root_.mul_assoc]
    have e' : cubN θ (n + 1) a (m ^ k) x = cubN θ n a (m ^ k) x * θ (a * (m ^ k) ^ n) (m ^ k) x :=
      Finset.prod_range_succ _ _
    rw [e, e', ih, h.N_split k (a * (m ^ k) ^ n), pow_succ (cubN θ k 1 m x)]
    ac_rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frame {k : ℕ} (p : QkPt D F k) (w : Frm D F k p.g.b) (hw : w.IsGen) (g₀ : GtPtF D F)
    (ω₀ : Frm D F k g₀.b) (h₀ : ω₀.IsGen) (b : TF (R := R) F ⟶ D.P.A) (hb : b = g₀.b * p.g.b) :
    ∃ ω₁ : Frm D F k b, ω₁.IsGen ∧ ∀ z J, Good D.P.L z J → val ω₁ (𝟙 _) z J =
      val ω₀ (𝟙 _) z J * val w (𝟙 _) z J * val (g₀.s p.y) (𝟙 _) z J * cubN (th D z J) k 1 p.g.b g₀.b := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p.g.b g₀.b k
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      refine Eq.trans (prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 4) (K' := Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 4) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_line k g₀.b h) (prod_line k p.g.b h))
          (prod_gt g₀.b p.y h)) rfl) ?_
      rw [prod_line, cPoint_y, hb, mul_comm g₀.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ ω₀ w) (g₀.s p.y)) N)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ hw) (g₀.isGen _)) hN)
  refine ⟨u, hu, fun z J hJ => ?_⟩
  have e := vN _ (𝟙 _) z J hJ
  simp only [Category.id_comp, Over.id_left] at e
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) e))

theorem coef_phi : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (g₀ g₁ : GtPtF D.toPre F), g₀.IsAdd p.g g₁ → ∀ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen → ∃ ω₁ : Frm D.toPre F k g₁.b, ω₁.IsGen ∧ (g₀.IsZero → FrmOne ω₀ → ∀ z J, Good D.toPre.P.L z J → val ω₁ (𝟙 _) z J = val w (𝟙 _) z J) ∧ ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → ∀ (wN : Frm D.toPre F N q.g.b) (w₀ : Frm D.toPre F N g₀.b) (w₁ : Frm D.toPre F N g₁.b), (wN.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val wN (𝟙 _) z J = val w (𝟙 _) z J ^ n) → (w₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₀ (𝟙 _) z J = val ω₀ (𝟙 _) z J ^ n) → (w₁.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J = val ω₁ (𝟙 _) z J ^ n) → ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N q wN s s' → ∀ α, coef s' g₀ w₀ (α + q.y) = coef s g₁ w₁ α := by
  intro hL R _ _ _ I _ D F _ _ _ k _ p w hw g₀ g₁ hadd ω₀ h₀
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ω₁, h₁, v₁⟩ := exists_frame p w hw g₀ ω₀ h₀ g₁.b hb
  refine ⟨ω₁, h₁, fun hz ho z J hJ => ?_, ?_⟩
  · have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 hz
    have c : cubN (th D.toPre z J) k 1 p.g.b g₀.b = 1 := by rw [z₁, C.N_one]
    rw [v₁ z J hJ, ho.2 z J hJ, z₂ _ z J hJ, c, _root_.one_mul, _root_.mul_one, _root_.mul_one]
  · rintro n _ _ rfl ⟨qy, qg, qe⟩ hy hg wN w₀ w₁ ⟨hN, vN⟩ ⟨-, v₀⟩ ⟨hw₁, vw₁⟩ s s' hΦ α
    dsimp only at hy hg
    subst hy hg
    have H := (phiRel_iff hL.1.globalFns _ wN hN s s').1 hΦ
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    have e₁ := H α _ rfl _ (lift (𝟙 (TF (R := R) F)) g₀.b) z J hJ
    have t : lift (𝟙 (TF (R := R) F)) g₀.b ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := R) F)) g₁.b := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
      · rw [lift_snd, hb, Category.assoc]
        refine (congrArg (_ ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_
        rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
    dsimp only at e₁ vN
    rw [t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, Over.id_left, val_mul hJ, vN z J hJ,
      cubN_mul C] at e₁
    have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g₀ α p.y n
    rw [Category.id_comp, Over.id_left, cPoint_y] at e₂
    have e₃ := hs α z J hJ
    rw [isCoef_coef g₁ hw₁ α s z J hJ]
    dsimp only
    rw [e₁, v₀ z J hJ, vw₁ z J hJ, v₁ z J hJ]
    simp only [_root_.mul_assoc, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂

end GlobalTheory.UT.CoefPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.exists_degData_isPullDeg : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R'), I.map φ ≤ I' → ∀ (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Out.PsiOn D.toPre W) → (_root_.ReciprocityTheory.ChartRestriction.G.Out.specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R' I') (hD : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPullDeg φ D.toPre D'.toPre), hD.W = W ∧ D'.toPre.P.g = D.toPre.P.g := by
  intro hP hG R R' _ _ _ _ I I' φ hle D W hψ hgen
  obtain ⟨D₀, hE, hT, hI, hF⟩ := D
  obtain ⟨D', hD, hW, hg⟩ :=
    _root_.GlobalTheory.DegPull.exists_isPullDeg hP R R' φ D₀ W hψ hgen
  refine ⟨⟨D', _root_.GlobalTheory.PsiEvenPull.psiEven_pull hG R R' φ D₀ D' hD hE,
    _root_.GlobalTheory.tauBimult_of_isPullDeg hG R R' φ D₀ D' hD hT, ?_, ?_⟩, hD, hW, hg⟩
  · intro χ hχ
    exact _root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ I I' hle
      (hI _ fun h => hχ (hD.xe.map_eq_zero_iff.mp h))
  · intro n
    refine ((hF n).preimage hD.xe.injective.injOn).subset ?_
    intro χ hχ h
    exact hχ (_root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ (I ^ n) (I' ^ n)
      (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hle n) h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiSpread

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_finite_cube_induction (X : Type) [AddCommGroup X] [Module.Finite ℤ X] :
    ∃ S : Set X, S.Finite ∧ ∀ E : X → Prop, (∀ x ∈ S, E x) →
      (∀ a a' b, E a → E a' → E b → E (a + a') → E (a + b) → E (a' + b) → E (a + a' + b)) → ∀ x, E x := by
  have h : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨G, hG, hGfin⟩ := AddMonoid.fg_iff.mp h
  refine ⟨insert 0 (G ∪ Set.image2 (· + ·) G G),
    (hGfin.union (hGfin.image2 _ hGfin)).insert _, fun E hS hE x => ?_⟩
  have h₁ : ∀ g ∈ G, E g := fun g hg => hS g (Or.inr (Or.inl hg))
  have key : E x ∧ ∀ g ∈ G, E (g + x) := by
    refine AddSubmonoid.induction_of_closure_eq_top_left (motive := fun x => E x ∧ ∀ g ∈ G, E (g + x))
      hG x ⟨hS 0 (Or.inl rfl), fun g hg => by rw [add_zero]; exact h₁ g hg⟩ fun g hg y hy => ⟨hy.2 g hg, fun g' hg' => ?_⟩
    rw [← add_assoc]
    exact hE g' g y (h₁ _ hg') (h₁ _ hg) hy.1 (hS _ (Or.inr (Or.inr ⟨g', hg', g, hg, rfl⟩))) (hy.2 _ hg') (hy.2 _ hg)
  exact key.1

theorem exists_gen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j : K → L.ι) (hj : ∀ y, y ∈ LB.wchart L φ j) (V : Y.Opens) (hV : ∀ y, y ∈ V) (u : Γ(Y, V)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u := by
  let t : LB.Gen (LB.LinComb L φ ε) := ⟨fun j' =>
    res (le_inf le_rfl (fun y _ => hj y) : LB.wchart L φ j' ≤ LB.wchart L φ j' ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j' j) * res (fun y _ => hV y : LB.wchart L φ j' ≤ V) u⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j' : K → L.ι),
      r z ∈ LB.wchart L φ j' → gm r z (LB.wchart L φ j') (t.s j') = trF φ ε r z j' j * gm r z V u :=
    fun Z r z j' h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ h _).trans (gm_linComb L φ ε r z j' j h (hj _))) (gm_res r z _ h _))
  refine ⟨t, fun (i i' : K → L.ι) => unit_ext fun y hy => ?_, key⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i hy.1)).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y i i' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i' hy.2))).trans ?_)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hj _), _root_.mul_assoc]
  rfl

theorem exists_unit_near {X Y : Scheme.{0}} (f : Y ⟶ X) [IsPreimmersion f] (y : Y) (a : (Y.presheaf.stalk y)ˣ) :
    ∃ (U : X.Opens) (u : Γ(X, U)ˣ), f y ∈ U ∧ gm f y U u = a := by
  obtain ⟨s, hs⟩ := f.stalkMap_surjective y a.val
  obtain ⟨U, hU, g, rfl⟩ := X.presheaf.exists_germ_eq s
  have hu : IsUnit ((X.presheaf.germ U (f y) hU).hom g) :=
    (isUnit_map_iff (f.stalkMap y).hom _).1 (hs ▸ a.isUnit)
  have hm : f y ∈ X.basicOpen g := (X.mem_basicOpen g (f y) hU).2 hu
  refine ⟨X.basicOpen g, (X.toRingedSpace.isUnit_res_basicOpen g).unit, hm, Units.ext ?_⟩
  refine (gs_unit f y _ hm _).symm.trans ((gs_res f y (X.basicOpen_le g) hm g).trans ((gs_eq f y U hU g).trans ?_))
  exact (Scheme.Hom.germ_stalkMap_apply f U y hU g).symm.trans hs

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def Extends {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (χ : D.X) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (cP D T χ).left) (fun _ => -1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → val t κ.left z J = val (D.psi χ) (𝟙 _) z J

theorem exists_extends (χ : D.X) (z : (TK R).left) : ∃ V : (Spec (CommRingCat.of R)).Opens, jK R z ∈ V ∧
    ∀ W : (Spec (CommRingCat.of R)).Opens, W ≤ V → ∀ κ : TK R ⟶ TW W, Extends D κ χ := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R) (S := FractionRing R)
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  obtain ⟨j, hj⟩ := exists_chart D.P.isLB (D.xK χ z)
  obtain ⟨U, u, hU, e⟩ := exists_unit_near (jK R) z
    (gm (𝟙 (TK R).left) z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)))
  refine ⟨U ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U j, ⟨hU, hj⟩, fun W hW κ => ?_⟩
  have hκ : κ.left ≫ W.ι = jK R := Over.w κ
  obtain ⟨t, ht, vt⟩ := exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (cP D (TW W) χ).left) (fun _ => -1)
    (fun _ => j) (fun y => Set.mem_iInter.2 fun _ => (hW y.2).2) (W.ι ⁻¹ᵁ U) (fun y => (hW y.2).1) (pullU W.ι U u)
  refine ⟨t, ht, fun z' J hJ => ?_⟩
  obtain rfl : z = z' := Subsingleton.elim _ _
  have q : κ.left ≫ (cP D (TW W) χ).left = 𝟙 _ ≫ D.xK χ :=
    (congrArg (fun q => q.left) (comp_cP D κ χ)).trans (Category.id_comp _).symm
  refine (vt _ κ.left z _ (hJ.mem _ _)).trans (Eq.trans ?_
    (gen_trans (D.psi_gen χ) (𝟙 _) z (j' := fun _ => j) (hJ.mem _ _) (Set.mem_iInter.2 fun _ => hj)).symm)
  refine congrArg₂ (· * ·) ?_ ((gm_pull κ.left W.ι z U (hW (κ.left z).2).1 u).trans (by rw [hκ]; exact e))
  exact congrArg (fun ψ => ∏ _k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U j) (D.P.L.g (J ψ) j) ^ (-1 : ℤ)) q

theorem prod_elim {A U K K' : Type} [CommGroup U] [Fintype K] [Fintype K'] (h : A → U) {φ : K → A} {ε : K → ℤ}
    {φ' : K' → A} {ε' : K' → ℤ} {c c' : U} (e : ∏ k, h (φ k) ^ ε k = c) (e' : ∏ k, h (φ' k) ^ ε' k = c') :
    ∏ k, h (Sum.elim φ φ' k) ^ Sum.elim ε ε' k = c * c' := by
  rw [Fintype.prod_sum_type, ← e, ← e']; rfl

theorem prod_punit {A U : Type} [CommGroup U] (h : A → U) (a : A) (n : ℤ) :
    ∏ k : PUnit.{1}, h ((fun _ => a) k) ^ (fun _ => n) k = h a ^ n := Fintype.prod_unique _

theorem Extends.cube (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (κ : TK R ⟶ T) (a a' b : D.X)
    (h₁ : Extends D κ a) (h₂ : Extends D κ a') (h₃ : Extends D κ b) (h₄ : Extends D κ (a + a'))
    (h₅ : Extends D κ (a + b)) (h₆ : Extends D κ (a' + b)) : Extends D κ (a + a' + b) := by
  obtain ⟨t₁, g₁, v₁⟩ := h₁
  obtain ⟨t₂, g₂, v₂⟩ := h₂
  obtain ⟨t₃, g₃, v₃⟩ := h₃
  obtain ⟨t₄, g₄, v₄⟩ := h₄
  obtain ⟨t₅, g₅, v₅⟩ := h₅
  obtain ⟨t₆, g₆, v₆⟩ := h₆
  obtain ⟨t, gt, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => (cP D T (a + a' + b)).left) (ε' := fun _ => -1)
    (fun U _ h => by
      have p := prod_cub (cP D T a) (cP D T a') (cP D T b) h
      have q : (toUnit T).left ≫ eSec D.P.A = (1 : T ⟶ D.P.A).left := rfl
      refine (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
        (prod_neg _ _ (prod_elim h (prod_elim h (prod_elim h (prod_punit h _ _) (prod_punit h _ _)) (prod_punit h _ _))
          (prod_elim h (prod_punit h _ _) p)))).trans (Eq.trans ?_ (prod_punit h _ _).symm)
      rw [q]
      simp only [cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₄ t₅) t₆)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁ t₂) t₃)
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit T).left)
          (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (cP D T a) (lift (cP D T a') (cP D T b))).left)))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₄ g₅) g₆)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) g₃)
        (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) (pullGen_isGen _ _ _ _ D.cub.isGen _)))))
  refine ⟨t, gt, fun z J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).trans (by simp only [comp_cP])
  have vρ : val (LB.pullGen D.P.L _ _ D.rig (toUnit T).left) κ.left z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact congrArg (fun q => val D.rig q z J) (Over.w κ)
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D T a) (lift (cP D T a') (cP D T b))).left) κ.left z J = th D z J (cP D _ a) (cP D _ a') (cP D _ b) :=
    (val_cub D.cub κ hJ _ _ _).trans (by simp only [comp_cP])
  rw [c, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ] at e
  refine (vt _ _ z J hJ).trans (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (v₄ z J hJ) (v₅ z J hJ))) (v₆ z J hJ)))
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (v₁ z J hJ) (v₂ z J hJ))) (v₃ z J hJ)))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) vρ vc)))))))).trans ?_)
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) -e'

theorem nonempty_psiOn {W : (Spec (CommRingCat.of R)).Opens} (κ : TK R ⟶ TW W) (h : ∀ χ, Extends D κ χ) :
    Nonempty (PsiOn D W) := by
  choose t gt vt using h
  refine ⟨⟨t, gt, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  have c : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (t χ) κ.left) (D.psi χ) :=
    corr_of_val D.P.isLB fun z J hJ => (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; exact vt χ z J hJ)
  have q : (jK R ⁻¹ᵁ W).ι ≫ κ.left = jK R ∣_ W := by
    have hκ : κ.left ≫ W.ι = jK R := Over.w κ
    rw [← cancel_mono W.ι, morphismRestrict_ι, Category.assoc, hκ]
  have e := (val_pull hJ _ _ _).symm.trans (val_corr hJ c (jK R ⁻¹ᵁ W).ι)
  rw [q] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [Category.id_comp, Category.id_comp]
  exact e

theorem exists_psiOn (hB : D.TauBimult) : ∃ W : (Spec (CommRingCat.of R)).Opens,
    genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W) := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨S, hS, ind⟩ := exists_finite_cube_induction D.X
  choose V hV ext using fun χ => exists_extends D χ z
  let W : (Spec (CommRingCat.of R)).Opens := ⟨⋂ χ ∈ S, V χ, hS.isOpen_biInter fun χ _ => (V χ).isOpen⟩
  have hz : jK R z ∈ W := Set.mem_iInter₂.2 fun χ _ => hV χ
  let κ : TK R ⟶ TW W := Over.homMk (IsOpenImmersion.lift W.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact TauPull.jK_mem y W ⟨_, hz⟩)) (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨W, ?_, nonempty_psiOn D κ (ind _ (fun χ hχ => ext χ W (fun x hx => Set.mem_iInter₂.1 hx χ hχ) κ)
    (Extends.cube D hB κ))⟩
  exact ((genericPoint_spec (Spec (CommRingCat.of R))).mem_open_set_iff W.isOpen).2 ⟨_, trivial, hz⟩

end PsiSpread

theorem psiOnExists : PsiOnExistsSt := fun _ _ _ _ _ D => PsiSpread.exists_psiOn D.toPre D.tau_bimult

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_section_endomorphism_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  first | exact @GlobalTheory.PullInt.main | exact GlobalTheory.PullInt.main | (intros; apply GlobalTheory.PullInt.main <;> assumption)
end

