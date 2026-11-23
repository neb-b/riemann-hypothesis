module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DerivationEqZeroOfKodairaSpencerZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.KerZero

def derPt {o R : Type} [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ]
    (D : Derivation o R ℂ) : R →+* DualNumber ℂ where
  toFun r := TrivSqZeroExt.inl (algebraMap R ℂ r) + TrivSqZeroExt.inr (D r)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem derivation_eq_zero_of_ks_zero : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))) (s₀ : Sp ℂ ⟶ Sp o) (t₀ : TObj g k J b s₀) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∀ (D : Derivation o R ℂ) s, KSRel u t.A.hom m (fun r => D r) 0 s → D = 0 := by
  intro h₁ h₂ h₃ o _ g k J b R _ _ _ _ _ t s₀ t₀ m u Hm χ hu hm hun D s hs
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := hm
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (derPt D) = spMap (algebraMap R ℂ) := by
    rw [spMap_comp]; congr 1; ext r; simp [derPt]
  obtain ⟨t', ht'⟩ := _root_.GlobalTheory.tObj_pull o g k J b _ _ _ _ (spMap (derPt D)) t rfl
  obtain ⟨φ, hφ₁, hφ₂, hφ₃, hφ₄⟩ := id ht'
  have hp := hφ₁.1
  let j : t₀.A.left ⟶ t'.A.left := hp.lift m (t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    (by rw [hm₁.1.w, Category.assoc, hfst])
  have hj : j ≫ φ = m := hp.lift_fst _ _ _
  have hw : j ≫ t'.A.hom = t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := hp.lift_snd _ _ _
  have hj₁ : IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j :=
    hφ₁.cancel (hm₁.congr hfst.symm hj.symm) hw
  have hj₂ : LBIso t₀.L (t'.L.pull j) :=
    LBIso.trans t₀.isLB (pull_isLB t.isLB m) (pull_isLB t'.isLB j) hm₂
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t'.L j j rfl) (chartPullSame t.L _ _ _ j fun _ => hj.symm) hφ₂).symm
  have hj₃ : ∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left := by
    intro i
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₃, Category.assoc, hφ₃, ← Category.assoc, hfst]
    · have a₁ : (t₀.pt i).left ≫ t₀.A.hom = 𝟙 _ := Over.w (t₀.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 _ := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hj₄ : ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left := by
    intro a
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₄, Category.assoc, hφ₄, ← Category.assoc, hj]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.KS.exists_isConst_of_ksRel_zero h₁ t₀.pol u Hm χ hu R (derPt D) t.A t'.A φ j s t.ab t'.ab hφ₁ hj₁ (by
    have e : (fun r => (derPt D r).snd) = fun r => D r := by funext r; simp [derPt]
    rw [e]
    exact hj ▸ hs)
  have hc := _root_.GlobalTheory.KS.tMap_of_isConst h₁ h₂ h₃ o g k J b s₀ _ t₀ t' ρ j hρ ⟨hj₁, hj₂, hj₃, hj₄⟩
  have hcp : constPt (spMap (derPt D)) = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (algebraMap R ℂ) := by
    rw [constPt, hfst]
  have hc' : TMap t' t (constPt (spMap (derPt D))) := by
    rw [hcp]
    exact ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ ⟨m, hm₁, hm₂, hm₃, hm₄⟩).1 hc
  have hx := hun (spMap (derPt D)) t' (by
    rw [hcp, spMap_comp, spMap_comp, spMap_comp]
    congr 1
    ext r <;> simp [derPt, TrivSqZeroExt.algebraMap_eq_inl]) ht' hc'
  rw [hcp, spMap_comp] at hx
  have hx' := spMap_inj hx
  ext r
  have := congrArg (fun f : R →+* DualNumber ℂ => (f r).snd) hx'
  simpa [derPt, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KS.KerZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.Direct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelDirect

open GlobalTheory.SiegelPullComp

private theorem tensor_left_hom_ext' {T : Scheme.{0}} {G : Over T} {X : Scheme.{0}} (a b : X ⟶ (G ⊗ G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key := CartesianMonoidalCategory.hom_ext
    (Over.homMk a rfl : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) (Over.homMk b hw)
    (by ext; simpa using h1) (by ext; simpa using h2)
  simpa using congrArg (fun k => k.left) key

theorem exists_inverse {T : Scheme.{0}} {A G : Over T} [GrpObj A] [GrpObj G] {φ : A.left ⟶ G.left}
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hφ : IsGrpPullback A G (𝟙 T) φ) (hs : Geo.Tor.IsSquare φ φ₂) :
    ∃ (F : G.left ⟶ A.left) (F₂ : (G2 G).left ⟶ (G2 A).left), IsGrpPullback G A (𝟙 T) F ∧ Geo.Tor.IsSquare F F₂ ∧
      φ ≫ F = 𝟙 _ ∧ F₂ ≫ φ₂ = 𝟙 _ := by
  have hw : φ ≫ G.hom = A.hom := by simpa using hφ.1.w
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  let e : A ≅ G := Over.isoMk (asIso φ) hw
  have heL : e.inv.left = inv φ := rfl
  have hsF : Geo.Tor.IsSquare (inv φ) (e.inv ⊗ₘ e.inv).left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst, Over.comp_left, heL]
    · rw [← Over.comp_left, tensorHom_snd, Over.comp_left, heL]
  refine ⟨inv φ, (e.inv ⊗ₘ e.inv).left, ⟨?_, ?_⟩, hsF, by simp, ?_⟩
  · refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← hw]
    simp
  · intro U x y x₀ y₀ hx hy
    have key := hφ.2 (Over.mk (U.hom ≫ 𝟙 T)) x₀ y₀ (Over.homMk x.left (by simp))
      (Over.homMk y.left (by simp)) (by simp [hx]) (by simp [hy])
    have hxy := mul_left_congr (a := (U.hom ≫ 𝟙 T) ≫ 𝟙 T) (b := U.hom) (by simp)
      (Over.homMk x.left (by simp)) (Over.homMk y.left (by simp)) x y (by simp) (by simp)
    rw [hxy.symm.trans key]
    simp
  · apply tensor_left_hom_ext'
    · rw [Category.assoc, hs.1, ← Category.assoc, hsF.1]
      simp
    · rw [Category.assoc, hs.2, ← Category.assoc, hsF.2]
      simp

theorem direct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), SiegData sT t lev Ag z bas w → ∃ (θ : t.G.left ⟶ Ag.univ.A.left) (θ₂ : (G2 t.G).left ⟶ (G2 Ag.univ.A).left), IsGrpPullback t.G Ag.univ.A (w ≫ pullback.fst _ _) θ ∧ IsSquare θ θ₂ ∧ LBIso (abelian₂ t.G t.PP.L) (Ag.univ.P.pull θ₂) ∧ ∀ u, (lev (bas u)).left ≫ θ = (w ≫ pullback.fst _ _) ≫ (Ag.univ.lev u).left := by
  intro E _ _ _ H D O _ T sT t lev g p N Ag z bas w hd
  obtain ⟨o, φ, φ₂, hφ, hs, hL, hlev, hcl, ψ, ψ₂, hψ, hs', hP, hlev'⟩ := hd
  obtain ⟨F, F₂, hF, hsF, hφF, hF₂⟩ := exists_inverse hφ hs
  have h0 : t.PP.L.IsLB := t.PP.isLB
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := by
    unfold abelian₂
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ h0 _ _
  refine ⟨F ≫ ψ, F₂ ≫ ψ₂, (hF.comp hψ).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hs'.1, ← Category.assoc, hsF.1, Category.assoc]
  · rw [Category.assoc, hs'.2, ← Category.assoc, hsF.2, Category.assoc]
  · have hΛ₁ := pull_isLB hΛ (𝟙 (G2 t.G).left)
    have hΛ₂ := pull_isLB (pull_isLB hΛ φ₂) F₂
    have hO := pull_isLB o.isLB F₂
    have hU₁ := pull_isLB (pull_isLB Ag.univ.isLB ψ₂) F₂
    have hU₂ := pull_isLB Ag.univ.isLB (F₂ ≫ ψ₂)
    have s1 : LBIso (abelian₂ t.G t.PP.L) ((abelian₂ t.G t.PP.L).pull (𝟙 _)) := iso_pull_id hΛ
    have s2 : LBIso ((abelian₂ t.G t.PP.L).pull (𝟙 _)) (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) := by
      have k := iso_pull_pull hΛ φ₂ F₂
      rw [hF₂] at k
      exact k.symm
    have s3 : LBIso (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) (o.P.pull F₂) := (iso_pull F₂ hL).symm
    have s4 : LBIso (o.P.pull F₂) ((Ag.univ.P.pull ψ₂).pull F₂) := iso_pull F₂ hP
    have s5 : LBIso ((Ag.univ.P.pull ψ₂).pull F₂) (Ag.univ.P.pull (F₂ ≫ ψ₂)) := iso_pull_pull Ag.univ.isLB ψ₂ F₂
    exact LBIso.trans hΛ hΛ₁ hU₂ s1 (LBIso.trans hΛ₁ hΛ₂ hU₂ s2
      (LBIso.trans hΛ₂ hO hU₂ s3 (LBIso.trans hO hU₁ hU₂ s4 s5)))
  · intro u
    rw [← hlev u]
    simp only [Category.assoc, reassoc_of% hφF]
    exact hlev' u

end GlobalTheory.SiegelDirect

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullRigid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_field (hS : Out.SerreSt) {S : Scheme.{0}} {t : SAB H S} (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) {K : Type} [Field K] [CharZero K] {z : Sp K ⟶ S}
    {t' : SAB H (Sp K)} (m m' : SABMap t' t z) {N : ℕ} (hN : 3 ≤ N)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Sp K) (y : Over.mk x ⟶ t'.G),
      y ^ N = 1 → y.left ≫ m.φ = y.left ≫ m'.φ) : m.φ = m'.φ := by
  obtain ⟨θ, hθ, hφ, -, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w₁, g₁, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have : ConnectedSpace t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp K) :=
    { A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB
      ample := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) U hU hy hA
      ktriv := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) hK
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have hNK : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
  have hMu : IsUnit (N : Γ(Sp K, ⊤)) := by
    simpa using hNK.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : Etale (Out.mulA t'.G N).left := GrpTangent.etale_id_pow t'.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine hS (Sp K) P N hN θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t'.G N θ.hom fun k _ _ x y hy => ?_)
    · obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (t'.G.hom ⁻¹ᵁ ⊤).ι
      refine gen_chartPull (chartPullOut t'.PP.L _ _ _ _ fun n => ?_) t ht
      fin_cases n
      exacts [rfl, (Category.comp_id _).symm]
    · let β : K →+* k := (Spec.preimage x).hom
      have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
      apply Over.OverMorphism.ext
      apply m'.cart.1.hom_ext
      · rw [Over.comp_left, Category.assoc]
        exact (congrArg _ hφ).trans (hfix k x y hy)
      · rw [Over.w, Over.w]
  rw [← hφ, h, Over.id_left, Category.id_comp]

theorem eq_on_torsion {D : Datum H} {n N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S}
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {t' : SAB H S'} {f : S' ⟶ S} (ν ν' : SABMap t' t f)
    (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)) (hN : 0 < N) (o : FullObj D s t lev)
    (h : ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) (h' : ∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ t'.G) (hy : y ^ N = 1) :
    y.left ≫ ν.φ = y.left ≫ ν'.φ := by
  obtain ⟨-, I, -, hI⟩ := o.geom k (x ≫ f) (Spec.preimage ((x ≫ f) ≫ s)).hom (Spec.map_preimage _).symm
  have hy₁ : pushHom ν.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN _).1 hy₁
  have e : (x ≫ f) ≫ (lev a).left = y.left ≫ ν.φ := congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply ν.cart.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h a).trans (h' a).symm)

end GlobalTheory.FullRigid

theorem GlobalTheory.fullObj_rigid : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (t' : SAB H S') (f : S' ⟶ S) (ν ν' : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), 3 ≤ N → Odd N → FullObj D s t lev → IsReduced S' → (∀ x : S', CharZero (S'.residueField x)) → (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → (∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left) → ν.φ = ν'.φ := by
  intro hL E _ _ _ H D n N S S' s t lev t' f ν ν' lv hN _ o _ hc h h'
  obtain ⟨θ, hθ, hφ, -⟩ := sabMap_iso ν ν' rfl rfl
  have hA : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 o.proper, t'.semi.geomConnected⟩
  have key : θ.hom = 𝟙 _ := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre hL.globalFns t'.G hA θ.hom (IsMonHom.one_hom θ.hom) fun p => ?_
    have := hc p
    let j : Sp (S'.residueField p) ⟶ S' := S'.fromSpecResidueField p
    have hsemi : IsSemiAbelian ((Over.pullback j).obj t'.G) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := t'.semi.comm; infer_instance
      · have := t'.semi.smooth; change Smooth (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.separated; change IsSeparated (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.quasiCompact; change QuasiCompact (pullback.snd t'.G.hom j); infer_instance
      · have := t'.semi.geomConnected; change GeometricallyConnected (pullback.snd t'.G.hom j); infer_instance
      · intro Ω _ _ q
        obtain ⟨E⟩ := t'.semi.fibres Ω (q ≫ j)
        exact ⟨torusExtOfIso (pullCompIso q j t'.G) E⟩
    have hPull : ∃ (PP' : RigLB ((Over.pullback j).obj t'.G))
        (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback j).obj t'.G, hsemi,
          OAct.pullback j t'.G t'.act, PP', cub, sym, adj, prim⟩ t' j),
        m.φ = pullback.fst t'.G.hom j := by
      have h := isGrpPullback_pullback t'.G j
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull _ _ t'.G _ (cubeMapOf h) t'.PP t'.cub
      have hact : ∀ a, ((OAct.pullback j t'.G t'.act).act a).left ≫ pullback.fst t'.G.hom j =
          pullback.fst t'.G.hom j ≫ (t'.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over (Sp (S'.residueField p))} (x : T ⟶ (Over.pullback j).obj t'.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback j t'.G t'.act).act a) = pushPt h.1.w x ≫ t'.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB t'.PP hL hr, c', hs t'.sym, fun a => ?_, ?_,
        ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback j).obj t'.G) ((Over.pullback j).obj t'.G)))
          (pushPt h.1.w (snd ((Over.pullback j).obj t'.G) ((Over.pullback j).obj t'.G)))
        refine LBIso.chartPull (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t'.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback j).obj t'.G))
        refine LBIso.chartPull (chartPullPull t'.PP.L _)
          (chartPullLinComb t'.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t'.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := hPull
    generalize (⟨(Over.pullback j).obj t'.G, hsemi,
      OAct.pullback _ t'.G t'.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t'' at m
    obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m
    obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' m
    have e : a.φ = b.φ := GlobalTheory.FullRigid.eq_of_field hL.serre o.proper o.ample o.ktriv a b hN fun k _ _ _ x y hy => by
      have hy₁ : pushHom m.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
      have e₁ := GlobalTheory.FullRigid.eq_on_torsion ν ν' lv (by omega) o h h' k (x ≫ j) _ hy₁
      rw [ha, hb, ← Category.assoc, ← Category.assoc]
      exact e₁
    refine ⟨_, _, j, m.φ, _, (default : PrimeSpectrum (S'.residueField p)),
      Scheme.fromSpecResidueField_apply p _, m.cart.1, ?_⟩
    apply ν'.cart.1.hom_ext
    · rw [Category.assoc]
      exact (congrArg (m.φ ≫ ·) hφ).trans (ha.symm.trans (e.trans hb))
    · rw [Category.assoc, Over.w]
  rw [← hφ, key, Over.id_left, Category.id_comp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayFlatProjRep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearCut


open MvPolynomial in
theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI := (MvPolynomial.gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R))
  have h : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨d, hx.1⟩
  have := h e hF
  rwa [show ((DirectSum.decompose (homogeneousSubmodule σ R) F e : homogeneousSubmodule σ R e) : MvPolynomial σ R)
    = homogeneousComponent e F from MvPolynomial.decomposition.decompose'_apply F e] at this


open MvPolynomial in
theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  intro F hF
  have key : ∀ e, eval₂ β v (homogeneousComponent e F) = 0 := by
    intro e
    have h1 : ∀ i, v i ^ d * eval₂ β v (homogeneousComponent e F) = 0 := by
      intro i
      have := hJ _ (hle (d + e) (by omega) (X i ^ d * homogeneousComponent e F)
        ((isHomogeneous_X_pow i d).mul (homogeneousComponent_isHomogeneous e F)) (I.mul_mem_left _ (hI F hF e)))
      rwa [eval₂_mul, eval₂_pow, eval₂_X] at this
    have h2 := Ideal.span_pow_eq_top _ hv d
    have h3 : Ideal.span ((fun x => x ^ d) '' Set.range v) ≤
        LinearMap.ker (LinearMap.toSpanSingleton T T (eval₂ β v (homogeneousComponent e F))) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact h1 i
    rw [h2] at h3
    simpa using h3 (Submodule.mem_top (x := (1 : T)))
  rw [← sum_homogeneousComponent F, eval₂_sum]
  exact Finset.sum_eq_zero fun e _ => key e

theorem exists_away_flat_projRep : ∀ (R σ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ (Z : Over (Sp (Localization.Away f))) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d (fun h i => loc f (p h i))) Z.hom M th ∧ Flat Z.hom ∧ ∀ (K : Type) [Field K] (x : Localization.Away f →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → CutBy I Q d (fun h i => x (loc f (p h i))) → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  intro R σ Hh _ _ _ _ _ p Q d P hP hcutP q₀ hq₀
  obtain ⟨f, hf, hproj, hmap⟩ := _root_.GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal R σ Hh p Q d P hP hcutP q₀ hq₀
  obtain ⟨Z, s, M, th, -, hrep, -, hflat⟩ := _root_.GlobalTheory.ProjFlat.exists_projRep_flat (Localization.Away f) σ
    (vanIdeal d (fun h i => loc f (p h i))) d (homogeneousComponent_mem_vanIdeal d _)
  refine ⟨f, hf, Over.mk s, M, th, hrep, hflat fun e he => by have := hproj e he; infer_instance, ?_⟩
  intro K _ x I X s' M' th' hI hcut hrep'
  have hpb := IsPullback.of_hasPullback s (spMap x)
  obtain ⟨th₁, hrep₁, hc₁⟩ := _root_.GlobalTheory.ZM.RepBC.projRep_baseChange _ K σ x _ Z _ s _ _ M th hrep hpb
  rw [hmap K x] at hrep₁
  obtain ⟨e, he, hiso, hc⟩ := _root_.GlobalTheory.RepUniq.exists_iso_of_projRep K σ I _ X _ s' _ M' _ th' th₁ hrep' hrep₁ fun T _ β v hv =>
    ⟨eval₂_eq_zero_of_forms_le (homogeneousComponent_mem_vanIdeal d _) (fun e he F hF h => ((hcut e he).2 F hF).2 h) β v hv,
      eval₂_eq_zero_of_forms_le hI (fun e he F hF h => ((hcut e he).2 F hF).1 h) β v hv⟩
  refine ⟨e.hom ≫ pullback.fst s (spMap x), ?_, ?_, fun T _ y w => ?_⟩
  · have h0 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
    simpa using h0.paste_horiz hpb
  · exact LBIso.trans hrep'.1 (pull_isLB hrep₁.1 _) (pull_isLB hrep.1 _) hiso
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ e.hom e.hom rfl) (chartPullSame M _ _ _ e.hom fun _ => rfl)
        ⟨_, idIso_isGen hrep₁.1⟩)
  · rw [hc T y w, hc₁ T _ w, Category.assoc]

end GlobalTheory.ZM.NearCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_finite_etale_surjective_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  first | exact @GlobalTheory.LevelMap.exists_levelMap | exact GlobalTheory.LevelMap.exists_levelMap | (intros; apply GlobalTheory.LevelMap.exists_levelMap <;> assumption)
end

