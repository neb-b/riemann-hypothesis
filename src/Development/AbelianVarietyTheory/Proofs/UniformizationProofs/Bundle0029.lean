module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionEndomorphismExpansion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PullInt

theorem oneLeft {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ eSec M := by
  have h : (toUnit X).left = X.hom := by simpa using Over.w (toUnit X)
  rw [Hom.one_def, Over.comp_left, h]; rfl

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (a b : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun i => ((a : ℤ) - b) * ε i)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ ((a : ℤ) - b) := by
  obtain ⟨t', h₁, h₂⟩ := exists_gen hL (φ' := φ) (ε' := fun i => ((a : ℤ) - b) * ε i) (fun U _ h => by
      rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← zpow_add]; congr 1; ring)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L φ ε t a) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t b)))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ ht a) (invGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ ht b)))
  refine ⟨t', h₁, fun Z r z J hJ => (h₂ Z r z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
  rw [val_inv, zpow_sub, zpow_natCast, zpow_natCast]
  exact congrArg₂ (fun u v => u * v⁻¹) (map_pow _ _ _) (map_pow _ _ _)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem rig_val (e : ℕ) {Z : Scheme.{0}} (s : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) {z : Z}
    {N : (Z ⟶ G.left) → U.LG.L.ι} {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hN : Good U.LG.L z N) (hJ : Good D.toPre.P.L z J) (o : Z ⟶ (thickObj R I e G).left)
    (ho : o = s ≫ eSec (thickObj R I e G)) :
    rigV D.toPre (s ≫ thick R I e) z J =
      wv U e o z (J (o ≫ pGl U e)) (N (o ≫ fGl I G e)) *
        val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (s ≫ thick R I e) z N := by
  subst ho
  have hp : (s ≫ eSec (thickObj R I e G)) ≫ pGl U e = (s ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_pGl U e)).trans
      (Category.assoc _ _ _).symm)
  have hf : (s ≫ eSec (thickObj R I e G)) ≫ fGl I G e = (s ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (UnitValue.eSec_fGl (G := G) e)).trans
      (Category.assoc _ _ _).symm)
  rw [hp, hf, rigV]
  obtain ⟨j, hj⟩ : ∃ j, J ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) = j := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, N ((s ≫ thick R I e) ≫ eSec G) = k := ⟨_, rfl⟩
  have mj : ((s ≫ thick R I e) ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U j := hj ▸ hJ _
  have mk : ((s ≫ thick R I e) ≫ eSec G) z ∈ U.LG.L.U k := hk ▸ hN _
  rw [val_of _ _ z J (fun _ => j) (fun _ => hj), val_of _ _ z N (fun _ => k) (fun _ => hk), hj, hk]
  have m₁ : s z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U j) hp).mpr mj),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U k) hf).mpr mk)⟩
  have m₂ : s z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => k) := mem_pull.2 mk
  have m₃ : s z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => j) := mem_pull.2 mj
  have W := congrArg (gm s z _) (U.w_rig e (fun _ => j, fun _ => k) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₃ _)).symm.trans (W.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₁ _))
      ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₂ _)))))

variable {U} (E : EndU U)

theorem act_fGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e = fGl I G e ≫ E.aG.left :=
  pullback.lift_fst _ _ _

theorem act_pGl (e : ℕ) :
    ((Over.pullback (thick R I e)).map E.aG).left ≫ pGl U e = pGl U e ≫ E.aB.left := by
  have h1 := congrArg (fun f => f.left) (E.q_lin e)
  simp only [Over.comp_left] at h1
  simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left]
  rw [← Category.assoc, h1, Category.assoc, Category.assoc]
  congr 1
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem exists_secG (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left]
    ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])) (hβ : β.IsGen) (σ : H0 U.LG.L k) :
    ∃ σ' : H0 U.LG.L k', ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J →
      sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G)
        (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow U.LG.isLB (LB.pullGen U.LG.L (fun _ : PUnit => eSec G) (fun _ => 1) U.LG.rig G.hom)
    (pullGen_isGen _ _ _ _ U.LG.rigGen _) k' k
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => (k' : ℤ)) (fun V _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_three, Matrix.cons_val, Category.comp_id,
        Fintype.prod_unique, oneLeft]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec σ E.aG.left (LB.mulGen U.LG.L _ _ _ _ β ρ) (mulGen_isGen _ _ _ _ _ _ _ hβ hρ))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, vρ Z r z J hJ, val_pull hJ]

theorem exists_secB (k' k : ℕ) (κ : LB.Gen (kapLB D.toPre E.aB k' k)) (hκ : κ.IsGen) (χ : D.toPre.X)
    (f : D.toPre.SecB k χ) :
    ∃ g : D.toPre.SecB k' (E.h χ), ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval g r z J = sval f (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val := by
  obtain ⟨ρ, hρ, vρ⟩ := exists_zpow D.toPre.P.isLB (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A)
    (fun _ => 1) D.toPre.rig D.toPre.P.A.hom) (pullGen_isGen _ _ _ _ D.toPre.rig_gen _) k' k
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (φ' := D.toPre.famφB (E.h χ)) (ε' := DegPre.famε k') (fun V _ h => by
      have p₁ := SectionScalarValuation.prod_famB D.toPre E.aB χ k h
      have p₂ := SectionScalarValuation.prod_famB D.toPre (𝟙 _) (E.h χ) k' h
      have e₃ : ∀ i, Over.Hom.left (𝟙 D.toPre.P.A) ≫ D.toPre.famφB (E.h χ) i = D.toPre.famφB (E.h χ) i :=
        fun i => by simp
      simp only [e₃] at p₂
      have p₃ : ∏ i, h (D.toPre.Oφ (𝟙 _) (E.h χ) i) ^ Oε i =
          h (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ (E.h χ)).left ^ (-1 : ℤ) *
            h (Over.Hom.left (𝟙 D.toPre.P.A)) ^ (-1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      have p₄ : ∏ i, h (D.toPre.Oφ E.aB χ i) ^ Oinvε i =
          h (E.aB * SectionScalarValuation.cQ D.toPre _ χ).left ^ (-1 : ℤ) * h (SectionScalarValuation.cQ D.toPre _ χ).left ^ (1 : ℤ) *
            h E.aB.left ^ (1 : ℤ) * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four]; rfl
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p₁, p₂, p₃, p₄]
      simp only [Fin.prod_univ_three, Matrix.cons_val, Fintype.prod_unique, oneLeft, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (pullMulSec f E.aB.left (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ κ ρ) (E.u χ))
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hκ hρ) (E.u_norm χ).1))
  refine ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)⟩
  rw [val_mul hJ, val_mul hJ, vρ Z r z J hJ, val_pull hJ, rigV]

theorem alg {Γ : Type} [CommRing Γ] (k' k : ℕ) (wx wa wo β κ ρG ρB : Γˣ) (s : Γ)
    (h₁ : κ = β * wx ^ (k' : ℤ) * wa ^ (-(k : ℤ)) * wo ^ ((k : ℤ) - k')) (h₂ : ρB = wo * ρG) :
    (wx ^ k').val * (s * (β * ρG ^ ((k' : ℤ) - k)).val) = (κ * ρB ^ ((k' : ℤ) - k)).val * ((wa ^ k).val * s) := by
  have : wx ^ k' * (β * ρG ^ ((k' : ℤ) - k)) = κ * ρB ^ ((k' : ℤ) - k) * wa ^ k := by
    rw [h₁, h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
    module
  rw [mul_comm s, ← _root_.mul_assoc, ← Units.val_mul, this, Units.val_mul, _root_.mul_assoc]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U), Function.Injective E.h → ∀ (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), κ.IsGen → (∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k')) → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → ∃ (σ' : H0 U.LG.L k') (f' : ∀ α : D.toPre.X, D.toPre.SecB k' α), (∀ e, U.ExpandsAt e k' σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good U.LG.L z J → sval σ' r z J = sval σ (r ≫ E.aG.left) z J * (val β r z J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ G.hom) z J ^ ((k' : ℤ) - k)).val) ∧ (∀ (χ : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f' (E.h χ)) r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J * rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧ ∀ b, b ∉ Set.range E.h → ∀ j, (f' b).f j = 0 := by
  classical
  intro R _ _ I D A G _ _ U E hinj k' k β hβ κ hκ H σ f hf
  obtain ⟨σ', hσ'⟩ := exists_secG E k' k β hβ σ
  have key : ∀ b, ∃ s : D.toPre.SecB k' b, (∀ χ, b = E.h χ → ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval s r z J = sval (f χ) (r ≫ E.aB.left) z J * (val κ r z J *
        rigV D.toPre (r ≫ D.toPre.P.A.hom) z J ^ ((k' : ℤ) - k) * val (E.u χ) r z J).val) ∧
      (b ∉ Set.range E.h → ∀ j, s.f j = 0) := by
    intro b
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨g, hg⟩ := exists_secB E k' k κ hκ χ (f χ)
      refine ⟨g, fun χ' e => ?_, fun h => (h ⟨χ, rfl⟩).elim⟩
      obtain rfl := hinj e
      exact hg
    · exact ⟨SecOps.secZero, fun χ e => (hb ⟨χ, e.symm⟩).elim, fun _ _ => rfl⟩
  choose f' hf₁ hf₂ using key
  refine ⟨σ', f', fun e => ?_, hσ', fun χ => hf₁ _ χ rfl, hf₂⟩
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f (hf e)
  refine expandsAt_of_val U e k' σ' f' (S.image E.h) fun y J hJ => ?_
  obtain ⟨b₁, b₂⟩ := hS _ ((Over.pullback (thick R I e)).map E.aG).left y J hJ
  simp only [act_pGl E e, act_fGl E e] at b₁
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · by_cases hb : α ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      rw [hf₁ _ χ rfl _ _ y J hJ, b₁ χ fun h => hα (Finset.mem_image_of_mem _ h), zero_mul]
    · exact (congrArg (gs _ y _) (hf₂ α hb _)).trans (gs_zero _ y _ (hJ.mem _ _))
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : Unit => fGl I G e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : JG (fGl I G e) = jL := eJ ()
    have c₁ := b₂ _ (hJG (((Over.pullback (thick R I e)).map E.aG).left ≫ fGl I G e))
    have c₂ := H e _ (𝟙 _) _ y JG J hJG hJ rfl
      (fun x => wv U e x y (J (x ≫ pGl U e)) (JG (x ≫ fGl I G e))) (fun _ => rfl)
    have c₃ := rig_val U e (thickObj R I e G).hom hJG hJ _ oneLeft
    have c₄ := hσ' _ (fGl I G e) y JG hJG
    have sv_eq : ∀ (n : ℕ) (τ : H0 U.LG.L n) (q : (thickObj R I e G).left ⟶ G.left),
        sval τ q y JG = sv U n τ q y (JG q) := fun n τ q =>
      sval_of τ q y JG (fun _ => JG q) (fun _ => by rw [Category.comp_id])
    have w₁ : fGl I G e ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have w₂ : pGl U e ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
    simp only [Category.id_comp] at c₂
    rw [sv_eq, sv_eq, w₁, ← act_fGl E e] at c₄
    rw [c₄, Finset.sum_image fun _ _ _ _ h => hinj h]
    refine (alg k' k _ _ _ _ _ _ _ _ c₂ c₃).trans ?_
    rw [c₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have t := E.t_lin e χ _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at t
    rw [hf₁ _ χ rfl _ _ y J hJ, w₂, act_pGl E e]
    refine (congrArg (fun u : ((thickObj R I e G).left.presheaf.stalk y)ˣ => _ * (_ * u.val)) t).trans ?_
    simp only [Units.val_mul]
    ring

end GlobalTheory.PullInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EvenPull

theorem pmaps_of_section {X X' Y Y' S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (π : Y' ⟶ S₀) (e : S₀ ⟶ Y') (he : e ≫ π = 𝟙 _) (hp : Function.Surjective π.appTop.hom)
    (H : ∀ y J J', Good L y J → Good L' y J' → val t (e ≫ h) y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique' hL (φ := fun k => h ≫ φ k) (ε := ε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ ε I) (hψ I))
    π e he hp (DVR.pullGen_isGen _ _ _ _ ht h) ht₁ (fun y J hJ => by
      choose J' hJ' using fun χ : S₀ ⟶ X' => exists_chart hL' (χ y)
      refine (val_pull hJ _ _ _).trans ((H y J J' hJ hJ').trans (Eq.trans ?_
        (hv _ e y _ _ (hJ.mem _ e) (Good.mem hJ' _ e)).symm))
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl
      rw [Category.assoc])
  intro Z r z p q hp hq
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have m₁ : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  have m₂ : (r ≫ h) z ∈ LB.wchart L φ p := Set.mem_iInter.2 fun k =>
    (congrArg (fun g => g (r z) ∈ L.U (p k)) (hψ k)).mp (hp k)
  have c₁ := gen_trans ht (r ≫ h) z m₂ (Good.mem hJ _ _)
  have c₂ := gen_trans ht₁ r z m₁ (Good.mem hJ _ _)
  have c₃ : trF φ ε (r ≫ h) z p (fun k => J ((r ≫ h) ≫ φ k)) =
      trF (fun k => φ' k ≫ F) ε r z p (fun k => J (r ≫ φ' k ≫ F)) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (r ≫ h) ≫ φ k = r ≫ φ' k ≫ F := by rw [hψ, Category.assoc]
    show gm ((r ≫ h) ≫ φ k) z (L.U (p k) ⊓ L.U (J ((r ≫ h) ≫ φ k))) (L.g (p k) (J ((r ≫ h) ≫ φ k))) ^ _ =
      gm (r ≫ φ' k ≫ F) z (L.U (p k) ⊓ L.U (J (r ≫ φ' k ≫ F))) (L.g (p k) (J (r ≫ φ' k ≫ F))) ^ _
    rw [this]
  have c₄ : val t (r ≫ h) z J = val t₁ r z J := (val_pull hJ _ _ _).symm.trans (key Z r z J hJ)
  exact c₁.trans ((congrArg₂ (· * ·) c₃ c₄).trans (c₂.symm.trans (hv Z r z p q m₁ (Set.mem_iInter.2 hq))))

theorem inv_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (ι[(Over.pullback f).obj G]).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ι[G]).left := by
  rw [Functor.obj.ι_def]
  exact pullback.lift_fst _ _ _

theorem inv_left_comp {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (b : G' ⟶ G) [IsMonHom b] :
    (ι[G']).left ≫ b.left = b.left ≫ (ι[G]).left := by
  rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]

theorem inv_hom_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {G' : Over S'} [GrpObj G']
    (b : G' ⟶ (Over.pullback f).obj G) [IsMonHom b] :
    (ι[G']).left ≫ b.left ≫ pullback.fst G.hom f = (b.left ≫ pullback.fst G.hom f) ≫ (ι[G]).left := by
  rw [← Category.assoc, inv_left_comp b, Category.assoc, Category.assoc]
  exact congrArg (b.left ≫ ·) (inv_fst f G)

theorem eSec_inv {S : Scheme.{0}} (H : Over S) [GrpObj H] : eSec H ≫ (ι[H]).left = eSec H := by
  rw [eSec, ← Over.comp_left, GrpObj.one_inv]

theorem sym_pmaps (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := Fin 2) ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]
      D'.sym D.sym (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have := hD.e_hom
  refine pmaps_of_section ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB _ (fun k => ?_) _ D'.sym_gen _ D.sym_gen
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (fun y J J' hJ hJ' => ?_)
  · fin_cases k
    · exact inv_hom_fst _ _ hD.e.hom
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have a₁ := val_corr hJ D.sym_rig (specOf φ)
    have a₂ := val_corr hJ' D'.sym_rig (𝟙 _)
    rw [val_pull hJ, val_one] at a₁
    rw [val_pull hJ', val_one, Category.id_comp] at a₂
    rw [hD.he, a₂, Fin.prod_univ_two]
    refine a₁.trans ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eSec_inv, Category.comp_id]
    simp

theorem even_stalk {T G B Z : Scheme.{0}} {L : LB G} {M : LB B} {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G}
    {iB : B ⟶ B} (w : LB.Iso (L.pull f) (M.pull p))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι)
    (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
    (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
    (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
    (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS) (r : Z ⟶ T) (z : Z) (hz : r z ∈ V) :
    gm r z V (res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1))) =
      gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) * gw w r z (jT 1) (fun _ => jS 1) ∧
    gm r z V (res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))) =
      gw w (r ≫ iT) z (jT 0) (fun _ => jS 0) * gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) :=
  ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z h₁ hz _).trans (gm_pull r p z _ (h₁ hz) _))
      (gm_res r z h₂ hz _)),
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z h₃ hz _).trans (gm_pull r iT z ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) (@h₃ (r z) hz) _))
      ((gm_res r z h₄ hz _).trans (gm_pull r f z _ (h₄ hz) _)))⟩

theorem even_of_square {T G B T' G' B' : Scheme.{0}} {L : LB G} {M : LB B} {L' : LB G'} {M' : LB B'}
    (hL : L.IsLB) (hM : M.IsLB)
    {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {f' : T' ⟶ G'} {p' : T' ⟶ B'} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    {Ψ : G' ⟶ G} {Φ : B' ⟶ B} {h : T' ⟶ T}
    (hf : h ≫ f = f' ≫ Ψ) (hp : p' ≫ Φ = h ≫ p) (ih : iT' ≫ h = h ≫ iT)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iF' : iT' ≫ f' = f' ≫ iG') (iP' : iT' ≫ p' = p' ≫ iB')
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p'))
    (wL : LB.Iso L' (L.pull Ψ)) (wM : LB.Iso M' (M.pull Φ))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hs : PMaps wL (K := Fin 2) ![iG', 𝟙 G'] ![iG, 𝟙 G] ![1, -1] s' s Ψ)
    (hσ : PMaps wM (K := Fin 2) ![iB', 𝟙 B'] ![iB, 𝟙 B] ![1, -1] σ' σ Φ)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      Φ (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → Ψ (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL')
    (ev : ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
      ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
        (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
        (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
        (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
        res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1)) =
          res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS)))
    (jS' : Fin 2 → L'.ι) (jT' : Fin 2 → M'.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]).U jT')
    (h₂ : V ≤ (M'.pull p').U (fun _ => jT' 1) ⊓ (L'.pull f').U (fun _ => jS' 1))
    (h₃ : V ≤ iT' ⁻¹ᵁ ((M'.pull p').U (fun _ => jT' 0) ⊓ (L'.pull f').U (fun _ => jS' 0)))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]).U jS') :
    res h₁ (pullU p' _ (σ'.s jT')) * res h₂ (w'.s (fun _ => jT' 1, fun _ => jS' 1)) =
      res h₃ (pullU iT' _ (w'.s (fun _ => jT' 0, fun _ => jS' 0))) * res h₄ (pullU f' _ (s'.s jS')) := by
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := even_stalk w' s' σ' jS' jT' V h₁ h₂ h₃ h₄ (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  choose JL hJL using fun χ : T' ⟶ G => exists_chart hL (χ z)
  choose JM hJM using fun χ : T' ⟶ B => exists_chart hM (χ z)
  obtain ⟨jS, hjS, cS⟩ : ∃ jS : Fin 2 → L.ι, (∀ k, (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) z ∈ L.U (jS k)) ∧
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS :=
    ⟨fun k => JL (h ≫ f ≫ (![iG, 𝟙 G] : Fin 2 → _) k), fun k => hJL _,
      fun a b e => congrArg (fun q => JL (h ≫ q)) e⟩
  obtain ⟨jT, hjT, cT⟩ : ∃ jT : Fin 2 → M.ι, (∀ k, (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) z ∈ M.U (jT k)) ∧
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT :=
    ⟨fun k => JM (h ≫ p ≫ (![iB, 𝟙 B] : Fin 2 → _) k), fun k => hJM _,
      fun a b e => congrArg (fun q => JM (h ≫ q)) e⟩
  have S0 : (h ≫ f ≫ iG) z ∈ L.U (jS 0) := hjS 0
  have S1 : (h ≫ f) z ∈ L.U (jS 1) := hjS 1
  have T0 : (h ≫ p ≫ iB) z ∈ M.U (jT 0) := hjT 0
  have T1 : (h ≫ p) z ∈ M.U (jT 1) := hjT 1
  have OrbitIntegralProperties : (h ≫ iT ≫ f) z ∈ L.U (jS 0) := by rw [iF]; exact S0
  have T0a : (h ≫ iT ≫ p) z ∈ M.U (jT 0) := by rw [iP]; exact T0
  have S0b : (iT' ≫ f' ≫ Ψ) z ∈ L.U (jS 0) := by rw [← hf, ← Category.assoc, ih, Category.assoc]; exact OrbitIntegralProperties
  have T0b : (iT' ≫ p' ≫ Φ) z ∈ M.U (jT 0) := by rw [hp, ← Category.assoc, ih, Category.assoc]; exact T0a
  have S0c : ((f' ≫ iG') ≫ Ψ) z ∈ L.U (jS 0) := by rw [← iF', Category.assoc]; exact S0b
  have T0c : ((p' ≫ iB') ≫ Φ) z ∈ M.U (jT 0) := by rw [← iP', Category.assoc]; exact T0b
  have TopsChoiceSecondBound : (f' ≫ Ψ) z ∈ L.U (jS 1) := by rw [← hf]; exact S1
  have T1b : (p' ≫ Φ) z ∈ M.U (jT 1) := by rw [hp]; exact T1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : h z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hjT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0a, mem_pull.2 OrbitIntegralProperties⟩,
    Set.mem_iInter.2 hjS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := even_stalk w s σ jS jT W l₁ l₂ l₃ l₄ h z hW
  have E := n₁.symm.trans ((congrArg (gm h z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  have A₁ := sq _ (𝟙 T') z (jT 1) (jT' 1) (jS 1) (jS' 1) T1b (mem_pull.1 (h₂ hz).1) TopsChoiceSecondBound (mem_pull.1 (h₂ hz).2)
  have A₀ := sq _ iT' z (jT 0) (jT' 0) (jS 0) (jS' 0) T0b (mem_pull.1 (h₃ hz).1) S0b (mem_pull.1 (h₃ hz).2)
  have Bσ := hσ _ p' z jT jT' (Fin.forall_fin_two.2 ⟨T0c, T1b⟩) (Set.mem_iInter.1 (h₁ hz))
  have Bs := hs _ f' z jS jS' (Fin.forall_fin_two.2 ⟨S0c, TopsChoiceSecondBound⟩) (Set.mem_iInter.1 (h₄ hz))
  rw [Fin.prod_univ_two] at Bσ Bs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg] at Bσ Bs
  simp only [Category.id_comp] at A₁ ⊢
  rw [iP', iF', ih] at A₀
  rw [hp] at Bσ
  rw [← hf] at Bs
  apply Additive.ofMul.injective
  have e₁ := congrArg Additive.ofMul E
  have e₂ := congrArg Additive.ofMul A₁
  have e₃ := congrArg Additive.ofMul A₀
  have e₄ := congrArg Additive.ofMul Bσ
  have e₅ := congrArg Additive.ofMul Bs
  simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ ⊢
  linear_combination (norm := abel) e₁ + e₂ - e₃ - e₄ + e₅

end GlobalTheory.EvenPull

namespace GlobalTheory


open GlobalTheory.EvenPull in
theorem pulled_comparison_even : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w' : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt' e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt' e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt' e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w' e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → ∀ (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen → Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' U.symG (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) → ∀ (e : ℕ) (jS : Fin 2 → L'.L.ι) (jT : Fin 2 → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (fstG I' e G').left ≫ (![(ι[G']).left, 𝟙 G'.left] : Fin 2 → _) k) jS → LB.Coh D'.toPre.P.L (fun k => (gt' e).pG.left ≫ (![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] : Fin 2 → _) k) jT → ∀ (V : (thickObj R' I' e G').left.Opens) (h₁ : V ≤ (gt' e).pG.left ⁻¹ᵁ (LB.LinComb D'.toPre.P.L (K := Fin 2) ![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] ![1, -1]).U jT) (h₂ : V ≤ (D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 1) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 1)) (h₃ : V ≤ (ι[thickObj R' I' e G']).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 0) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 0))) (h₄ : V ≤ (fstG I' e G').left ⁻¹ᵁ (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]).U jS), res h₁ (pullU (gt' e).pG.left _ (D'.toPre.sym.s jT)) * res h₂ ((w' e).s (fun _ => jT 1, fun _ => jS 1)) = res h₃ (pullU (ι[thickObj R' I' e G']).left _ ((w' e).s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU (fstG I' e G').left _ (s'.s jS)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ hbc U L' wL _ _ _ gt' w' _ _ H s' _ hs e jS jT _ _
    V h₁ h₂ h₃ h₄
  obtain ⟨h, hf, ⟨hp, -⟩, sq⟩ := H e
  have iF : ∀ {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G],
      (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    fun I G _ => inv_fst _ G
  have iP : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
      {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G),
      (ι[thickObj R I e G]).left ≫ g.pG.left = g.pG.left ≫ (ι[D.P.A]).left := fun g => by
    have := g.q_hom
    exact inv_hom_fst _ _ g.q
  have : Mono (thick R I e) := by
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have m : Mono (fstG I e G).left := pullback.fst_of_mono
  have ih : (ι[thickObj R' I' e G']).left ≫ h = h ≫ (ι[thickObj R I e G]).left := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, Category.assoc, hf, iF, ← Category.assoc, iF,
      Category.assoc, inv_hom_fst _ _ bc.hom, ← Category.assoc h, hf]
    simp only [Category.assoc]
  exact even_of_square U.LG.isLB D.toPre.P.isLB hf hp ih (iF I G) (iP _) (iF I' G') (iP _) (U.w e) (w' e) wL hD.w
    U.symG D.toPre.sym s' D'.toPre.sym hs (sym_pmaps hG hD) sq (U.w_even e) jS jT V h₁ h₂ h₃ h₄

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumIOfFinite
section
namespace GlobalTheory.UT

theorem sumI_of_finite {R : Type} [CommRing R] (I : Ideal R) {E Ix : Type} [AddCommGroup E] [Module R E] (x : Ix → E)
    (S : Finset Ix) (hS : ∀ i, i ∉ S → x i = 0) : SumI I x (∑ i ∈ S, x i) := by
  classical
  have hx : ∀ i, x i ∈ Submodule.span R (↑(S.image x) : Set E) := fun i => by
    by_cases h : i ∈ S
    · exact Submodule.subset_span (by simpa using ⟨i, h, rfl⟩)
    · rw [hS i h]; exact Submodule.zero_mem _
  refine ⟨Submodule.span R ↑(S.image x), ⟨_, rfl⟩, Submodule.sum_mem _ fun i _ => hx i, hx, fun n => ⟨S, fun T hT => ?_⟩⟩
  rw [Finset.sum_subset hT (fun i _ h => hS i h), sub_self]; exact Submodule.zero_mem _

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilIsCompIffOfRosatiAdj
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem weilIs_comp_iff_of_rosatiAdj : LL → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → RosatiAdj P.A P.L a a' → ∀ (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P.A P.L k (x ≫ a) y c ↔ WeilIs P.A P.L k x (y ≫ a') c := by
  intro h S _ P a a' ha ha' hR F _ p k x y hx hy c
  exact GlobalTheory.weilIs_rosati_iff h.1.globalFns h.1.cube P a a' hR k x y hx hy c

end GlobalTheory.UT
end

