module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmResPull
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ToChart

theorem gm_res_pull {X Y : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ g ⁻¹ᵁ U) {y : Y} (hy : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU g U a)) = gm g y U a :=
  (gm_res _ y h hy _).trans ((gm_pull (𝟙 Y) g y U (h hy) a).trans (by rw [Category.id_comp]))

theorem cub_alg' {M : Type} [CommGroup M] {C C' a b c d e g h k : M} (H : C * b * c * d * k = a * e * g * h * C') :
    C = a * b⁻¹ * c⁻¹ * d⁻¹ * e * g * h * k⁻¹ * C' := by
  apply Additive.ofMul.injective
  have H' := congrArg Additive.ofMul H
  simp only [ofMul_mul, ofMul_inv] at H' ⊢
  linear_combination (norm := abel) H'

theorem cube_left {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {T : Over S} {T' : Over S'} (β : (T' ⟶ G') →* (T ⟶ G)) (x : Fin 3 → (T' ⟶ G')) (k : thK) :
    (lift (β (x 0)) (lift (β (x 1)) (β (x 2)))).left ≫ thφ G (x3 G) k = (β (psum G' x k.down)).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift (β (x 0)) (lift (β (x 1)) (β (x 2))))) (x3 G) k.down).trans
    ((congrArg (fun q => psum G q k.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])).trans
      (psum_hom β x k.down).symm))

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)

def fstHom (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
    toBase_mul_pullback G (thick R I e) T x y

variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def projHom (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ g.pG) fun x y => by
    have := g.q_hom
    have h : ∀ a : T ⟶ thickObj R I e G, (Over.map (thick R I e)).map a ≫ g.pG = fstHom I e D.P.A T (a ≫ g.q) :=
      fun a => by rw [← Category.assoc, ← Functor.map_comp]; rfl
    rw [h, h, h, MonObj.mul_comp, map_mul]

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)

theorem w_compat (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (thickObj R I e G).left.Opens)
    (h₁ : V ≤ thickMap R I e G ⁻¹ᵁ ((D.P.L.pull (U.gt (e + 1)).pG.left).U p.1 ⊓
      (U.P.L.L.pull (fstG I (e + 1) G).left).U p.2))
    (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2) :
    res h₁ (pullU (thickMap R I e G) _ ((U.w (e + 1)).s p)) = res h₂ ((U.w e).s p) := by
  refine unit_ext fun y hy => ?_
  have := U.w_compat e _ (𝟙 _) y (p.1 PUnit.unit) (p.2 PUnit.unit) (mem_pull.1 (h₂ hy).1) (mem_pull.1 (h₂ hy).2)
  rw [Category.id_comp] at this
  exact (gm_res_pull _ h₁ hy _).trans (this.trans (gm_res _ y h₂ hy _).symm)

theorem w_rig (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))).Opens)
    (h₁ : V ≤ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2))
    (h₂ : V ≤ thick R I e ⁻¹ᵁ (U.P.L.L.pull (eSec G)).U p.2)
    (h₃ : V ≤ thick R I e ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U p.1) :
    res h₁ (pullU (eSec (thickObj R I e G)) _ ((U.w e).s p)) *
      res h₂ (pullU (thick R I e) _ (U.P.L.rig.s p.2)) =
      res h₃ (pullU (thick R I e) _ (D.rig.s p.1)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec G, eSec (thickObj R I e G) ≫ (fstG I e G).left] (fun _ => p.2 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₂ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).2 PUnit.unit⟩)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec D.P.A, eSec (thickObj R I e G) ≫ (U.gt e).pG.left] (fun _ => p.1 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₃ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).1 PUnit.unit⟩)
  have H := (U.w_vals e (𝟙_ _) y JG J hJG hJ _ (fun _ => rfl)).1
  have o : (1 : 𝟙_ _ ⟶ thickObj R I e G).left = eSec (thickObj R I e G) :=
    (one_left _ _).trans (Category.id_comp _)
  have t : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).hom ≫ thick R I e = thick R I e := Category.id_comp _
  rw [o, t] at H
  have a := val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (thick R I e) y J p.1
    (fun _ => eB 0)
  have b := val_of (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (thick R I e) y JG p.2
    (fun _ => eG 0)
  have c := congrArg₂ (fun j k => gw (U.w e) (eSec (thickObj R I e G)) y j (fun _ => k)) (eB 1) (eG 1)
  refine (map_mul _ _ _).trans (Eq.trans ?_ (gm_res_pull _ h₃ hy _).symm)
  refine (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res_pull _ h₂ hy _)).trans ?_
  exact (a.symm.trans (H.trans (congrArg₂ (· * ·) c b))).symm

theorem w_even (e : ℕ) (jS : Fin 2 → U.P.L.L.ι) (jT : Fin 2 → D.P.L.ι)
    (cS : LB.Coh U.P.L.L (fun k => (fstG I e G).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) jS)
    (cT : LB.Coh D.P.L
      (fun k => (U.gt e).pG.left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) jT)
    (V : (thickObj R I e G).left.Opens)
      (h₁ : V ≤ (U.gt e).pG.left ⁻¹ᵁ (LB.LinComb D.P.L (K := Fin 2)
        ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]).U jT)
      (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 1) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 1))
      (h₃ : V ≤ (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 0) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 0)))
      (h₄ : V ≤ (fstG I e G).left ⁻¹ᵁ (LB.LinComb U.P.L.L (K := Fin 2)
        ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS) :
      res h₁ (pullU (U.gt e).pG.left _ (D.sym.s jT)) *
        res h₂ ((U.w e).s (fun _ => jT 1, fun _ => jS 1)) =
      res h₃ (pullU (ι[thickObj R I e G]).left _ ((U.w e).s (fun _ => jT 0, fun _ => jS 0))) *
        res h₄ (pullU (fstG I e G).left _ (U.P.sym.s jS)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jS cS (fun k => Set.mem_iInter.1 (h₄ hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jT cT (fun k => Set.mem_iInter.1 (h₁ hy) k)
  have H := (U.w_vals e _ y JG J hJG hJ _ (fun _ => rfl)).2.1 (𝟙 _)
  have o : ((𝟙 (thickObj R I e G))⁻¹).left = (ι[thickObj R I e G]).left := by rw [Hom.inv_def, Category.id_comp]
  have iG : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    (congrArg (fun q => q.left) (map_inv (fstHom I e G _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[G]).left) (Category.id_comp (fstG I e G).left))
  have iB : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ (ι[D.P.A]).left :=
    (congrArg (fun q => q.left) (map_inv (projHom (U.gt e) _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[D.P.A]).left) (Category.id_comp (U.gt e).pG.left))
  have g₀ : JG ((fstG I e G).left ≫ (ι[G]).left) = jS 0 := eG 0
  have g₁ : JG (fstG I e G).left = jS 1 := (congrArg JG (Category.comp_id _).symm).trans (eG 1)
  have b₀ : J ((U.gt e).pG.left ≫ (ι[D.P.A]).left) = jT 0 := eB 0
  have b₁ : J (U.gt e).pG.left = jT 1 := (congrArg J (Category.comp_id _).symm).trans (eB 1)
  rw [iG, iB, o, g₀, b₀, Over.id_left, Category.id_comp, Category.id_comp, g₁, b₁, val_of _ _ _ _ jT eB,
    val_of _ _ _ _ jS eG] at H
  refine (map_mul _ _ _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  exact (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res _ y h₂ hy _)).trans
    (H.trans (congrArg₂ (· * ·) (gm_res_pull _ h₃ hy _) (gm_res_pull _ h₄ hy _)).symm)

theorem w_cub (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → U.P.L.L.ι) (jM : thK → D.P.L.ι)
    (cL : LB.Coh U.P.L.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL)
    (cM : LB.Coh D.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
        ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ≫
          thφ D.P.A (x3 D.P.A) k) jM)
    (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
          ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ⁻¹ᵁ
            (Theta D.P.A D.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G U.P.L.L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jM k) ⊓
          (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL k))) :
      res hB (pullU _ _ (D.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          ((U.w e).s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (U.P.c.t.s jL)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jL cL (fun k => Set.mem_iInter.1 (hG hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 (hB hy) k)
  obtain ⟨h, hh⟩ : ∃ h : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk y)ˣ, ∀ q,
      h q = gw (U.w e) q y (J (q ≫ (U.gt e).pG.left)) (fun _ => JG (q ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  have H := (U.w_vals e T y JG J hJG hJ (fun a => h a.left) (fun _ => hh _)).2.2 (x 0) (x 1) (x 2)
  have P := prod_cub (x 0) (x 1) (x 2) h
  have Q : ∀ k : thK, gm (𝟙 T.left) y V (res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
      ((U.w e).s (fun _ => jM k, fun _ => jL k)))) =
      h ((lift (x 0) (lift (x 1) (x 2))).left ≫ thφ (thickObj R I e G) (x3 _) k) := fun k => by
    have g : JG ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left) = jL k :=
      (congrArg JG (cube_left (fstHom I e G T) x k).symm).trans (eG k)
    have b : J ((psum (thickObj R I e G) x k.down).left ≫ (U.gt e).pG.left) = jM k :=
      (congrArg J (cube_left (projHom (U.gt e) T) x k).symm).trans (eB k)
    refine (gm_res_pull _ (hw k) hy _).trans (Eq.trans ?_ (congrArg h (cube_left (MonoidHom.id _) x k)).symm)
    exact ((hh _).trans (congrArg₂ (fun j l => gw (U.w e) (psum (thickObj R I e G) x k.down).left y j (fun _ => l))
      b g)).symm
  have a := val_of (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t _ y J jM eB
  have b := val_of (L := U.P.L.L) (φ := thφ G (x3 G)) (ε := thε) U.P.c.t _ y JG jL eG
  refine (gm_res_pull _ hB hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
      (congrArg (· ^ thε k) (Q k)))).trans P) (gm_res_pull _ hG hy _))).symm)
  exact a.symm.trans ((cub_alg' H).trans (congrArg₂ (· * ·) rfl b))

theorem exists_match : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G), ∃ U' : UnifPre I D A G, Match U U' :=
  fun _ _ _ _ _ _ _ _ _ U =>
    ⟨{ smooth := U.semi.smooth
       separated := U.semi.separated
       gen := U.gen
       gen_hom := U.gen_hom
       LG := U.P.L
       cubG := U.P.c
       symG := U.P.sym
       symG_gen := U.P.sym_gen
       symG_rig := U.P.sym_rig
       ext := ⟨U.wA, U.wA_gen⟩
       gt := U.gt
       gt_q := U.gt_q
       gt_t := U.gt_t
       w := U.w
       w_gen := U.w_gen
       w_rig := w_rig U
       w_even := w_even U
       w_cub := w_cub U
       w_compat := w_compat U }, ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩⟩

end GlobalTheory.UU.ToChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtCoordCompare

section Refine

variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def Refines (M : LB Y) (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ σ : M.ι → K → L.ι, (∀ i, M.U i ≤ LB.wchart L φ (σ i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : M.ι), r z ∈ M.U i → r z ∈ M.U j →
      gm r z (M.U i ⊓ M.U j) (M.g i j) = trF φ ε r z (σ i) (σ j)

theorem refines_self (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Refines (LB.LinComb L φ ε) L φ ε :=
  ⟨id, fun _ => le_rfl, fun _ r z i j hi hj => gm_linComb L φ ε r z i j hi hj⟩

theorem Refines.linComb {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    (ψ : K' → (Y' ⟶ Y)) (δ : K' → ℤ) :
    Refines (LB.LinComb M ψ δ) L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1) := by
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨fun j p => σ (j p.1) p.2, fun j y hy => Set.mem_iInter.2 fun p => ?_, fun Z r z i j hi hj => ?_⟩
  · exact Set.mem_iInter.1 (le _ (Set.mem_iInter.1 hy p.1)) p.2
  · refine (gm_linComb M ψ δ r z i j hi hj).trans ?_
    rw [trF, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hg Z (r ≫ ψ a) z _ _ (Set.mem_iInter.1 hi a) (Set.mem_iInter.1 hj a), trF, ← Finset.prod_zpow]
    simp only [zpow_mul, Category.assoc]

theorem isGen_one : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

end Refine

section Present

variable {S : Scheme.{0}}


end Present

section Data

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)

end Data

section

variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)

variable {q a p}

theorem gm_gen {N : LB B} {t : LB.Gen N} (ht : t.IsGen) {Z : Scheme.{0}} (r : Z ⟶ B) (z : Z)
    {j j' : N.ι} (h : r z ∈ N.U j) (h' : r z ∈ N.U j') :
    gm r z _ (t.s j) = gm r z _ (N.g j j') * gm r z _ (t.s j') := by
  have hm : r z ∈ N.U j ⊓ N.U j' := ⟨h, h'⟩
  exact (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht j j')).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res r z _ hm _))))

end

theorem gm_res_pull_top {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (f : Y ⟶ X) {V : Y.Opens}
    (hz : r z ∈ V) (h : V ≤ f ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)ˣ) :
    gm r z V (res h (pullU f ⊤ c)) = gm (r ≫ f) z ⊤ c :=
  (gm_res r z h hz _).trans (gm_pull r f z ⊤ trivial c)

section Datum

variable {S : Scheme.{0}}

variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)

attribute [local instance] SplitExt.free SplitExt.finite

end Datum

end GlobalTheory.GtCoordCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.PsiInt

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) :=
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem scal_jK {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (c : R) :
    scal (p ≫ jK R) c = scal p (algebraMap R (FractionRing R) c) := by
  have e := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  unfold scal
  rw [e]
  rfl

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem exists_defect
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (f : ∀ α, SecBT D (𝟙_ _) 1 α) (χ : D.X) (hg : (ga χ).IsGen) (p q : R) :
    ∃ d : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval d (lift (toUnit T) y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J -
        gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val *
          sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq (famφT D (𝟙_ _) χ) (DegPre.famε 1)
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero, MonObj.comp_one]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨d, hd⟩ := exists_sec_relation_defect Y.left D.P.A.left Y.left D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ τ.left
    (f 0) (f χ) (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (ga χ) D.rig) (toUnit Y).left)
    (scal Y.hom p) (scal Y.hom q)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg D.rig_gen) _) hF
  refine ⟨d, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ Y.hom = T.hom := Over.w _
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [τ, comp_lift, MonObj.comp_mul, lift_snd, cT, ← Category.assoc]
    congr 2
    · exact toUnit_unique _ _
    · congr 1
      exact toUnit_unique _ _
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hd _ _ z J hJ, gs_scal, gs_scal Y.hom _ z p, e₁, e₂, val_pull hJ, e₃, val_mul hJ, mul_comm (sval (f 0) _ z J)]
  congr 5

theorem psiRel_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiScal D ga a → PsiRel D (𝟙_ _) f → ∀ (χ : D.X) (p q : R), algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p → ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J = gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val * sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  intro R _ _ D ga a f hS hR χ p q hpq T y z J hJ
  obtain ⟨d, hd⟩ := exists_defect D ga f χ (hS χ).1 p q
  haveI : Flat D.P.A.hom := by
    haveI := D.P.smoothDim
    haveI : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
    infer_instance
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TK R).left := inferInstanceAs (IsAffine (Spec _))
  have hinj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    have e : (toUnit (TK R)).left = jK R := by simp
    rw [e]
    exact jK_appTop_injective R
  have h0 := sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A (𝟙_ _) (TK R) (toUnit _) hinj _ D.P.L D.P.isLB _ _ _ d
    (fun w I hI => by
      have e : toUnit (TK R) ▷ D.P.A = lift (toUnit (TK R ⊗ D.P.A)) (snd _ _) := by
        ext1
        · exact toUnit_unique _ _
        · simp
      have e' : (TK R ⊗ D.P.A).hom = (fst (TK R) D.P.A).left ≫ jK R := (Over.w (fst (TK R) D.P.A)).symm
      have e₁ := hR χ _ (toUnit _) (fst (TK R) D.P.A) (snd _ _) w I hI
      have e₂ := (hS χ).2 _ (fst (TK R) D.P.A) w I hI
      have e₃ : gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom q) * gs (𝟙 _) w ⊤ (scal (fst (TK R) D.P.A).left (a χ).val) =
          gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom p) := by
        rw [← gs_mul _ w ⊤ trivial, e']
        congr 1
        refine (congrArg (· * _) (scal_jK _ q)).trans (Eq.trans ?_ (scal_jK _ p).symm)
        rw [← hpq]
        unfold scal
        rw [map_mul, map_mul]
      rw [e, hd _ _ w I hI, e₁, Units.val_mul, Units.val_mul, e₂, ← e₃]
      ring)
  refine sub_eq_zero.1 ((hd T y z J hJ).symm.trans ?_)
  refine (congrArg (gs _ z _) (h0 _)).trans ((gs_eq _ z _ (hJ.mem _ _) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end GlobalTheory.PsiInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.qkToAk_descends_along_baseChange : GlobalFnsSt → SecBaseChangeSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A) (p' : QkPt D'.toPre F k) (x' : TFK (R := R') F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF φ hD F p.g p'.g → x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) → QkToAkU U'.toUnifPre F k p' x' → QkToAkU U.toUnifPre F k p x := by
  first | exact @GlobalTheory.qkToAk_of_baseChange | exact GlobalTheory.qkToAk_of_baseChange | (intros; apply GlobalTheory.qkToAk_of_baseChange <;> assumption)
end

