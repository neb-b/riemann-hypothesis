module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjective
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

section Corner

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem comp_proj_eq_of_comp_eq_zero {X Y Y₀ Y₁ : PDivGroup p k} (f : X ⟶ Y) (r₀ : Y ⟶ Y₀)
    (j₀ : Y₀ ⟶ Y) (r₁ : Y ⟶ Y₁) (j₁ : Y₁ ⟶ Y) (hY : r₀ ≫ j₀ + r₁ ≫ j₁ = 𝟙 Y)
    (h : f ≫ r₁ = 0) : f ≫ r₀ ≫ j₀ = f := by
  have h' : f ≫ r₁ ≫ j₁ = 0 := by rw [← Category.assoc, h, Limits.zero_comp]
  calc f ≫ r₀ ≫ j₀ = f ≫ r₀ ≫ j₀ + f ≫ r₁ ≫ j₁ := by rw [h', add_zero]
    _ = f ≫ 𝟙 Y := by rw [← hY, Preadditive.comp_add]
    _ = f := Category.comp_id f

theorem proj_comp_eq_of_comp_eq_zero {X X₀ X₁ Y : PDivGroup p k} (f : X ⟶ Y) (π₀ : X ⟶ X₀)
    (i₀ : X₀ ⟶ X) (π₁ : X ⟶ X₁) (i₁ : X₁ ⟶ X) (hX : π₀ ≫ i₀ + π₁ ≫ i₁ = 𝟙 X)
    (h : i₀ ≫ f = 0) : π₁ ≫ i₁ ≫ f = f := by
  have h' : π₀ ≫ i₀ ≫ f = 0 := by rw [h, Limits.comp_zero]
  calc π₁ ≫ i₁ ≫ f = π₀ ≫ i₀ ≫ f + π₁ ≫ i₁ ≫ f := by rw [h', zero_add]
    _ = 𝟙 X ≫ f := by rw [← hX, Preadditive.add_comp, Category.assoc, Category.assoc]
    _ = f := Category.id_comp f

theorem isIsog_corner {G H G' H' : PDivGroup p k} (q : G ⟶ H) (hq : IsIsog q) (i : G' ⟶ G)
    (π : G ⟶ G') (j : H' ⟶ H) (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hjr : j ≫ r = 𝟙 H')
    (hq' : i ≫ q ≫ r ≫ j = i ≫ q) (hg : ∀ g : H ⟶ G, j ≫ g ≫ π ≫ i = j ≫ g) :
    IsIsog (i ≫ q ≫ r) := by
  unfold IsIsog at hq ⊢
  obtain ⟨n, g, h1, h2⟩ := hq
  refine ⟨n, j ≫ g ≫ π, ?_, ?_⟩
  · calc (i ≫ q ≫ r) ≫ j ≫ g ≫ π = (i ≫ q ≫ r ≫ j) ≫ g ≫ π := by
          simp only [Category.assoc]
      _ = i ≫ (q ≫ g) ≫ π := by rw [hq']; simp only [Category.assoc]
      _ = _ := by rw [h1, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hiπ]
  · calc (j ≫ g ≫ π) ≫ i ≫ q ≫ r = (j ≫ g ≫ π ≫ i) ≫ q ≫ r := by
          simp only [Category.assoc]
      _ = j ≫ (g ≫ q) ≫ r := by rw [hg g]; simp only [Category.assoc]
      _ = _ := by rw [h2, Linear.smul_comp, Linear.comp_smul, Category.id_comp, hjr]

theorem omegaMap_corner_surjective {G H G' H' : PDivGroup p k} (q : G ⟶ H)
    (hs : Function.Surjective (omegaMap G H q)) (i : G' ⟶ G) (π : G ⟶ G') (j : H' ⟶ H)
    (r : H ⟶ H') (hiπ : i ≫ π = 𝟙 G') (hq' : i ≫ q ≫ r ≫ j = i ≫ q) :
    Function.Surjective (omegaMap G' H' (i ≫ q ≫ r)) := by
  intro w
  obtain ⟨v, hv⟩ := hs (omegaMap G G' π w)
  refine ⟨omegaMap H' H j v, ?_⟩
  have e1 : omegaMap G' H' (i ≫ q ≫ r) (omegaMap H' H j v) = omegaMap G' H (i ≫ q) v := by
    rw [← LinearMap.comp_apply, ← omegaMap_comp]
    simp only [Category.assoc]
    rw [hq']
  rw [e1, omegaMap_comp, LinearMap.comp_apply, hv, ← LinearMap.comp_apply, ← omegaMap_comp, hiπ,
    omegaMap_id, LinearMap.id_apply]

theorem isIsog_dualHom_of_isIsog {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    IsIsog (dualHom G H f) := by
  unfold IsIsog at hf ⊢
  obtain ⟨n, g, h1, h2⟩ := hf
  refine ⟨n, dualHom H G g, ?_, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]

theorem isIso_of_isIso_dualHom {G H : PDivGroup p k} (f : G ⟶ H) (h : IsIso (dualHom G H f)) :
    IsIso f := by
  obtain ⟨d, hd⟩ := (dualHom_bijective (G := H) (H := G)).2 (inv (dualHom G H f))
  refine ⟨⟨d, ?_, ?_⟩⟩
  · apply (dualHom_bijective (G := G) (H := G)).1
    rw [dualHom_comp, hd, IsIso.inv_hom_id, dualHom_id]
  · apply (dualHom_bijective (G := H) (H := H)).1
    rw [dualHom_comp, hd, IsIso.hom_inv_id, dualHom_id]

theorem isIso_of_isConn_of_omegaMap_surjective [CharP k p] {G H : PDivGroup p k} (f : G ⟶ H)
    (hG : G.IsConn) (hf : IsIsog f) (hs : Function.Surjective (omegaMap G H f)) : IsIso f := by
  have hsurj := _root_.GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective p k G H f hG hs
  apply ((_root_.GlobalTheory.Dieu.isog_basics p k G).2.2.2 H f hf).1
  unfold HasLogDeg
  refine ⟨0, fun n _ => ?_⟩
  rw [pow_zero]
  exact (_root_.GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one k _ _ _).1 (hsurj n)

end Corner

theorem isIso_of_isIsog_of_omegaMap_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q →
    Function.Surjective (omegaMap G H q) →
    Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  intro p _ k _ _ _ G H q hq hs hsd
  obtain ⟨G₀, G₁, i₀, π₀, i₁, π₁, hG₀, hG₁, hi₀, hi₁, hG⟩ := _root_.GlobalTheory.PDivGroup.exists_isConn_isEt_splitting p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, hj₀, hj₁, hH⟩ := _root_.GlobalTheory.PDivGroup.exists_isConn_isEt_splitting p k H
  have z : ∀ {X Y : PDivGroup p k}, X.IsConn → Y.IsEt → (∀ f : X ⟶ Y, f = 0) ∧ ∀ f : Y ⟶ X, f = 0 :=
    fun {X Y} hX hY => _root_.GlobalTheory.PDivGroup.hom_eq_zero_of_isConn_of_isEt p k X Y hX hY

  have c₀ : i₀ ≫ q ≫ r₀ ≫ j₀ = i₀ ≫ q := by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₀ ≫ q) r₀ j₀ r₁ j₁ hH ((z hG₀ hH₁).1 _)
  have c₁ : i₁ ≫ q ≫ r₁ ≫ j₁ = i₁ ≫ q := by
    have hH' : r₁ ≫ j₁ + r₀ ≫ j₀ = 𝟙 H := by rw [add_comm, hH]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (i₁ ≫ q) r₁ j₁ r₀ j₀ hH' ((z hH₀ hG₁).2 _)
  have g₀ : ∀ g : H ⟶ G, j₀ ≫ g ≫ π₀ ≫ i₀ = j₀ ≫ g := fun g => by
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₀ ≫ g) π₀ i₀ π₁ i₁ hG ((z hH₀ hG₁).1 _)
  have g₁ : ∀ g : H ⟶ G, j₁ ≫ g ≫ π₁ ≫ i₁ = j₁ ≫ g := fun g => by
    have hG' : π₁ ≫ i₁ + π₀ ≫ i₀ = 𝟙 G := by rw [add_comm, hG]
    simpa only [Category.assoc] using
      comp_proj_eq_of_comp_eq_zero (j₁ ≫ g) π₁ i₁ π₀ i₀ hG' ((z hG₀ hH₁).2 _)

  have ha : IsIso (i₀ ≫ q ≫ r₀) :=
    isIso_of_isConn_of_omegaMap_surjective _ hG₀ (isIsog_corner q hq i₀ π₀ j₀ r₀ hi₀ hj₀ c₀ g₀)
      (omegaMap_corner_surjective q hs i₀ π₀ j₀ r₀ hi₀ c₀)

  have hb : IsIso (i₁ ≫ q ≫ r₁) := by
    apply isIso_of_isIso_dualHom
    have hdb : dualHom G₁ H₁ (i₁ ≫ q ≫ r₁) =
        dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ := by
      rw [dualHom_comp, dualHom_comp, Category.assoc]
    have hrj : dualHom H H₁ r₁ ≫ dualHom H₁ H j₁ = 𝟙 H₁.dual := by
      rw [← dualHom_comp, hj₁, dualHom_id]
    have hq'd : dualHom H H₁ r₁ ≫ dualHom G H q ≫ dualHom G₁ G i₁ ≫ dualHom G G₁ π₁ =
        dualHom H H₁ r₁ ≫ dualHom G H q := by
      have e : π₁ ≫ i₁ ≫ q ≫ r₁ = q ≫ r₁ :=
        proj_comp_eq_of_comp_eq_zero (q ≫ r₁) π₀ i₀ π₁ i₁ hG
          (by rw [← Category.assoc]; exact (z hG₀ hH₁).1 _)
      have e' := congrArg (dualHom G H₁) e
      simp only [dualHom_comp, Category.assoc] at e'
      exact e'
    have hs' : Function.Surjective (omegaMap H₁.dual G₁.dual (dualHom G₁ H₁ (i₁ ≫ q ≫ r₁))) := by
      rw [hdb]
      exact omegaMap_corner_surjective (dualHom G H q) hsd (dualHom H H₁ r₁) (dualHom H₁ H j₁)
        (dualHom G G₁ π₁) (dualHom G₁ G i₁) hrj hq'd
    exact isIso_of_isConn_of_omegaMap_surjective _ (_root_.GlobalTheory.PDivGroup.dual_isConn_of_isEt p k H₁ hH₁)
      (isIsog_dualHom_of_isIsog _ (isIsog_corner q hq i₁ π₁ j₁ r₁ hi₁ hj₁ c₁ g₁)) hs'

  have hqd : q = π₀ ≫ (i₀ ≫ q ≫ r₀) ≫ j₀ + π₁ ≫ (i₁ ≫ q ≫ r₁) ≫ j₁ := by
    simp only [Category.assoc, c₀, c₁]
    rw [← Category.assoc π₀, ← Category.assoc π₁, ← Preadditive.add_comp, hG, Category.id_comp]
  have hj01 : j₀ ≫ r₁ = 0 := (z hH₀ hH₁).1 _
  have hj10 : j₁ ≫ r₀ = 0 := (z hH₀ hH₁).2 _
  have hi01 : i₀ ≫ π₁ = 0 := (z hG₀ hG₁).1 _
  have hi10 : i₁ ≫ π₀ = 0 := (z hG₀ hG₁).2 _
  generalize i₀ ≫ q ≫ r₀ = a at ha hqd
  generalize i₁ ≫ q ≫ r₁ = b at hb hqd
  subst hqd
  refine ⟨⟨r₀ ≫ inv a ≫ i₀ + r₁ ≫ inv b ≫ i₁, ?_, ?_⟩⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hj₀,
      reassoc_of% hj₁, reassoc_of% hj01, reassoc_of% hj10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.hom_inv_id_assoc]
    exact hG
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, reassoc_of% hi₀,
      reassoc_of% hi₁, reassoc_of% hi01, reassoc_of% hi10, Limits.zero_comp, Limits.comp_zero,
      add_zero, zero_add, IsIso.inv_hom_id_assoc]
    exact hH

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEquivOfSameCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.LatCmp

theorem act_unit {Y : Type} [AddCommGroup Y] (a b : Fin 8) (w : Fin 8 → Y) :
    (fun i => ∑ j, (Matrix.of fun i' j' => if i' = a ∧ j' = b then (1 : ℤ) else 0) i j • w j) = Pi.single a (w b) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem eq_diag {Y Y' : Type} [AddCommGroup Y] [AddCommGroup Y'] (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y'))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b)
    (v : Fin 8 → Y) (a : Fin 8) : θ v a = θ (Pi.single 0 (v a)) 0 := by
  have h1 := h (Matrix.of fun i' j' => if i' = a ∧ j' = a then (1 : ℤ) else 0) v
  rw [act_unit, act_unit] at h1
  have h2 := h (Matrix.of fun i' j' => if i' = a ∧ j' = 0 then (1 : ℤ) else 0) (Pi.single 0 (v a))
  rw [act_unit, act_unit] at h2
  have e1 := congrFun h1 a
  have e2 := congrFun h2 a
  simp only [Pi.single_eq_same] at e1 e2
  rw [← e1, e2]

theorem exists_diag {Y Y' : Type} [AddCommGroup Y] [AddCommGroup Y'] (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y'))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b) :
    ∃ κ : Y ≃ₗ[ℤ] Y', ∀ v : Fin 8 → Y, θ v = fun a => κ (v a) := by
  let κ0 : Y →+ Y' := (Pi.evalAddMonoidHom (fun _ : Fin 8 => Y') 0).comp
      (θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 8 => Y) 0))
  have hθ : ∀ v a, θ v a = κ0 (v a) := fun v a => eq_diag θ h v a
  have hsingle : ∀ y, θ (Pi.single 0 y) = Pi.single 0 (κ0 y) := by
    intro y; funext a; rw [hθ]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  have inj : Function.Injective κ0 := by
    intro y y' hy
    have : θ (Pi.single 0 y) = θ (Pi.single 0 y') := by rw [hsingle, hsingle, hy]
    exact Pi.single_injective 0 (θ.injective this)
  have surj : Function.Surjective κ0 := by
    intro y
    refine ⟨θ.symm (fun _ => y) 0, ?_⟩
    rw [← hθ]; simp
  refine ⟨(AddEquiv.ofBijective κ0 ⟨inj, surj⟩).toIntLinearEquiv, fun v => ?_⟩
  funext a
  exact hθ v a

end GlobalTheory.Poinc.LatCmp

theorem GlobalTheory.Poinc.lattice_equiv_of_same_centre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c c' : CTrait X₁ p z₁) (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (yy' : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c'.T.D.toPre.X)), IsLab X₁ ε₁ c yy → IsLab X₁ ε₁ c' yy' → ∃ κ : c.T.D.toPre.X ≃ₗ[ℤ] c'.T.D.toPre.X, ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (fun u => κ (μ u)) := by
  intro g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hε p _ z₁ c c' yy yy' h h'
  obtain ⟨Y, U₀, EE, FinalForm, q, hov, hee, hq, hpt, hcon, hlift⟩ := _root_.GlobalTheory.Poinc.exists_zhModel_proper_over_setup g n F W Z i X₁ hg hn ho hi he ht hp
  obtain ⟨y, hy⟩ := hlift p z₁ c
  obtain ⟨y', hy'⟩ := hlift p z₁ c'
  obtain ⟨θ, hl, hE⟩ := GlobalTheory.T.exists_labelled_lattice_equiv_of_common_fibre g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hε Y U₀ EE FinalForm q hov hee hq hpt p z₁ (hcon z₁) c c' y y' hy hy' yy yy' h h'
  obtain ⟨κ, hκ⟩ := GlobalTheory.Poinc.LatCmp.exists_diag θ hE
  refine ⟨κ, fun a μ hμ => ?_⟩
  rw [hl a μ hμ, hκ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongOfSmoothInj
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem liftsAlong_of_smooth_inj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → Inj A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ g hA hg U M hU hM hI B _ _ t ht hsq
  have : Smooth U.hom := hU.smooth
  have : LocallyOfFiniteType U.hom := inferInstance
  have hF : FieldChart A M := fieldChart_of_inj _ A hA g hg U M hU hM hI
  have hT : TanLift A M := tanLift_of_fieldChart _ A hA U M hM hI hF
  have hS : SmallLift A M := _root_.GlobalTheory.DualOpen.smallLift_of_tanLift _ A hA U M hM hI hT
  exact _root_.GlobalTheory.DualOpen.liftsAlong_span_singleton R A U M hM hS B t ht hsq

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriods
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem mem_primDR_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  intro A _ g L u hA c p hp
  obtain ⟨n, L', v, M₁, M₂, hAA, h1, h2, h3, hM1, hM2⟩ := _root_.GlobalTheory.CechPer.exists_holUnif_square A g L u hA
  rw [mem_prim_iff]
  have key : ∀ (φ : A ⊗ A ⟶ A) (M : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (_hw : ∀ w, u.ex (M w) = v.ex w ≫ φ)
      (hM : ∀ l : v.Λ, M l ∈ u.Λ),
      IsPer v.ex v.Λ (cmp1 (str (A ⊗ A)) (pullOver (dp0 ℂ) (𝟙 _) φ c)) (fun l ↦ p ⟨M l, hM l⟩) := by
    intro φ M hw hM
    have hm := IsMor.of_over (dp0 ℂ) (φ := φ.left) (s := str A) (s' := str (A ⊗ A))
      (by rw [← Category.assoc, Over.w])
    exact _root_.GlobalTheory.CechPer.Nat.isPer_pull A g L u (A ⊗ A) n L' v φ M hm.w hw hM _ _ _ (comparison_pullback hm c) hp
  have hμ := key μ[A] (M₁ + M₂) h3 (fun l ↦ add_mem (hM1 l) (hM2 l))
  have hf := key (fst A A) M₁ h1 hM1
  have hs := key (snd A A) M₂ h2 hM2
  obtain ⟨hlin, -⟩ := _root_.GlobalTheory.CechPer.periods_linear (A ⊗ A) n L' v
  have hdiff := (hlin _ _ _ _ hμ (hlin _ _ _ _ hf hs).1).2
  have hq : ((fun l : v.Λ ↦ p ⟨(M₁ + M₂) l, add_mem (hM1 l) (hM2 l)⟩) -
      ((fun l : v.Λ ↦ p ⟨M₁ l, hM1 l⟩) + fun l : v.Λ ↦ p ⟨M₂ l, hM2 l⟩)) = 0 := by
    funext l
    rw [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_eq_zero, ← map_add (f := _)]
    rfl
  rw [hq] at hdiff
  have h0 := _root_.GlobalTheory.CechPer.eq_zero_of_isPer_zero (A ⊗ A) n L' v hAA _ hdiff
  rw [← map_add (f := _), ← map_sub] at h0
  exact sub_eq_zero.1 ((_root_.GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian (A ⊗ A) hAA).1 (h0.trans (map_zero _).symm))

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_coeffValuationLossLe_awayPrime : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    change UnitIn K q (((GlobalTheory.FunObj.muBase R.toLevCh j).loc P.1 x : ℂ) *
      ((R.xiH t).loc P.1 x : ℂ))
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · exact unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · exact unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, ite_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickenin
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem primCris_isBC_of_nilThick : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  intro A₀ _ g hA _ D _ _ π κ hκ hπ k
  haveI : Smooth A₀.hom := hA.smooth
  haveI : IsProper A₀.hom := hA.proper
  let P : Over (Sp ℂ) := A₀ ⊗ A₀
  haveI : Smooth P.hom := smooth_tensorObj_hom A₀ A₀
  haveI : IsProper P.hom := by
    change IsProper (A₀ ⊗ A₀).hom
    rw [Over.tensorObj_hom]; infer_instance
  have m2 : IsMor (dp0 ℂ) (P.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) (𝟙 P.left) :=
    ⟨k.dp, by rw [Category.assoc, ← k.base]; simp⟩
  have key : ∀ (f : P ⟶ A₀) (x : FirstDeRham (A₀.hom ≫ 𝟙 _)),
      pullOver κ (spMap π) f (k.isMor.pull1 x) = m2.pull1 (pullOver (dp0 ℂ) (𝟙 _) f x) := by
    intro f x
    have h'' : IsMor (dp0 ℂ) (A₀.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) f.left :=
      ⟨k.dp, by rw [← Category.assoc, Over.w f, Category.assoc, ← k.base]; simp⟩
    exact (IsMor.pullback1_comp k.isMor
        (IsMor.of_over κ (φ := f.left) (by rw [← Category.assoc, Over.w])) h'' (fun _ ↦ rfl)
        (by simp) x).trans
      (IsMor.pullback1_comp (IsMor.of_over (dp0 ℂ) (φ := f.left) (by rw [← Category.assoc, Over.w]))
        m2 h'' (fun _ ↦ rfl) (by simp) x).symm
  have hM : Function.Bijective (liftSemi k.isMor.pull1) :=
    _root_.GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 ℂ D π κ hκ hπ A₀.left (A₀.hom ≫ 𝟙 _) (A₀.hom ≫ spMap π) (Over.Hom.left (𝟙 A₀))
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) (by simp) k.isMor
  have hN : Function.Bijective (liftSemi m2.pull1) :=
    _root_.GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 ℂ D π κ hκ hπ P.left (P.hom ≫ 𝟙 _) (P.hom ≫ spMap π) (𝟙 P.left)
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) rfl m2
  have hZ : Function.Bijective (liftSemi k.pull) := by
    refine GlobalTheory.FlatKerLarge.liftSemi_bijective_of_exact_large ℂ D _ _ _ _ _ _ (prim (dp0 ℂ) (𝟙 _) A₀).subtype
      (pullOver (dp0 ℂ) (𝟙 _) μ[A₀] - pullOver (dp0 ℂ) (𝟙 _) (fst A₀ A₀) - pullOver (dp0 ℂ) (𝟙 _) (snd A₀ A₀))
      (prim κ (spMap π) A₀).subtype
      (pullOver κ (spMap π) μ[A₀] - pullOver κ (spMap π) (fst A₀ A₀) - pullOver κ (spMap π) (snd A₀ A₀))
      k.pull k.isMor.pull1 m2.pull1 (Submodule.injective_subtype _) ?_ (Submodule.injective_subtype _) ?_
      (fun _ ↦ rfl) ?_ hM hN.1
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro x
      simp only [LinearMap.sub_apply, map_sub, key]
  refine ⟨hZ, eq_top_iff.2 fun y _ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hZ.2 y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)

end GlobalTheory
end

