module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadingBlockLowerEntriesToBlockCoords
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0755

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixNorm

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (s : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem gs_npow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem one_comp_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hφ (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem stalkMap_gm_pow {Z Y : Scheme.{0}} (t : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : t z ∈ V) (a : Γ(Y, V)ˣ) (n : ℕ) :
    (t.stalkMap z).hom ((gm (𝟙 Y) (t z) V a) ^ n).val = gs t z V a.val ^ n := by
  rw [Units.val_pow_eq_pow_val, ← gs_unit (𝟙 Y) (t z) V h, map_pow, ← gs_stalkMap t z V h]

theorem norm_at_zero : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c u hcov hA hB hT hN hrel p
  obtain ⟨gA, gB, hΦ, -⟩ := hT
  haveI : IsMonHom Φ' := hΦ
  have e₀ : zeroPt A' ≫ A'.hom = 𝟙 _ := by simp [zeroPt]
  have eΦ : zeroPt A' ≫ Φ'.left = zeroPt B' := by rw [zeroPt, zeroPt, ← Over.comp_left, IsMonHom.one_hom]
  have eA' : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by
    rw [← Category.assoc, zeroPt, one_comp_of_isGrpPullback gA, Category.assoc]; rfl
  have eB' : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by
    rw [← Category.assoc, eΦ, ← Category.assoc, zeroPt, one_comp_of_isGrpPullback gB, Category.assoc]; rfl
  refine fn_ext fun z hz => ?_

  have hz0 := hz
  obtain ⟨⟨hzU', hzA'⟩, hzB'⟩ := hz
  have hzU : zeroPt A' z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := hzU'
  have hzA : t z ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) := hzA'
  have hzB : t z ∈ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := hzB'
  have pA : eSec A (t z) ∈ L.U (p.2 0) := Set.mem_iInter.1 hzA PUnit.unit
  have pB : eSec B (t z) ∈ M.U (p.1 0) := Set.mem_iInter.1 hzB PUnit.unit
  have mA : (eSec A ≫ θ A) (t z) ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) A).left ((eSec A ≫ θ A) (t z)) ∈ L.U (p.2 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pA
  have mB : (eSec B ≫ θ B) (t z) ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) B).left ((eSec B ≫ θ B) (t z)) ∈ M.U (p.1 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pB
  have sB : ∀ j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((Φ'.left ≫ (φB' ≫ θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs t z ⊤ (βB j) * gs t z (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)) (eB.s (fun _ => p.1 0)).val ^ k := by
    intro j
    have v := hB j (t z) p.1 mB
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eB']
    erw [gs_comp t _ z _ mB]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzB, ← gs_stalkMap t z ⊤ trivial]
  have sA : ∀ i, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    intro i
    have v := hA i (t z) p.2 mA
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eA']
    erw [gs_comp t _ z _ mA]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzA, ← gs_stalkMap t z ⊤ trivial]
  have sC : ∀ i j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      ((A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom (c i j)) =
        gs (𝟙 _) z ⊤ (c i j) := by
    intro i j
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [e₀]
  have gt : ∀ x : Γ(Sp Rg, ⊤), gs t z ⊤ x = gs (𝟙 _) z ⊤ (t.appTop x) := by
    intro x
    have e := gs_pull (𝟙 (Sp R)) t z ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have nN : ∀ j, ∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i) = gs t z ⊤ (βB j) := by
    intro j
    rw [gt, hN j, gs_finsum _ z ⊤ trivial]
    exact Finset.sum_congr rfl fun i _ => by rw [gt, gs_mul _ z ⊤ trivial]
  have hcz : (eSec B ≫ θ B) (t z) ∈ (⨆ j, nonzeroLocus (bB j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hcz
  have hu := (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) (eSec B ≫ θ B) (t z) mB).1 hj
  erw [hB j (t z) p.1 mB] at hu
  have hβ : IsUnit (gs t z ⊤ (βB j)) := by
    rw [gs_stalkMap t z ⊤ trivial]
    exact (isUnit_of_mul_isUnit_left hu).map _
  have E := congrArg (gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)) (hrel j p)
  rw [sB j, gs_mul _ _ _ hzU, gs_finsum _ _ _ hzU] at E
  simp only [gs_mul _ _ _ hzU, sC, sA] at E
  have hs : ∑ i, gs (𝟙 _) z ⊤ (c i j) * (gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k) =
      (∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i)) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  rw [hs, nN j] at E
  rw [gs_mul _ z _ hz0, gs_npow _ z _ hz0, gs_npow _ z _ hz0]
  erw [gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0]
  simp only [Category.id_comp]
  exact hβ.mul_left_cancel (by rw [E]; ring)

end GlobalTheory.HomFixNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatSumThIndRegroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory

theorem latSum_tower_reps (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D G C B : Submodule (𝓞 E) W) (hBC : B ≤ C) (hCG : C ≤ G) (hGD : G ≤ D)
    (hfin : Finite (↥D ⧸ B.comap D.subtype)) :
    ∃ R : Finset W, (∀ x ∈ R, x ∈ G) ∧ R.card = Nat.card (↥G ⧸ C.comap G.subtype) ∧
      ∀ f : W → ℂ, (∀ x, f x ≠ 0 → x ∈ G) → (∀ x y, x - y ∈ B → f x = f y) →
        latSum D B f = ∑ x ∈ R, latSum C B fun y => f (x + y) := by
  classical
  have key : ∀ (P Q : Submodule (𝓞 E) W) (t u : ↥P),
      (Submodule.Quotient.mk t : ↥P ⧸ Q.comap P.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ Q := by
    intro P Q t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  set r : (↥G ⧸ C.comap G.subtype) → ↥G :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap G.subtype)) with hr
  set s : (↥C ⧸ B.comap C.subtype) → ↥C :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap C.subtype)) with hs
  set t : (↥D ⧸ B.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap D.subtype)) with ht
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have ht' : ∀ z, Submodule.Quotient.mk (t z) = z := fun z => Function.surjInv_eq _ z
  have hmem : ∀ p : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype), (r p.1 : W) + s p.2 ∈ D :=
    fun p => hGD (G.add_mem (r p.1).2 (hCG (s p.2).2))
  let φ : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype) → (↥D ⧸ B.comap D.subtype) :=
    fun p => Submodule.Quotient.mk ⟨_, hmem p⟩
  have hinj : Function.Injective φ := by
    rintro ⟨x, j⟩ ⟨x', j'⟩ h
    have h1 : (r x : W) + s j - (r x' + s j') ∈ B := (key D B _ _).1 h
    have h2 : x = x' := by
      rw [← hr' x, ← hr' x', key]
      have : (r x : W) - r x' = ((r x : W) + s j - (r x' + s j')) + (s j' - s j) := by abel
      rw [this]
      exact C.add_mem (hBC h1) (C.sub_mem (s j').2 (s j).2)
    subst h2
    have h3 : j = j' := by
      rw [← hs' j, ← hs' j', key]
      simpa using h1
    rw [h3]
  haveI hprod : Finite ((↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype)) := Finite.of_injective φ hinj
  haveI : Finite (↥G ⧸ C.comap G.subtype) := Finite.prod_left (↥C ⧸ B.comap C.subtype)
  haveI : Finite (↥C ⧸ B.comap C.subtype) := Finite.prod_right (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥C ⧸ B.comap C.subtype)
  letI := Fintype.ofFinite (↥D ⧸ B.comap D.subtype)
  have hrinj : Function.Injective fun z => (r z : W) := by
    intro z w h
    rw [← hr' z, ← hr' w, Subtype.ext h]
  refine ⟨Finset.univ.image fun z => (r z : W), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
    exact (r z).2
  · rw [Finset.card_image_of_injective _ hrinj, Nat.card_eq_fintype_card, Finset.card_univ]
  · intro f hf0 hf
    rw [Finset.sum_image fun _ _ _ _ h => hrinj h]
    unfold latSum
    simp only [finsum_eq_sum_of_fintype]
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_of_injective φ hinj _ _ ?_ ?_
    · intro z hz
      by_contra hne
      have hG : (t z : W) ∈ G := hf0 _ hne
      apply hz
      have h1 : (r (Submodule.Quotient.mk ⟨_, hG⟩) : W) - t z ∈ C := (key G C _ ⟨_, hG⟩).1 (hr' _)
      have h1' : (t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩) ∈ C := by
        simpa using C.neg_mem h1
      have h2 : (s (Submodule.Quotient.mk ⟨_, h1'⟩) : W) - ((t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩)) ∈ B :=
        (key C B _ ⟨_, h1'⟩).1 (hs' _)
      refine ⟨(Submodule.Quotient.mk ⟨_, hG⟩, Submodule.Quotient.mk ⟨_, h1'⟩), ?_⟩
      refine Eq.trans ?_ (ht' z)
      refine (key D B _ _).2 ?_
      convert h2 using 1
      simp only
      abel
    · intro p
      apply hf
      exact (key D B ⟨_, hmem p⟩ _).1 (ht' _).symm

theorem thInd_congr_of_sub_mem {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x y : HomE X.E a b)
    (h : x - y ∈ mulLat c (homAt S L L')) : A.thInd S L L' c x = A.thInd S L L' c y := by
  have h1 : A.IsLift S L L' c x = A.IsLift S L L' c y := by
    funext s
    unfold Amb.IsLift
    congr 1
    apply propext
    constructor
    · intro hs
      simpa using Submodule.add_mem _ hs h
    · intro hs
      simpa using Submodule.sub_mem _ hs h
  unfold Amb.thInd Amb.liftW
  rw [h1]

theorem latSum_thInd_regroup : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c c' : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndAdd a b S (cA * (c * c')) → IsSdLat L → IsSdLat L' → 0 < cA → 0 < c → 0 < c' → (∀ x, Ξ x ≠ 0 → x ∈ homAt S L L') → (∀ x, ∀ y ∈ mulLat c (homAt S L L'), Ξ (x + y) = Ξ x) → ∃ R : Finset (HomE X.E a b), R.card ≤ c ^ (Module.finrank ℚ X.E * a * b) ∧ ∀ z, latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) (fun x => Ξ x * A.thInd S L L' (c * c') x z) = ∑ x ∈ R, Ξ x * A.thInd S L L' c x z := by
  intro X A a b S L L' cA c c' Ξ hadd hL hL' hcA hc hc' hsupp hinv
  have hdiv : ∀ (n : ℕ) x, x ∈ homAt S L L' → x ∈ divLat n (homAt S L L') := fun n x hx =>
    Submodule.smul_mem (homAt S L L') (n : 𝓞 X.E) hx
  have hone : ∀ x, x ∈ divLat 1 (homAt S L L') → x ∈ homAt S L L' := fun x hx => by
    simpa [divLat] using hx
  have hBC : mulLat (c * c') (homAt S L L') ≤ mulLat c (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(c' : 𝓞 X.E) • x, Submodule.smul_mem _ _ hx, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_smul]
  have hCG : mulLat c (homAt S L L') ≤ divLat 1 (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiv 1 _ (Submodule.smul_mem (homAt S L L') (c : 𝓞 X.E) hx)
  have hfin := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' cA (c * c') hL.1 hL'.1 hcA (Nat.mul_pos hc hc')).1
  have hcard := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' 1 c hL.1 hL'.1 Nat.one_pos hc).2
  obtain ⟨R, hR, hRc, hsum⟩ := latSum_tower_reps X.E (HomE X.E a b) (divLat cA (homAt S L L'))
    (divLat 1 (homAt S L L')) (mulLat c (homAt S L L')) (mulLat (c * c') (homAt S L L')) hBC hCG
    (fun x hx => hdiv cA x (hone x hx)) hfin
  refine ⟨R, by rw [hRc]; simpa using hcard, fun z => ?_⟩
  rw [hsum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [hadd L L' c c' x hc hc' ⟨hL, hL', Nat.mul_pos hc hc', Dvd.intro_left _ rfl, hdiv _ x (hone x (hR x hx))⟩ z]
    unfold latSum
    rw [mul_finsum]
    exact finsum_congr fun q => by beta_reduce; rw [hinv x _ (Subtype.property _)]
  · intro x hx
    exact hdiv 1 x (hsupp x (left_ne_zero_of_mul hx))
  · intro x y hxy
    rw [thInd_congr_of_sub_mem A S L L' (c * c') x y hxy]
    have := hinv y _ (hBC hxy)
    rw [add_sub_cancel] at this
    rw [this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearNormalisationClosedSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem factors_quot_iff {P : Type} [CommRing P] (I : Ideal P) (T : Scheme.{0}) (g : T ⟶ Sp P) :
    (∃ w : T ⟶ Sp (P ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ x ∈ I, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ x hx
    have e : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of P)).inv x) =
        (Scheme.ΓSpecIso (CommRingCat.of (P ⧸ I))).inv (Ideal.Quotient.mk I x) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e,
      Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of P ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of P)).inv ≫ g.appTop
    let ψ : CommRingCat.of (P ⧸ I) ⟶ Γ(T, ⊤) :=
      CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom (fun x hx => h x hx))
    refine ⟨T.toSpecΓ ≫ Spec.map ψ, ?_⟩
    have e : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ ψ = φ := by ext x; rfl
    rw [Category.assoc, ← Spec.map_comp, e]
    simp only [φ, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]

def normEq {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (j : Fin mB) : MvPolynomial (Fin (mA * mB)) Rg :=
  MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (β j)) -
    ∑ i, MvPolynomial.X (finProdFinEquiv (i, j)) *
      MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom (α i))

theorem appTop_affπ {Rg : Type} [CommRing Rg] {N : ℕ} (a : Γ(Sp Rg, ⊤)) :
    (affπ Rg N).appTop a = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv
      (MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of Rg)).hom a)) := by
  conv_lhs => rw [← (Scheme.ΓSpecIso (CommRingCat.of Rg)).hom_inv_id_apply a]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl

theorem normal_iff {Rg : Type} [CommRing Rg] {mA mB : ℕ} (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔
      ∀ j, g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (normEq α β j)) = 0 := by
  refine forall_congr' fun j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [normEq, map_sub, map_sub, sub_eq_zero, map_sum, map_sum]
  simp only [map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_affπ, matOf, coord]

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem normal_closed : ∀ (Rg : Type) [CommRing Rg] (mA mB : ℕ) (α : Fin mA → Γ(Sp Rg, ⊤)) (β : Fin mB → Γ(Sp Rg, ⊤)), ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), (GlobalTheory.HomFixUniv.Normal (g ≫ affπ Rg (mA * mB)) (matOf g) α β ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  intro Rg _ mA mB α β
  let I : Ideal (MvPolynomial (Fin (mA * mB)) Rg) := Ideal.span (Set.range (normEq α β))
  refine ⟨Sp (MvPolynomial (Fin (mA * mB)) Rg ⧸ I), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, fun T g => ?_⟩
  rw [factors_quot_iff, normal_iff]
  let φ : MvPolynomial (Fin (mA * mB)) Rg →+* Γ(T, ⊤) :=
    g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv.hom
  change (∀ j, φ (normEq α β j) = 0) ↔ ∀ x ∈ I, φ x = 0
  constructor
  · intro h x hx
    have hle : I ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h j
    exact hle hx
  · intro h j
    exact h _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomain
section
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

noncomputable section

theorem lintegral_exp_muF_eq_setLIntegral_Om (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 =
      ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  have hT : Measurable (GlobalTheory.UpCoordCompare.toEntries X) :=
    (GlobalTheory.UpCoordCompare.contDiff_toEntries X).continuous.measurable
  have hf : Measurable fun z => ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((GlobalTheory.PoleDbar.measurable_rhF X x0.1).const_mul s).neg)
  have hd : Measurable fun z => ENNReal.ofReal (density X x0 z) := by
    have e : (fun z => ENNReal.ofReal (density X x0 z)) =
        (fun z => ENNReal.ofReal (densF X x0.1 z)) ∘ GlobalTheory.UpCoordCompare.toEntries X := by
      funext z
      simp only [Function.comp_apply, GlobalTheory.UpCoordCompare.densF_toEntries]
    rw [e]
    exact (OntoC.measurable_densF X x0.1).comp hT
  have hOm : MeasurableSet (Om X) := by
    have : Om X = GlobalTheory.UpCoordCompare.toEntries X ⁻¹' OmF X x0.1 := by
      ext z; exact (GlobalTheory.UpCoordCompare.toEntries_mem_OmF_iff X x0 z).symm
    rw [this]
    exact hT (ExF.isOpen_OmF X x0.1).measurableSet
  rw [← GlobalTheory.UpCoordCompare.map_mu X x0, lintegral_map hf hT, mu,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hOm fun z hz => ?_
  simp only [Pi.mul_apply, GlobalTheory.UpCoordCompare.rhF_toEntries X x0 hz]

end

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modF_finiteIdeleUpToExtension : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  first | exact @GlobalTheory.UpIdeleMod.modF_upIdele | exact GlobalTheory.UpIdeleMod.modF_upIdele | (intros; apply GlobalTheory.UpIdeleMod.modF_upIdele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormToLMapPInfLe
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.GLCuspNorm


open scoped Classical in
theorem norm_pInf_le (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Ad E) :
    ‖pInf E x‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace E x.1‖ := by
  classical
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
  have h1 : ‖pInf E x w‖ = ‖x.1 w‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))) (x.1 w)
  rw [h1, ← GroundTheory.Automorphic.CuspidalSpectrum.normAtPlace_ringEquiv_mixedSpace, mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w _) (Finset.mem_univ w)

theorem norm_toL_map_pInf_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ c : ℝ, 0 ≤ c ∧
    ∀ M : Matrix (Fin a) (Fin a) (Ad E),
      ‖toL (M.map (pInf E))‖ ≤ c * ‖GroundTheory.Automorphic.CuspidalSpectrum.archMat E a M‖ := by
  intro E _ _ _ a
  refine ⟨1, zero_le_one, fun M => ?_⟩
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  refine (norm_pInf_le E (M i j)).trans ?_
  rw [← GroundTheory.Automorphic.CuspidalSpectrum.archMat_apply]
  exact GroundTheory.Automorphic.CuspidalSpectrum.norm_entry_le_norm_archMatrix _ i j

end GlobalTheory.GLCuspNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnitStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  first | (exact @GlobalTheory.VertUnits.units_eq_const_mul_unit) | (exact GlobalTheory.VertUnits.units_eq_const_mul_unit) | (intros; apply GlobalTheory.VertUnits.units_eq_const_mul_unit <;> assumption)
end

