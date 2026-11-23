module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteFibrePoints
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbTorsionFinite

theorem finite_fibre_points {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    [IsFinite f.left] (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y) :
    Finite {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X // x ≫ f = y} := by
  have hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite :=
    f.left.finite_preimage_singleton _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by
      have h := congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2
      exact h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_
  intro a b hab
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1)
    (congrArg Subtype.val hab)

theorem finite_torsion : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B // x ^ n = 1} := by
  intro K _ _ B _ hB n hn
  have := _root_.GlobalTheory.MulFiniteAny.isFinite_mulA K B hB n hn
  have : IsProper B.hom := hB.proper
  have := finite_fibre_points (mulA B n) 1
  refine Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulA B n = 1) fun x => ?_)
  have : x ≫ mulA B n = x ^ n := by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  rw [this]

end GlobalTheory.AbTorsionFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneLeFinrankSecM
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.PolSection

open GlobalTheory.SecGrowth

variable {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X)

theorem wchart_le_tw (N t : ℤ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => π) j ≤
      (tw (L.pull π) (pw (L.pull π) N) t).U ((fun _ => j 0), (fun _ => j 0)) :=
  le_inf (wchart_le_unit L π j) (wchart_le_unit L π j)

theorem lcg_tw (N t : ℤ) (j j' : Fin 1 → L.ι) :
    LB.lcg L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t) j j' =
      res (inf_le_inf (wchart_le_tw L π N t j) (wchart_le_tw L π N t j'))
        ((tw (L.pull π) (pw (L.pull π) N) t).g ((fun _ => j 0), (fun _ => j 0))
          ((fun _ => j' 0), (fun _ => j' 0))) := by
  have h := SecOn.res_tw_g (M := L.pull π) (H := pw (L.pull π) N) t (fun _ => j 0) (fun _ => j' 0)
    (fun _ => j 0) (fun _ => j' 0) (inf_le_inf (wchart_le_tw L π N t j) (wchart_le_tw L π N t j'))
    (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
    (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
  refine Eq.trans ?_ h.symm
  change _ = res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) (fun _ => j 0) (fun _ => j' 0)) *
      res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) (fun _ => j 0) (fun _ => j' 0) ^ N) ^ t
  rw [map_zpow, ← zpow_mul, ← zpow_one_add, LB.lcg_pull, LB.res_res, LB.lcg, Fintype.prod_unique]
  rfl

theorem exists_sec_ne_zero [IsIntegral Y] (hL : L.IsLB) (N t : ℤ)
    (σ : LB.Sec (tw (L.pull π) (pw (L.pull π) N) t)) (i : (tw (L.pull π) (pw (L.pull π) N) t).ι)
    (hi : σ.f i ≠ 0) :
    ∃ τ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)), τ.f ≠ 0 := by
  refine ⟨transSec (M := tw (L.pull π) (pw (L.pull π) N) t)
    (M' := LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t))
    (fun j => ((fun _ => j 0), (fun _ => j 0))) (wchart_le_tw L π N t) (lcg_tw L π N t) σ, fun h => hi ?_⟩
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hc := (LB.isLB_linComb hL (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)).cover
  have hy : y ∈ ⨆ j, (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)).U j := by
    rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  haveI : Nonempty (LB.wchart L (fun _ : Fin 1 => π) j) := ⟨⟨y, hj⟩⟩
  exact sec_eq_zero σ (wchart_le_tw L π N t j) (congrFun h j) i

theorem exists_sq_eq (K : Type) [Field K] (N : ℕ) (hN : 1 ≤ N) (t₀ : ℤ) :
    ∃ (n : ℕ) (t : ℤ), (n : K) ≠ 0 ∧ t₀ ≤ t ∧ ((n ^ 2 * 1 : ℕ) : ℤ) = 1 + N * t := by
  have key : ∃ a : ℕ, t₀ ≤ a ∧ ((1 + N * a : ℕ) : K) ≠ 0 := by
    obtain ⟨p, hp⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K p with h | h
    · refine ⟨p * t₀.toNat, ?_, ?_⟩
      · have h1 : t₀.toNat ≤ p * t₀.toNat := Nat.le_mul_of_pos_left _ h.pos
        have h2 := Int.self_le_toNat t₀
        omega
      · push_cast
        rw [CharP.cast_eq_zero K p]
        simp
    · subst h
      haveI := CharP.charP_to_charZero K
      exact ⟨t₀.toNat, Int.self_le_toNat t₀, Nat.cast_ne_zero.2 (by omega)⟩
  obtain ⟨a, ha, hK⟩ := key
  refine ⟨1 + N * a, 2 * a + N * a ^ 2, hK, ?_, ?_⟩
  · have h1 : (0 : ℤ) ≤ a := Int.natCast_nonneg a
    have h2 : (0 : ℤ) ≤ N * a ^ 2 := by positivity
    omega
  · push_cast
    ring

theorem one_le_finrank_secM :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), 1 ≤ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) := by
  intro K _ _ P
  let T : Over (Spec (CommRingCat.of K)) := baseOver (Spec (CommRingCat.of K))
  let π : (T ⊗ P.A).left ⟶ P.A.left := (snd T P.A).left
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst T P.A).left
  have hpb : IsPullback π f P.A.hom (𝟙 _) := (IsPullback.of_hasPullback T.hom P.A.hom).flip
  obtain ⟨N, hN, m, s, hH, hs⟩ :=
    GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1 _ P K (𝟙 _) _ π f hpb
  have hgi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom
    P.isAb.smooth P.isAb.geomConnected
  haveI : IsIntegral (T ⊗ P.A).left := GeometricallyIntegral.geometrically_isIntegral _ _ _ hpb
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.AbLaw.exists_sec_tw_ne_zero K _ f _ m s (P.L.pull π) hH (LB.isLB_pull P.isLB π) hs
  obtain ⟨n, t, hn, ht, hnt⟩ := exists_sq_eq K N hN t₀
  obtain ⟨σ, i, hi⟩ := ht₀ t ht
  obtain ⟨τ, hτ⟩ := exists_sec_ne_zero P.L π P.isLB N t σ i hi
  have hbig : Nontrivial (SecM P.A P.L (1 + N * t) T) :=
    ⟨SecM.ofSec P.A τ, 0, fun h => hτ (congrArg Subtype.val h)⟩
  rw [← hnt] at hbig
  obtain ⟨e⟩ := (GlobalTheory.AbLaw.FromCube.all_of_cubeGen CubeAssembly.cube_gen).2.2.2.2.2.2.2.2.2 K P n 1 hn le_rfl
  have hone : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) T) := by
    by_contra h
    haveI := not_nontrivial_iff_subsingleton.1 h
    exact not_subsingleton _ e.toEquiv.subsingleton
  have hfin := (CubeAssembly.sections_growth K P).1 1
  letI : Field Γ(T.left, ⊤) :=
    (isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K))).toField
  exact Module.finrank_pos (R := Γ(T.left, ⊤)) (M := SecM P.A P.L ((1 : ℕ) : ℤ) T)

end GlobalTheory.PolSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TranslateDivAdditive
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.TranslateAdditive

noncomputable def chartPullTw {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ε : K → ℤ)
    {φ₀ φ₁ φ₂ : K → (Y ⟶ X)} {A₀ A₁ A₂ : LB Y} (a₀ : ChartPull A₀ (LB.LinComb L φ₀ ε) (𝟙 Y))
    (a₁ : ChartPull A₁ (LB.LinComb L φ₁ ε) (𝟙 Y)) (a₂ : ChartPull A₂ (LB.LinComb L φ₂ ε) (𝟙 Y)) :
    ChartPull (LB.div (tw A₁ A₂ 1) A₀)
      (LB.LinComb L (Sum.elim φ₁ (Sum.elim φ₂ φ₀)) (Sum.elim ε (Sum.elim ε fun k => - ε k))) (𝟙 Y) :=
  have le : ∀ p : (A₁.ι × A₂.ι) × A₀.ι, (LB.div (tw A₁ A₂ 1) A₀).U p ≤
      LB.wchart L (Sum.elim φ₁ (Sum.elim φ₂ φ₀))
        (Sum.elim (a₁.idx p.1.1) (Sum.elim (a₂.idx p.1.2) (a₀.idx p.2))) := fun p y hy =>
    Set.mem_iInter.2 (by
      rintro (k | k | k)
      · exact Set.mem_iInter.1 (a₁.le _ hy.1.1) k
      · exact Set.mem_iInter.1 (a₂.le _ hy.1.2) k
      · exact Set.mem_iInter.1 (a₀.le _ hy.2) k)
  { idx := fun p => Sum.elim (a₁.idx p.1.1) (Sum.elim (a₂.idx p.1.2) (a₀.idx p.2))
    le := le
    g := fun y p q hp hq => by
      refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm
      have e₀ := (a₀.g y p.2 q.2 hp.2 hq.2).trans (gm_linComb L φ₀ ε (𝟙 Y) y _ _ (a₀.le _ hp.2) (a₀.le _ hq.2))
      have e₁ := (a₁.g y p.1.1 q.1.1 hp.1.1 hq.1.1).trans
        (gm_linComb L φ₁ ε (𝟙 Y) y _ _ (a₁.le _ hp.1.1) (a₁.le _ hq.1.1))
      have e₂ := (a₂.g y p.1.2 q.1.2 hp.1.2 hq.1.2).trans
        (gm_linComb L φ₂ ε (𝟙 Y) y _ _ (a₂.le _ hp.1.2) (a₂.le _ hq.1.2))
      have e₃ : gm (𝟙 Y) y _ ((pw A₂ (-1)).g p.1.2 q.1.2) = (gm (𝟙 Y) y _ (A₂.g p.1.2 q.1.2)) ^ (-1 : ℤ) :=
        map_zpow _ _ _
      have e₄ := (gm_div (pw A₂ (-1)) A₁ (𝟙 Y) y p.1 q.1 ⟨hp.1, hq.1⟩).trans
        (congrArg₂ (fun a b => a * b⁻¹) e₁ (e₃.trans (congrArg (· ^ (-1 : ℤ)) e₂)))
      refine ((gm_div A₀ (tw A₁ A₂ 1) (𝟙 Y) y p q ⟨hp, hq⟩).trans
        (congrArg₂ (fun a b => a * b⁻¹) e₄ e₀)).trans ?_
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine (_root_.mul_assoc _ _ _).trans (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ ?_))
      · rw [zpow_neg_one, inv_inv]; rfl
      · rw [← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun k _ => (zpow_neg _ _).symm }

theorem exists_gen_additive {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) {T : Over S} (a b c : T ⟶ G) (i : Fin 2 → L.ι)
    (hi : ∀ k (y : T.left), (![a.left, (1 : T ⟶ G).left] k) y ∈ L.U (i k)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
      (Sum.elim ![(a * b).left, b.left] (Sum.elim ![(a * c).left, c.left] ![(a * b * c).left, (b * c).left]))
      (Sum.elim ![1, -1] (Sum.elim ![1, -1] fun k => - (![1, -1] : Fin 2 → ℤ) k))), u.IsGen := by
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hL _ ![-1, 1] i hi
  obtain ⟨u, hu, -⟩ := exists_gen hL
    (φ' := Sum.elim ![(a * b).left, b.left] (Sum.elim ![(a * c).left, c.left] ![(a * b * c).left, (b * c).left]))
    (ε' := fun k => - Sum.elim ![1, -1] (Sum.elim ![1, -1] fun k => - (![1, -1] : Fin 2 → ℤ) k) k) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub a b c h))).trans ?_
      apply Additive.ofMul.injective
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ w (LB.pullGen L (thφ G (x3 G)) thε t (lift a (lift b c)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ ht _))
  obtain ⟨v, hv, -⟩ := exists_gen hL (φ' := _) (ε' := _) (fun U _ h => Finset.prod_congr rfl fun k _ => by
    rw [neg_neg]) (LB.invGen L _ _ u) (DVR.invGen_isGen _ _ _ _ hu)
  exact ⟨v, hv⟩

theorem exists_iso_of_cube {S : Scheme.{0}} [Unique S] {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) (x : 𝟙_ (Over S) ⟶ G) :
    ∃ w : LB.Iso
      ((LB.LinComb L (K := Fin 2) ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] ![1, -1]).pull μ[G].left)
      (tw ((LB.LinComb L (K := Fin 2) ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] ![1, -1]).pull
          (fst G G).left)
        ((LB.LinComb L (K := Fin 2) ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] ![1, -1]).pull
          (snd G G).left) 1), w.IsGen := by
  let χ : Fin 2 → ((𝟙_ (Over S)).left ⟶ G.left) := ![x.left, (1 : 𝟙_ (Over S) ⟶ G).left]
  choose i hi using fun k => exists_chart hL (χ k (default : S))
  have e : ∀ k, (![(toUnit (G ⊗ G) ≫ x).left, (1 : G ⊗ G ⟶ G).left] k) = (toUnit (G ⊗ G)).left ≫ χ k := by
    intro k
    fin_cases k
    · rfl
    · show _ = (toUnit (G ⊗ G) ≫ (1 : 𝟙_ (Over S) ⟶ G)).left
      rw [MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := exists_gen_additive hL t ht (toUnit (G ⊗ G) ≫ x) (fst G G) (snd G G) i (fun k z => by
    rw [e k]
    have h : (toUnit (G ⊗ G)).left z = (default : S) := Subsingleton.elim (α := S) _ _
    exact (congrArg (fun s => χ k s ∈ L.U (i k)) h).mpr (hi k))
  have key : ∀ b : G ⊗ G ⟶ G, ∀ k, (![((toUnit (G ⊗ G) ≫ x) * b).left, b.left] k) =
      b.left ≫ ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] k := by
    intro b k
    fin_cases k
    · show _ = (b ≫ ((toUnit G ≫ x) * 𝟙 G)).left
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]; rfl
    · exact (Category.comp_id _).symm
  have hμ : fst G G * snd G G = μ[G] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  refine gen_chartPull (chartPullTw L _ (chartPullOut L _ _ _ _ fun k => ?_) (chartPullOut L _ _ _ _ (key _))
    (chartPullOut L _ _ _ _ (key _))) u hu
  rw [_root_.mul_assoc, hμ]
  exact key _ k

theorem translate_div_additive :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A), ∃ w : LB.Iso ((LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]).pull μ[P.A].left) (tw ((LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]).pull (fst P.A P.A).left) ((LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]).pull (snd P.A P.A).left) 1), w.IsGen := by
  intro K _ _ P x
  obtain ⟨t, ht⟩ := GlobalTheory.AbLaw.CubeAssembly.cube_gen _ P P.L P.isLB
  letI : Unique (Spec (CommRingCat.of K)) := inferInstanceAs (Unique (PrimeSpectrum K))
  exact exists_iso_of_cube P.isLB t ht x

end GlobalTheory.TranslateAdditive
end

