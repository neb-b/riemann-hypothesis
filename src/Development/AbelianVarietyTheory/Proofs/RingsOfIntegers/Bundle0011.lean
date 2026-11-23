module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullGenG

theorem hasGen_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) :
    HasGen Lr.L (lf (Finsupp.single (1 : G ⟶ G) 1)) := by
  have h0 := (HasGen.of_gen (L := Lr.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) Lr.rig Lr.rigGen).pull G.hom
  have e1 : (1 : G ⟶ G).left = G.hom ≫ eSec G := rfl
  convert h0 using 1
  rw [lf_single, e1]
  simp [fsum, Finsupp.mapDomain_single]

theorem hasGen_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (cub : CubicalStr G Lr)
    {O : Type} [CommRing O] [StarRing O] (ra : RingAct G O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (hadj : Geo.Tor.LBIso (cubeLB G ![fst G G ≫ ra.act a, snd G G] Lr.L)
      (cubeLB G ![fst G G, snd G G ≫ ra.act (star a)] Lr.L))
    (hprim : Geo.Tor.LBIso Lr.L (cubeLB G ![𝟙 G, ra.act w0] Lr.L)) (k : ℕ) :
    HasGen Lr.L (fsum (K := Fin 2) ![𝟙 G.left, (ra.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)]) := by
  have := ra.hom w0
  obtain ⟨uR, huR⟩ := GlobalTheory.NormRos.exists_gen_rosati Lr.isLB (ra.act a) (ra.act (star a)) hadj
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim S G Lr (ra.act w0) hprim
  have hP : HasGen Lr.L (fsum (GlobalTheory.JetSer.primφ (ra.act w0)) GlobalTheory.JetSer.primε) := HasGen.of_gen ρ hρ
  have h1 := hasGen_one Lr
  obtain ⟨uΨ, huΨ⟩ := HasGen.gen Lr.isLB (h1.sub hP) (K' := Fin 4)
    ![(padd G (𝟙 _) (ra.act w0)).left, 𝟙 G.left, (ra.act w0).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      unfold GlobalTheory.JetSer.primφ GlobalTheory.JetSer.primε
      have e1 : toUnit G ≫ η[G] = (1 : G ⟶ G) := rfl
      rw [padd_eq_mul, e1, lf_single]
      classical
      ext x
      simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
      split_ifs <;> omega)
  have hM := hasGen_pullMul ra w0 a N hN uΨ huΨ uR huR cub.t cub.isGen
  have h2 := (hM.zsmul (-(k : ℤ))).add (h1.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  convert h2 using 1
  classical
  simp only [lf_add, lf_sub, lf_smul, lf_single]
  ext x
  simp [fsum, Fin.sum_univ_succ, Finsupp.single_apply]
  split_ifs <;> ring

end GlobalTheory.PullGenG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsBis
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpandsFracLinear

open GlobalTheory.ExpandsLinear

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k n : ℕ) (c : Fin n → FractionRing R) (s : Fin n → U.SecK k) (E : Fin n → Fam D.toPre (FractionRing R) k) (s₀ : U.SecK k), (∀ l, U.Expands k (s l) (E l)) → (∀ jj, s₀.f jj = ∑ l, resTop _ (scal (pullback.snd G.hom (jK R)) (c l)) * (s l).f jj) → U.Expands k s₀ (∑ l, c l • E l) := by
  intro R _ _ I D A G _ _ U k n c s E s₀ hE hs
  simp only [UnifPre.Expands] at hE ⊢
  choose r hr σ f h1 h2 h3 using hE
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) (Finset.univ : Finset (Fin n))
    (fun l => c l / algebraMap R (FractionRing R) (r l))
  choose a ha using fun l => hb l (Finset.mem_univ l)
  have hc : ∀ l, algebraMap R (FractionRing R) (a l) * algebraMap R (FractionRing R) (r l) =
      algebraMap R (FractionRing R) (b : R) * c l := by
    intro l
    have hrl : algebraMap R (FractionRing R) (r l) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R (FractionRing R))]
      exact fun h => hr l (IsFractionRing.injective R (FractionRing R) h)
    rw [ha l, Algebra.smul_def]
    field_simp
  refine ⟨b, nonZeroDivisors.ne_zero b.2, secComb (fun l => scal G.hom (a l)) σ,
    fun α => secComb (fun l => scal D.toPre.P.A.hom (a l)) (fun l => f l α), ?_, ?_, ?_⟩
  · exact secScal_comb (algebraMap R (FractionRing R)) U.LG.L _ _ _ _ (pullback.fst G.hom (jK R))
      (pullback.snd G.hom (jK R)) _ G.hom rfl pullback.condition s σ r a b c hc h1 s₀ hs
  · intro α
    refine secScal_comb (algebraMap R (FractionRing R)) D.toPre.P.L _ _ _ _ (D.toPre.prB (FractionRing R)).left
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_ ?_ (fun l => (E l).s α)
      (fun l => f l α) r a b c hc (fun l => h2 l α) _ ?_
    · have hh := (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
      unfold DegPre.BF TF at *
      rw [hh]
      congr 1
      show jFK (FractionRing R) ≫ jK R = _
      unfold jFK jK
      rw [← Spec.map_comp]
      rfl
    · exact Over.w (D.toPre.prB (FractionRing R))
    · intro j
      rw [fam_sum_f]
      simp only [smul_f]
      rfl
  · intro e
    exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun l => h3 l e) (fun j => rfl) (fun α j => rfl)

end GlobalTheory.ExpandsFracLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
section
namespace GlobalTheory.PowMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

variable {S : Scheme.{0}}

noncomputable def powHom {G B : Over S} (q : G ⟶ B) : ∀ n : ℕ, powObj G n ⟶ powObj B n
  | 0 => 𝟙 (𝟙_ (Over S))
  | n + 1 => (q ⊗ₘ powHom q n : G ⊗ powObj G n ⟶ B ⊗ powObj B n)

theorem powHom_pr {G B : Over S} (q : G ⟶ B) :
    ∀ (n : ℕ) (i : Fin n), powHom q n ≫ powPr B i = powPr G i ≫ q
  | 0, i => i.elim0
  | n + 1, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tensorHom_fst q (powHom q n)
    · show (q ⊗ₘ powHom q n) ≫ snd _ _ ≫ powPr B i = (snd _ _ ≫ powPr G i) ≫ q
      rw [tensorHom_snd_assoc, powHom_pr q n i, Category.assoc]

theorem prop_powHom (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G B : Over S} (q : G ⟶ B) (hq : P q.left) : ∀ n : ℕ, P (powHom q n).left
  | 0 => P.id_mem S
  | n + 1 => by
    have ih := prop_powHom P q hq n
    show P (q ⊗ₘ powHom q n).left
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := P) hq ih (Over.w q).symm (Over.w (powHom q n)).symm

theorem prop_of_comm (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ} (p : IsPowGrp G' G j)
    (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B') (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q)
    (hq : P q.left) : P q'.left := by
  let e : G' ≅ powObj G j := p.lim.conePointUniqueUpToIso (powIsLimit G j)
  let f : B' ≅ powObj B j := pB.lim.conePointUniqueUpToIso (powIsLimit B j)
  have he : ∀ i, e.hom ≫ powPr G i = p.pr i := fun i =>
    p.lim.conePointUniqueUpToIso_hom_comp (powIsLimit G j) ⟨i⟩
  have hf : ∀ i, f.inv ≫ pB.pr i = powPr B i := fun i =>
    pB.lim.conePointUniqueUpToIso_inv_comp (powIsLimit B j) ⟨i⟩
  have hq' : q' = e.hom ≫ powHom q j ≫ f.inv := by
    refine pB.lim.hom_ext fun ⟨i⟩ => ?_
    show q' ≫ pB.pr i = (e.hom ≫ powHom q j ≫ f.inv) ≫ pB.pr i
    rw [h, Category.assoc, Category.assoc, hf, powHom_pr, ← Category.assoc, he]
  have i1 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have i2 : IsIso f.inv.left := inferInstanceAs (IsIso ((Over.forget _).map f.inv))
  rw [hq', Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact prop_powHom P q hq j

theorem isMonHom_of_comm {G' G B' B : Over S} [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] {j : ℕ}
    (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B) (q' : G' ⟶ B')
    (h : ∀ i, q' ≫ pB.pr i = p.pr i ≫ q) (hq : IsMonHom q) : IsMonHom q' := by
  refine ⟨pB.lim.hom_ext fun ⟨i⟩ => ?_, pB.lim.hom_ext fun ⟨i⟩ => ?_⟩
  · have := p.hom i
    have := pB.hom i
    show (η ≫ q') ≫ pB.pr i = η ≫ pB.pr i
    rw [Category.assoc, h, IsMonHom.one_hom, IsMonHom.one_hom]
  · have := p.hom i
    have := pB.hom i
    show (μ ≫ q') ≫ pB.pr i = ((q' ⊗ₘ q') ≫ μ) ≫ pB.pr i
    rw [Category.assoc, Category.assoc, h, IsMonHom.mul_hom, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h]

theorem main : ∀ (S : Scheme.{0}) (G' G B' B : Over S) [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] (j : ℕ) (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (q : G ⟶ B), ∃ q' : G' ⟶ B', (∀ i, q' ≫ pB.pr i = p.pr i ≫ q) ∧ (IsMonHom q → IsMonHom q') ∧ (Flat q.left → Flat q'.left) ∧ (Surjective q.left → Surjective q'.left) ∧ (QuasiCompact q.left → QuasiCompact q'.left) ∧ (IsAffineHom q.left → IsAffineHom q'.left) := by
  intro S G' G B' B _ _ _ _ j p pB q
  have h : ∀ i, pB.lim.lift (Fan.mk G' fun i => p.pr i ≫ q) ≫ pB.pr i = p.pr i ≫ q := fun i =>
    pB.lim.fac (Fan.mk G' fun i => p.pr i ≫ q) ⟨i⟩
  exact ⟨_, h, isMonHom_of_comm p pB q _ h, prop_of_comm @Flat p pB q _ h,
    prop_of_comm @Surjective p pB q _ h, prop_of_comm @QuasiCompact p pB q _ h,
    prop_of_comm @IsAffineHom p pB q _ h⟩

end GlobalTheory.PowMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowPrimitive

open Geo.Tor

def chartPullSwap {X X' : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X))
    (φ : K → (X ⟶ X)) (ψ : K → (X' ⟶ X')) (ε : K → ℤ) (hc : ∀ k i, ψ k ≫ F i = F i ≫ φ k) :
    ChartPull (LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε) (LB.LinComb (LB.LinComb L φ ε) F (fun _ => 1)) (𝟙 X') :=
  have le : ∀ j : K → J → L.ι, LB.wchart (LB.LinComb L F (fun _ => 1)) ψ j ≤
      (𝟙 X') ⁻¹ᵁ LB.wchart (LB.LinComb L φ ε) F (fun i k => j k i) :=
    fun j y hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => by
      have h : (ψ k ≫ F i) y ∈ L.U (j k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
      rw [hc] at h
      exact h
  { idx := fun j i k => j k i
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 X') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L φ ε) F (fun _ => 1) (𝟙 X') y _ _ (le j hj) (le j' hj')).symm)
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k)
        (gm_linComb L F (fun _ => 1) (𝟙 X' ≫ ψ k) y (j k) (j' k)
          (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k))).trans ?_
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ (1 : ℤ))
        (gm_linComb L φ ε (𝟙 X' ≫ F i) y (fun k => j k i) (fun k => j' k i)
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      simp only [zpow_one, Category.id_comp, hc, ← Finset.prod_zpow]
      exact Finset.prod_comm }

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨LB.linCombIso u φ ε, linCombIso_isGen u hu φ ε⟩

private lemma foldr_padd_comp_eq_comp_foldr_padd {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (h : G' ⟶ G) [IsMonHom h]
    {n : ℕ} (x' : Fin n → (G' ⟶ G')) (x : Fin n → (G ⟶ G)) (hx : ∀ k, x' k ≫ h = h ≫ x k) (l : List (Fin n)) :
    List.foldr (fun k acc => padd G' (x' k) acc) (pzero G' G') l ≫ h =
      h ≫ List.foldr (fun k acc => padd G (x k) acc) (pzero G G) l := by
  induction l with
  | nil =>
    rw [List.foldr_nil, List.foldr_nil, show pzero G' G' = 1 from Over.OverMorphism.ext rfl,
      show pzero G G = 1 from Over.OverMorphism.ext rfl, one_comp, comp_one]
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, show ∀ a b : G' ⟶ G', padd G' a b = a * b from fun _ _ => Over.OverMorphism.ext rfl,
      show ∀ a b : G ⟶ G, padd G a b = a * b from fun _ _ => Over.OverMorphism.ext rfl, mul_comp, comp_mul, hx k, ih]

theorem lbIso_cube_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f : G ⟶ G) (f' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → Geo.Tor.LBIso L (cubeLB G ![𝟙 G, f] L) → Geo.Tor.LBIso L' (cubeLB G' ![𝟙 G', f'] L') := by
  intro S G' G _ _ _ _ j p L L' hL hL' hbox f f' hc hprim
  unfold cubeLB boxLB at *
  have hcomm : ∀ (I : ULift.{0} (Finset (Fin 2))) (i : Fin j),
      (psum G' ![𝟙 G', f'] I.down).left ≫ (p.pr i).left = (p.pr i).left ≫ (psum G ![𝟙 G, f] I.down).left := by
    intro I i
    have := p.hom i
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold psum
    refine foldr_padd_comp_eq_comp_foldr_padd (p.pr i) _ _ (fun k => ?_) _
    fin_cases k
    · simp
    · simpa using hc i
  have hP := linComb_isLB _ hL (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hQ := linComb_isLB _ (linComb_isLB _ hL (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hR := linComb_isLB _ hP (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h1 := lbIso_linComb hbox (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h3 := lbIso_linComb hprim (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have cp := chartPullSwap L (fun i => (p.pr i).left) (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)) hcomm
  have h2 : LBIso (LB.LinComb (LB.LinComb L (fun i => (p.pr i).left) (fun _ => (1 : ℤ)))
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
      (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)))
      (LB.LinComb (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
        (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))) := by
    have hQQ := LBIso.trans hQ hP hQ (LBIso.symm h3) h3
    exact LBIso.chartPull (h := 𝟙 G'.left) cp (chartPullId _) hQQ
  exact LBIso.trans hL' hQ (linComb_isLB _ hL' _ _) (LBIso.trans hL' hP hQ hbox h3)
    (LBIso.trans hQ hR (linComb_isLB _ hL' _ _) (LBIso.symm h2) (LBIso.symm h1))

end GlobalTheory.PowPrimitive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowKernel

theorem pow_ext {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    {X : Over S} {x y : X ⟶ G'} (h : ∀ l, x ≫ p.pr l = y ≫ p.pr l) : x = y :=
  Fan.IsLimit.hom_ext p.lim x y h

theorem one_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    (l : Fin j) : η[G'] ≫ p.pr l = η[G] := by
  haveI := p.hom l
  exact IsMonHom.one_hom (p.pr l)

theorem main : ∀ (S : Scheme.{0}) (T' T G' G B' B : Over S) [GrpObj T'] [GrpObj T] [GrpObj G'] [GrpObj G] [GrpObj B'] [GrpObj B] (j : ℕ) (pT : IsPowGrp T' T j) (p : IsPowGrp G' G j) (pB : IsPowGrp B' B j) (i : T ⟶ G) (q : G ⟶ B) (i' : T' ⟶ G') (q' : G' ⟶ B'), (∀ l, i' ≫ p.pr l = pT.pr l ≫ i) → (∀ l, q' ≫ pB.pr l = p.pr l ≫ q) → IsPullback i (toUnit T) q η[B] → IsPullback i' (toUnit T') q' η[B'] := by
  intro S T' T G' G B' B _ _ _ _ _ _ j pT p pB i q i' q' hi hq h

  have w : i' ≫ q' = toUnit T' ≫ η[B'] := by
    apply pow_ext pB
    intro l
    rw [Category.assoc, Category.assoc, hq l, one_pr pB l, ← Category.assoc, hi l,
      Category.assoc, h.w, ← Category.assoc, toUnit_unique (pT.pr l ≫ toUnit T) (toUnit T')]

  have key : ∀ (s : PullbackCone q' η[B']) (l : Fin j),
      (s.fst ≫ p.pr l) ≫ q = s.snd ≫ η[B] := by
    intro s l
    rw [Category.assoc, ← hq l, ← Category.assoc, s.condition, Category.assoc, one_pr pB l]
  have fac : ∀ (s : PullbackCone q' η[B']) (l : Fin j),
      Fan.IsLimit.lift pT.lim (fun l => h.lift (s.fst ≫ p.pr l) s.snd (key s l)) ≫ pT.pr l =
        h.lift (s.fst ≫ p.pr l) s.snd (key s l) :=
    fun s l => Fan.IsLimit.fac pT.lim _ l
  refine IsPullback.of_isLimit (c := PullbackCone.mk i' (toUnit T') w)
    (PullbackCone.IsLimit.mk w
      (fun s => Fan.IsLimit.lift pT.lim (fun l => h.lift (s.fst ≫ p.pr l) s.snd (key s l)))
      ?_ ?_ ?_)
  · intro s
    apply pow_ext p
    intro l
    rw [Category.assoc, hi l, ← Category.assoc, fac s l, h.lift_fst]
  · intro s
    exact toUnit_unique _ _
  · intro s m hm _
    apply pow_ext pT
    intro l
    rw [fac s l]
    apply h.hom_ext
    · rw [h.lift_fst, Category.assoc, ← hi l, ← Category.assoc, hm]
    · rw [h.lift_snd]
      exact toUnit_unique _ _

end GlobalTheory.PowKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.QuasiCompactGeomConnectedPow
section
namespace GlobalTheory.PowGrp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem quasiCompact_geomConnected_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), (QuasiCompact G.hom → QuasiCompact G'.hom) ∧ (Smooth G.hom → GeometricallyConnected G.hom → GeometricallyConnected G'.hom) := by
  intro S G' G _ _ j p
  refine ⟨prop_of_isPowGrp @QuasiCompact p, fun hs hc => ?_⟩
  obtain ⟨e, he, hw⟩ := exists_iso_powObj p
  have := geomConnected_powObj G j
  have := smooth_isMultiplicative
  have : Smooth (powObj G j).hom := prop_powObj @Smooth G hs j
  have := geomConnected_of_isIso e
  rw [hw]
  exact GeometricallyConnected.comp _ _

end GlobalTheory.PowGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
section
namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem smoothOfRelativeDimension_powObj {S : Scheme.{0}} (G : Over S) (g : ℕ)
    (hG : SmoothOfRelativeDimension g G.hom) : ∀ n : ℕ, SmoothOfRelativeDimension (n * g) (powObj G n).hom
  | 0 => by
    have h : SmoothOfRelativeDimension 0 (𝟙 S) := inferInstance
    rw [Nat.zero_mul]
    exact h
  | n + 1 => by
    have ih := smoothOfRelativeDimension_powObj G g hG n
    have h1 : SmoothOfRelativeDimension (n * g) (pullback.fst G.hom (powObj G n).hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n * g + g) (pullback.fst G.hom (powObj G n).hom ≫ G.hom) :=
      inferInstance
    rw [Nat.succ_mul]
    exact h2

theorem polAV_g_of_isPowPolAV : ∀ (K : Type) [Field K] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of K))),
    IsPowPolAV A' A j → A'.g = j * A.g := by
  intro K _ j A A' p
  let e : A'.A ≅ powObj A.A j := p.lim.conePointUniqueUpToIso (powIsLimit A.A j)
  have hw : A'.A.hom = e.hom.left ≫ (powObj A.A j).hom := (Over.w e.hom).symm
  have h1 := smoothOfRelativeDimension_powObj A.A A.g A.smoothDim j
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + j * A.g) A'.A.hom := by
    rw [hw]; infer_instance
  have := H1.dim_unique _ A'.smoothDim h2 (eSec A'.A (default : PrimeSpectrum K))
  simpa using this

end GlobalTheory
end

