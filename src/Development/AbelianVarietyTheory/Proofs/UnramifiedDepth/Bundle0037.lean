module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SeriesTwoPointsEqSumMul
section
namespace GlobalTheory

namespace SeriesTensor

private theorem mem_smul_top_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

private theorem isAdicComplete_of_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [hI : IsAdicComplete I R] :
    IsAdicComplete I M := by
  have htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hx n
    rw [SModEq.zero, mem_smul_top_iff b] at this
    rw [SModEq.zero, htop]
    exact this i
  have hP' : IsPrecomplete I M := by
    rw [isPrecomplete_iff]
    intro F hF
    have hP := hI.toIsPrecomplete
    rw [isPrecomplete_iff] at hP
    have hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro i
      refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
      have := hF hmn
      rw [SModEq.sub_mem, mem_smul_top_iff b] at this
      rw [SModEq.sub_mem, htop]
      simpa using this i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun k => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff b]
    intro i
    have := hL i k
    rw [SModEq.sub_mem, htop] at this
    have hr : b.repr (∑ j, L j • b j) i = L i := by
      have h := congrFun (b.equivFun.apply_symm_apply L) i
      rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
    rw [map_sub, Finsupp.sub_apply, hr]
    exact this
  exact { toIsHausdorff := hH, toIsPrecomplete := hP' }

private theorem exists_pow_mem {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {a c : O} (ha : algebraMap O C a ≠ 0) (hc : ¬ IsUnit c) :
    ∃ n : ℕ, c ^ n ∈ Ideal.span {a} := by
  have h1 : v (algebraMap O C c) < 1 :=
    lt_of_le_of_ne (hv.map_le_one c) fun h => hc (hv.isUnit_iff_valuation_eq_one.2 h)
  have h0 : 0 < v (algebraMap O C a) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 ha)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one h0 h1
  refine ⟨n, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
  rw [map_pow, map_pow]
  exact hn.le

private theorem exists_pow_X_mem {O σ A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (I : Ideal O)
    (hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I) (π : MvPowerSeries σ O →ₐ[O] A)
    (hπ : Function.Surjective π) (j : σ) :
    ∃ M : ℕ, π (MvPowerSeries.X j) ^ M ∈ I.map (algebraMap O A) := by
  change π (MvPowerSeries.X j) ∈ (I.map (algebraMap O A)).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro (P : Ideal A) ⟨hIP, hP⟩
  have hmax : (Ideal.comap (algebraMap O A) P).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤ Ideal.comap (algebraMap O A) P := by
      intro c hc
      obtain ⟨n, hn⟩ := hI c hc
      have : c ^ n ∈ Ideal.comap (algebraMap O A) P := (Ideal.map_le_iff_le_comap.1 hIP) hn
      exact (Ideal.comap_isPrime _ P).mem_of_pow_mem n this
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_isPrime _ P).ne_top hle
    rw [← this]
    exact IsLocalRing.maximalIdeal.isMaximal O
  have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P hmax
  have h2 : (Ideal.comap (π : MvPowerSeries σ O →+* A) P).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (π : MvPowerSeries σ O →+* A) hπ
  have h3 := IsLocalRing.eq_maximalIdeal h2
  have h4 : (MvPowerSeries.X j : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal _ := by
    intro hu
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at hu
    exact not_isUnit_zero hu
  rw [← h3] at h4
  exact h4

private theorem pow_mem_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (I : Ideal O) (e : A →ₐ[O] B) {x : A}
    (h : ∃ M : ℕ, x ^ M ∈ I.map (algebraMap O A)) :
    ∃ M : ℕ, e x ^ M ∈ I.map (algebraMap O B) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ?_⟩
  have := Ideal.mem_map_of_mem (e : A →+* B) hM
  rw [Ideal.map_map, AlgHom.comp_algebraMap, map_pow] at this
  exact this

end SeriesTensor

end GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem SeriesTensor.ev_pt_X {R : Type} [CommRing R] {d : ℕ} (k : Fin 2) (i : Fin d) :
    ev (n := 2) ![pt R d k] (MvPowerSeries.X ((0 : Fin 1), i)) = MvPowerSeries.X (k, i) := by
  unfold ev
  rw [MvPowerSeries.subst_X]
  · rfl
  · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    rintro ⟨a, l⟩
    fin_cases a
    exact MvPowerSeries.constantCoeff_X _


open SeriesTensor in
theorem series_two_points_eq_sum_mul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (J : Ideal (PS O 1 d)), Module.Free O (PS O 1 d ⧸ J) → Module.Finite O (PS O 1 d ⧸ J) → ∀ f : PS O 2 d, ∃ (m : ℕ) (g h : Fin m → PS O 1 d), ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → (∀ u ∈ J, φ u = 0) → (∀ u ∈ J, φ' u = 0) → Φ f = ∑ i, φ (g i) * φ' (h i) := by
  intro p _ C _ _ _ v O _ _ hv _ _ d J hfree hfin f
  have hdom : IsDomain O := hv.hom_inj.isDomain _
  have := ValuationRing.of_integers v hv
  set I : Ideal O := Ideal.span {(p : O)}
  have hp0 : algebraMap O C (p : O) ≠ 0 := by
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I := fun c hc => exists_pow_mem hv hp0 hc
  let Q := PS O 1 d ⧸ J
  let π : PS O 1 d →ₐ[O] Q := Ideal.Quotient.mkₐ O J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O J
  let A := Q ⊗[O] Q
  have hA : IsAdicComplete (I.map (algebraMap O A)) A := by
    rw [IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_basis (Module.Free.chooseBasis O A) I
  let e : Fin 2 → (Q →ₐ[O] A) :=
    ![Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
  let a : Fin 2 × Fin d → A := fun q => e q.1 (π (MvPowerSeries.X (0, q.2)))
  have ha : ∀ q, ∃ M : ℕ, a q ^ M ∈ I.map (algebraMap O A) := fun q =>
    pow_mem_map (A := Q) (B := A) I (e q.1) (exists_pow_X_mem (A := Q) I hI π hπ (0, q.2))
  obtain ⟨Ψ, hΨ⟩ := (mvPowerSeries_eval_of_pow_mem A _ _ a ha).1 hA O
  obtain ⟨m, x, y, hxy⟩ := TensorProduct.exists_sum_tmul_eq (Ψ f)
  choose g hg using fun i => hπ (x i)
  choose h hh using fun i => hπ (y i)
  refine ⟨m, g, h, fun Φ φ φ' h0 h1 hJ hJ' => ?_⟩
  let ψ : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ hJ
  let ψ' : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ' hJ'
  let T : A →ₐ[O] O := Algebra.TensorProduct.lift ψ ψ' fun _ _ => Commute.all _ _
  have hsurj : Function.Surjective Φ := fun c => ⟨algebraMap O _ c, Φ.commutes c⟩
  have hnil := fun q => exists_pow_X_mem I hI Φ hsurj q
  have hH : IsHausdorff (I.map (algebraMap O O)) O := by
    rw [IsHausdorff.map_algebraMap_iff]
    infer_instance
  have key := (mvPowerSeries_eval_of_pow_mem O _ _ _ hnil).2 hH O
    (Φ : PS O 2 d →+* O) (T.comp Ψ : PS O 2 d →+* O)
    (fun t => (Φ.commutes t).trans ((T.comp Ψ).commutes t).symm) (fun _ => rfl) (by
      rintro ⟨k, i⟩
      change T (Ψ (MvPowerSeries.X (k, i))) = _
      rw [hΨ, ← ev_pt_X k i]
      fin_cases k
      · refine Eq.trans ?_ (h0 _).symm
        change T (π _ ⊗ₜ 1) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
        rfl
      · refine Eq.trans ?_ (h1 _).symm
        change T (1 ⊗ₜ π _) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
        rfl)
  have hf : Φ f = T (Ψ f) := RingHom.congr_fun key f
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hg, ← hh]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubSurjectiveOfLinLeftInverse
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem isAdicComplete_germIdeal (R κ : Type) [CommRing R] [Finite κ] :
    IsAdicComplete (germIdeal κ R) (MvPowerSeries κ R) := by
  have h := (mem_sup_span_X_pow_iff_and_isAdicComplete R ⊥ κ).2 inferInstance
  rwa [Ideal.map_bot, bot_sup_eq, ← germIdeal_eq_span] at h

private theorem eq_zero_or_single {κ : Type} {e : κ →₀ ℕ} (he : e.degree < 2) :
    e = 0 ∨ ∃ k, e = Finsupp.single k 1 := by
  classical
  by_cases h0 : e = 0
  · exact Or.inl h0
  · right
    obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
    have hle : Finsupp.single k 1 ≤ e := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 hk
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    have hd : e.degree = 1 + c.degree := by rw [hc, map_add (f := _), Finsupp.degree_single]
    have : c = 0 := (Finsupp.degree_eq_zero_iff c).1 (by omega)
    exact ⟨k, by rw [hc, this, add_zero]⟩

theorem sub_surjective_of_lin_leftInverse : ∀ (R : Type) [CommRing R] (d r : ℕ) (φ : Fin d → PS R 1 r) (A' : Matrix (Fin r) (Fin d) R), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → A' * lin φ = 1 → Function.Surjective (fun f : PS R 1 d => sub ![φ] f) := by
  intro R _ d r φ A' h0 hA
  classical
  set a : Fin 1 × Fin d → PS R 1 r := fun q => (![φ] : Fin 1 → Fin d → PS R 1 r) q.1 q.2 with ha
  have ha' : ∀ q : Fin 1 × Fin d, a q = φ q.2 := by
    rintro ⟨i, j⟩
    fin_cases i
    rfl
  have hs : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by rw [ha', h0]
  let f : PS R 1 d →+* PS R 1 r := (MvPowerSeries.substAlgHom (R := R) hs).toRingHom
  have hf : ∀ u, f u = sub ![φ] u := fun u => by
    change MvPowerSeries.substAlgHom hs u = MvPowerSeries.subst a u
    rw [MvPowerSeries.coe_substAlgHom]
  have hfX : ∀ q, f (MvPowerSeries.X q) = φ q.2 := fun q => by
    change MvPowerSeries.substAlgHom hs _ = _
    rw [MvPowerSeries.substAlgHom_X, ha']
  have hC1 := isAdicComplete_germIdeal R (Fin 1 × Fin d)
  have hC2 := isAdicComplete_germIdeal R (Fin 1 × Fin r)
  have hmap : (germIdeal (Fin 1 × Fin d) R).map f = germIdeal (Fin 1 × Fin r) R := by
    apply le_antisymm
    · rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      rw [hfX]
      exact RingHom.mem_ker.2 (h0 _)
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := germIdeal (Fin 1 × Fin r) R) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [germIdeal_eq_span]
        exact Submodule.fg_span (Set.finite_range _)
      · rw [smul_eq_mul, ← pow_two]
        conv_lhs => rw [germIdeal_eq_span]
        rw [Ideal.span_le]
        rintro _ ⟨⟨i0, i⟩, rfl⟩
        obtain rfl : i0 = 0 := Subsingleton.elim _ _
        have h1 : ∑ j, A' i j • φ j ∈ (germIdeal (Fin 1 × Fin d) R).map f := by
          refine Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ ?_
          rw [← hfX (0, j)]
          exact Ideal.mem_map_of_mem _ (X_mem_germIdeal _)
        have h2 : (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) - ∑ j, A' i j • φ j ∈
            germIdeal (Fin 1 × Fin r) R ^ 2 := by
          refine mem_germIdeal_pow_iff.2 fun e he => ?_
          rcases eq_zero_or_single he with rfl | ⟨⟨k0, k⟩, rfl⟩
          · simp [h0]
          · obtain rfl : k0 = 0 := Subsingleton.elim _ _
            have h3 := congrFun (congrFun hA i) k
            rw [Matrix.mul_apply, Matrix.one_apply] at h3
            simp only [lin, Matrix.of_apply] at h3
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sub, map_sum]
            simp only [map_smul, smul_eq_mul]
            rw [h3, MvPowerSeries.coeff_X]
            simp [Finsupp.single_left_inj, eq_comm]
        have h4 := Submodule.add_mem_sup h1 h2
        rwa [add_sub_cancel] at h4
  have hsurj : Function.Surjective f := by
    have : IsHausdorff ((germIdeal (Fin 1 × Fin d) R).map f) (PS R 1 r) := by
      rw [hmap]
      exact hC2.toIsHausdorff
    refine surjective_of_mk_map_comp_surjective (I := germIdeal (Fin 1 × Fin d) R) f fun y => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPowerSeries.C (MvPowerSeries.constantCoeff y), ?_⟩
    have h5 : f (MvPowerSeries.C (MvPowerSeries.constantCoeff y)) =
        MvPowerSeries.C (MvPowerSeries.constantCoeff y) :=
      (MvPowerSeries.substAlgHom (R := R) hs).commutes _
    rw [RingHom.comp_apply, h5, Ideal.Quotient.eq, hmap]
    exact RingHom.mem_ker.2 (by simp)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, (hf x).symm.trans hx⟩

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThickeningQuotientImageOneIffExistsTorusImage
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem one_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (h : t ≫ f = r) :
    (1 : Over.mk t ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk r ⟶ G).left := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (𝟙_ (Over S)) :=
    toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f)
  have h1 : (1 : Over.mk t ⟶ (Over.pullback f).obj G) = z ≫ (Over.pullback f).map η[G] := by
    rw [Hom.one_def, Functor.obj.η_def, ← Category.assoc]
  have h2 : z.left ≫ pullback.fst (𝟙_ (Over S)).hom f = (toUnit (Over.mk r)).left := by
    have a1 : pullback.fst (𝟙_ (Over S)).hom f ≫ (𝟙_ (Over S)).hom = pullback.snd _ f ≫ f := pullback.condition
    have a2 : z.left ≫ pullback.snd (𝟙_ (Over S)).hom f = t := Over.w z
    have a3 : (toUnit (Over.mk r)).left ≫ (𝟙_ (Over S)).hom = r := Over.w _
    have : Mono (𝟙_ (Over S)).hom := inferInstanceAs (Mono (𝟙 S))
    rw [← cancel_mono (𝟙_ (Over S)).hom, a3, Category.assoc, a1, ← Category.assoc, a2, h]
  rw [h1, Over.comp_left, Category.assoc, A, ← Category.assoc, h2, Hom.one_def, Over.comp_left]

private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem qRel_one_iff_exists_iRel : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ z, QRel c S z 1 ↔ ∃ χ, IRel c S χ z := by
  intro R _ _ I D k G _ _ c S _ _ hS z
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hw : ∀ (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
      w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
    intro w h
    rw [← cancel_mono (Out.thick R I k), ht]
    have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
      (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
    rw [Category.assoc, h1, ← Category.assoc, h]
    exact Over.w z
  have h1 : (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left ≫ pullback.fst D.P.A.hom (Out.thick R I k) =
      (1 : sp (R₀ := R) S ⟶ D.P.A).left := one_left_fst D.P.A (Out.thick R I k) ht
  constructor
  · rintro ⟨w, a, b⟩
    let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw w a)
    have hx : x ≫ c.q = toUnit _ ≫ η[Out.thickObj R I k D.P.A] := by
      apply Over.OverMorphism.ext
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans b).trans h1.symm
    let u := c.isKernel.lift x (toUnit _) hx
    have hu : u ≫ c.i = x := c.isKernel.lift_fst _ _ _
    refine ⟨(Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom).comp
      (splitTorusPointsEquiv _ D.X (Over.mk t) u), u.left, fun χ => ?_, ?_⟩
    · exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (splitTorusPointsEquiv_val _ D.X (Over.mk t) u χ)).symm
    · have e : u.left ≫ c.i.left = w := congrArg (·.left) hu
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans a
  · rintro ⟨χ, w, -, a⟩
    have a' : (w ≫ c.i.left) ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans a
    refine ⟨w ≫ c.i.left, a', ?_⟩
    let u : Over.mk t ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w (by
      have := hw _ a'
      rw [Category.assoc, Over.w c.i] at this
      exact this)
    have hu : u ≫ c.i ≫ c.q = 1 := by
      rw [c.isKernel.w, Hom.one_def, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have e : (w ≫ c.i.left) ≫ c.q.left = (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (·.left) hu)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans h1

end GlobalTheory.ChF
end

