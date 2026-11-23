module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsTenBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem isTen_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (t : IsTen C D h T) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), EllMap C' C f φ → ∃ t' : IsTen C' D h T', ∀ a, (t'.ten.tmul a).left ≫ m.φ = φ ≫ (t.ten.tmul a).left := by
  intro E _ _ _ H R _ ω C D h T t R' _ ω' C' f φ T' m hC
  obtain ⟨-, ⟨-, hφ, iC⟩, -, hact⟩ := hC
  have hφ' : Serre.IsLinearPullback C'.act C.act (spMap f) φ := ⟨hφ, hact⟩
  have hψ : Serre.IsLinearPullback (Serre.comapAct T'.t.act (algebraMap (OK H) (𝓞 E)))
      (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (spMap f) m.φ := ⟨m.cart, fun c => m.act _⟩
  have iT : LBIso (T.t.PP.L.pull m.φ) T'.t.PP.L :=
    LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1)
  have e := fun a => t.ten.baseChange_tmul hφ' hψ a
  refine ⟨⟨t.ten.baseChange hφ' hψ, fun s a => ?_, fun a b => ?_⟩, e⟩
  · refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine (e (s • a)).trans ?_
    rw [t.lin, Over.comp_left, Over.comp_left, Category.assoc, m.act s, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (T.t.act.act s).left) (e a).symm
  · exact lamEq_baseChange _ _ (spMap f) C.P.A C.P.A T.t.G C.P.A C'.P.A C'.P.A T'.t.G C'.P.A φ φ m.φ φ
      hφ.1.w hφ.1.w m.cart hφ T.t.PP.L C.P.L T'.t.PP.L C'.P.L T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB iT iC
      _ _ _ _ _ _ _ _ (e a) (e b) (hact _) ((Category.id_comp _).trans (Category.comp_id _).symm) (t.lam a b)

end GlobalTheory.CM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfPerfect
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.PerfectTensorKernel

open GlobalTheory.CechPic GlobalTheory.HermTensorKernel GlobalTheory.Serre

theorem kTriv_of_perfect : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (L : LB G.left) (N : LB A.left) (h : M →ₗ[O] M →+ O) (n : ℕ) (x y : Fin n → M), (∀ m, m = ∑ i, h m (y i) • x i) → L.IsLB → N.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∃ t : LB.Gen (Theta A N), t.IsGen) → (∀ m m', LamEq N (t.tmul m) (t.tmul m') L (a.act (h m m')) (𝟙 G)) → Out.KTriv G L → Out.KTriv A N := by
  intro S O _ G A _ _ _ _ a b M _ _ t L N h n x₀ y₀ hdual hL hN hΘL hΘ hiso hK R _ s x hx
  have am := a.hom
  let l : M → (M →ₗ[O] O) := fun n =>
    { toFun := fun m => h m n
      map_add' := fun m m' => by rw [map_add (f := _), AddMonoidHom.add_apply]
      map_smul' := fun c m => by rw [map_smul, AddMonoidHom.smul_apply, RingHom.id_apply] }
  let q : M → (A ⟶ G) := fun n => t.mapLeft (IsTensor.self a) (l n)
  have qm : ∀ n, IsMonHom (q n) := fun n => IsTensor.isMonHom_mapLeft _ _ _
  have hq : ∀ m n, t.tmul m ≫ q n = a.act (h m n) := fun m n => by
    simp only [q, IsTensor.tmul_mapLeft, IsTensor.self_tmul]
    rfl
  have basic : ∀ {T : Over S} (g y : T ⟶ G) (m n : M),
      lam (cls N hN) (g ≫ t.tmul m) (y ≫ t.tmul n) = lam (cls L hL) (g ≫ a.act (h m n)) y := by
    intro T g y m n
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hiso m n)
    have h' := congrArg (pull (lift g y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have key : ∀ {T : Over S} (n : M) (u : T ⟶ A) (y : T ⟶ G),
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y := by
    intro T n u y
    refine t.induction_on (P := fun u =>
      lam (cls N hN) u (y ≫ t.tmul n) = lam (cls L hL) (u ≫ q n) y) u ?_ (fun m g => ?_)
      fun u v hu hv => ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [Category.assoc, hq, basic]
    · rw [lam_mul_left hN hΘ, hu, hv, MonObj.mul_comp, lam_mul_left hL hΘL]
  have H := (translDiff_iff hN x).1 hx
  have z : ∀ n, x ≫ q n = 1 := fun n => by
    refine hK R s _ ((translDiff_iff hL (x ≫ q n)).2 ?_)
    have H' := H.pull (Over.mk s ◁ t.tmul n).left
    rwa [pull_lam, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst_assoc, whiskerLeft_snd, key,
      Category.assoc] at H'
  have dec : ∀ u : Over.mk s ⟶ A, u = ∏ i, (u ≫ q (y₀ i)) ≫ t.tmul (x₀ i) := by
    intro u
    refine t.induction_on (P := fun u => u = ∏ i, (u ≫ q (y₀ i)) ≫ t.tmul (x₀ i)) u ?_
      (fun m g => ?_) fun u v hu hv => ?_
    · simp only [MonObj.one_comp, Finset.prod_const_one]
    · simp only [Category.assoc, reassoc_of% hq, ← t.tmul_smul']
      refine Eq.trans ?_ (map_prod (preHom g) _ _)
      rw [← t.tmul_sum, ← hdual]
      rfl
    · simp only [MonObj.mul_comp, Finset.prod_mul_distrib, ← hu, ← hv]
  rw [dec x]
  simp only [z, MonObj.one_comp, Finset.prod_const_one]
  rfl

end GlobalTheory.PerfectTensorKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KeyLocAtOfIsLocalModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem mem_range_iff_valuation_le_one {R K Γ : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hR : ∀ r : R, v (algebraMap R K r) ≤ 1) {π : K} (hπ0 : v π ≠ 0) (hπ : v π < 1) (y : K) :
    y ∈ Set.range (algebraMap R K) ↔ v y ≤ 1 := by
  refine ⟨fun ⟨r, hr⟩ => hr ▸ hR r, fun hy => ?_⟩
  have hu : ∀ u : Rˣ, v (algebraMap R K u) = 1 := fun u => by
    refine le_antisymm (hR _) ?_
    have h1 : v (algebraMap R K u) * v (algebraMap R K (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : Γ) = _ := h1.symm
      _ ≤ v (algebraMap R K u) * 1 := mul_le_mul_right (hR _) _
      _ = _ := _root_.mul_one _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hlt : v (algebraMap R K ϖ) < 1 := by
    refine lt_of_le_of_ne (hR _) fun h => ?_
    rcases ValuationRing.isInteger_or_isInteger R π with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hr0 : r ≠ 0 := by
        rintro rfl
        rw [map_zero] at hr
        exact hπ0 (by rw [← hr, map_zero])
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
      rw [← hr, map_mul, map_mul, hu, map_pow, map_pow, h, one_pow, _root_.mul_one] at hπ
      exact lt_irrefl _ hπ
    · have := hR r
      rw [hr, map_inv₀, inv_le_one₀ (zero_lt_iff.2 hπ0)] at this
      exact absurd hπ (not_lt.2 this)
  rcases ValuationRing.isInteger_or_isInteger R y with h | ⟨r, hr⟩
  · exact h
  · by_cases hy0 : y = 0
    · exact ⟨0, by rw [hy0, map_zero]⟩
    by_cases hr' : IsUnit r
    · obtain ⟨u, rfl⟩ := hr'
      refine ⟨(u⁻¹ : Rˣ), ?_⟩
      rw [← inv_inv y, ← hr]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    · exfalso
      have hm : r ∈ IsLocalRing.maximalIdeal R := hr'
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      have h1 : v y⁻¹ < 1 := by
        rw [← hr, map_mul, map_mul]
        calc _ ≤ v (algebraMap R K ϖ) * 1 := mul_le_mul_right (hR _) _
          _ < 1 := by rwa [_root_.mul_one]
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hy0))] at h1
      exact absurd hy (not_le.2 h1)

theorem keyLocAt_of_isLocalModel : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x p a M → IsLocGen p a T.I → IsLocGen p M.det abelian₂.I → KeyLocAt x T abelian₂ p := by
  intro K _ _ x T abelian₂ p a M hM ha hd
  obtain ⟨R, _, _, _, _, _, y, th', hth', v', hv', hR, h1, h2, h3⟩ := hM
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨K, inferInstance, inferInstance, R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    RingHom.id K, x, a, M.det, a, M.det, 1, 1, GlobalTheory.keyPB_id K x, ⟨th', hth', v', hv', M, y, h1, h2, rfl, h3⟩,
    fun z => ?_, by simp, by simp, ha, hd⟩
  refine mem_range_iff_valuation_le_one (p.valuation K) hR (π := π) (hπ ▸ WithZero.exp_ne_zero) ?_ z
  rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  decide

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LeftEqOfIsLieCombSingle
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LetterEigen

theorem prod_ofFn_eq_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (u : Fin n → M) (i : Fin n), (∀ j, j ≠ i → u j = 1) → (List.ofFn u).prod = u i
  | 0, _, i, _ => i.elim0
  | n + 1, u, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (motive := fun i => (∀ j, j ≠ i → u j = 1) →
      u 0 * (List.ofFn fun k : Fin n => u k.succ).prod = u i) (fun h => ?_) (fun i h => ?_) i h
    · have hprod : (List.ofFn fun k : Fin n => u k.succ).prod = 1 :=
        List.prod_eq_one (List.forall_mem_ofFn_iff.mpr fun k => h _ (Fin.succ_ne_zero k))
      rw [hprod, _root_.mul_one]
    · rw [h 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact prod_ofFn_eq_single (fun k : Fin n => u k.succ) i
        (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e)))

theorem left_eq_of_isLieComb_single {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : R) {w : epsR R ⟶ G}
    (hw : IsLieComb (Pi.single i t) v w) : w.left = spMap (epsScaleR t) ≫ (v i).left := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [prod_ofFn_eq_single u i, hu i, Pi.single_eq_same]
  intro j hj
  have h0 := (LieMultiple.isLieComb_one_iff (0 : R) (v j) 1).1
    ((LieMultiple.lieMultiple_calculus R G G (v j) 1 1 0 0).2.2.2.2.2 (hv j))
  apply Over.OverMorphism.ext
  rw [hu j, Pi.single_eq_of_ne hj, h0]

theorem exists_scale_of_eigen {K : Type} [Field K] [NumberField K] {A B : Over (Sp (𝓞 K))} {A' B' : Over (Sp K)}
    [GrpObj A'] [GrpObj B'] {n : ℕ} {v : Fin n → (epsR K ⟶ A')} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : K)
    (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (α : A ⟶ A) (β : B ⟶ B) (F : A ⟶ B) (hF : α ≫ F = F ≫ β)
    {w₁ : epsR K ⟶ A'} (hw₁ : IsLieComb (Pi.single i t) v w₁) (he : (v i).left ≫ φA ≫ α.left = w₁.left ≫ φA)
    {w : epsR K ⟶ B'} (hw : w.left ≫ φB = (v i).left ≫ φA ≫ F.left) :
    ∃ w' : epsR K ⟶ B', IsLieComb ![t] ![w] w' ∧ w.left ≫ φB ≫ β.left = w'.left ≫ φB := by
  have hc : IsLieComb ![t] ![w] (Chart.spMap (Chart.scaleD t) ≫ w) :=
    (LieMultiple.isLieComb_one_iff_comp t w _).2 rfl
  refine ⟨_, hc, ?_⟩
  have hF' : α.left ≫ F.left = F.left ≫ β.left := by
    rw [← Over.comp_left, hF, Over.comp_left]
  rw [(LieMultiple.isLieComb_one_iff t w _).1 hc, Category.assoc, hw, reassoc_of% hw, ← hF', reassoc_of% he,
    left_eq_of_isLieComb_single hv i t hw₁, Category.assoc]

theorem letter_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (b : E →+* ℂ) (i : Fin (L.m b)) (w : epsR o.K₁ ⟶ o.xB.P.A), L.IsLetter (L.e ⟨b, i⟩) w → ∀ a : 𝓞 E, ∃ w' : epsR o.K₁ ⟶ o.xB.P.A, IsLieComb ![labK c o.K₁ b (a : E)] ![w] w' ∧ w.left ≫ o.φB ≫ (o.oa.act a).left = w'.left ≫ o.φB := by
  intro E _ _ _ _ H l c nΨ n' f o La ho L hL b i w hw a
  obtain ⟨-, -, -, -, -, -, -, -, -, hΨ, h', eΨ, e', -⟩ := ho
  have hb := hL.2.1 b i
  unfold LamLetters.IsLetter at hw
  generalize L.src (L.e ⟨b, i⟩) = s at hb hw
  rcases s with q | q
  · obtain ⟨w₁, h₁, h₂⟩ := hΨ a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.xΨ.basis.1 q.2 _ _ _ _ _ _ (eΨ q.1 a) h₁ h₂ hw
  · obtain ⟨w₁, h₁, h₂⟩ := h' a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.x'.basis.1 q.2 _ _ _ _ _ _ (e' q.1 a) h₁ h₂ hw

end GlobalTheory.LamF.LetterEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieCombAddPowMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LieCombHom

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

theorem isLieComb_zero [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) : IsLieComb 0 v 1 :=
  (LieComb.isLieComb_iff_tanExp _ _).2
    (congrArg Additive.toMul (map_zero (LieComb.combHom hv))).symm

theorem isLieComb_add [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c c' : Fin n → R}
    {w w' : epsR R ⟶ G} (h : IsLieComb c v w) (h' : IsLieComb c' v w') :
    IsLieComb (c + c') v (w * w') := by
  rw [LieComb.isLieComb_iff_tanExp] at h h' ⊢
  rw [h, h']
  exact (congrArg Additive.toMul (map_add (LieComb.combHom hv) c c')).symm

theorem isLieComb_nsmul [IsCommMonObj G] (hv : ∀ i, IsTangent (v i)) {c : Fin n → R}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) (N : ℕ) : IsLieComb (N • c) v (w ^ N) := by
  induction N with
  | zero => rw [zero_smul, pow_zero]; exact isLieComb_zero hv
  | succ N ih => rw [succ_nsmul, pow_succ]; exact isLieComb_add hv ih h

theorem isTangent_comp (f : G ⟶ G') [IsMonHom f] {x : epsR R ⟶ G} (hx : IsTangent x) :
    IsTangent (x ≫ f) := by
  unfold IsTangent at hx ⊢
  rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, IsMonHom.one_hom]

theorem list_prod_comp (f : G ⟶ G') [IsMonHom f] (l : List (epsR R ⟶ G)) :
    l.prod ≫ f = (l.map (· ≫ f)).prod := by
  induction l with
  | nil => simpa using MonObj.one_comp f
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.mul_comp, ih]

theorem isLieComb_comp (f : G ⟶ G') [IsMonHom f] {c : Fin n → R} {w : epsR R ⟶ G}
    (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu i, Category.assoc]
  · rw [list_prod_comp, List.map_ofFn]
    rfl

theorem lieComb_add_pow_map : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] (n : ℕ) (v : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (v i)) → IsLieComb 0 v 1 ∧ (∀ c c' w w', IsLieComb c v w → IsLieComb c' v w' → IsLieComb (c + c') v (w * w')) ∧ (∀ c w (N : ℕ), IsLieComb c v w → IsLieComb (N • c) v (w ^ N)) ∧ ∀ f : G ⟶ G', IsMonHom f → (∀ i, IsTangent (v i ≫ f)) ∧ ∀ c w, IsLieComb c v w → IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  intro R _ G G' _ _ _ n v hv
  exact ⟨isLieComb_zero hv, fun _ _ _ _ h h' => isLieComb_add hv h h',
    fun _ _ N h => isLieComb_nsmul hv h N,
    fun f _ => ⟨fun i => isTangent_comp f (hv i), fun _ _ h => isLieComb_comp f h⟩⟩

end GlobalTheory.LieCombHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoDescent

theorem exists_gen_pull_div_iff {X Y : Scheme.{0}} (f : Y ⟶ X) {N N' : LB X} (hN : N.IsLB) (hN' : N'.IsLB) :
    (∃ t : LB.Gen ((LB.div N N').pull f), t.IsGen) ↔ LBIso (N.pull f) (N'.pull f) := by
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, -, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {L : LB X} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb X Y L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div X N' N hN' hN
  obtain ⟨hDf, eDf⟩ := pull_class hD
  obtain ⟨hNf, eNf⟩ := pull_class hN
  obtain ⟨hN'f, eN'f⟩ := pull_class hN'
  rw [← gen_iff Y _ hDf, eDf, eD, map_div, div_eq_one, ← eNf, ← eN'f,
    iso_iff Y _ _ hNf hN'f]

theorem lbIso_of_field : ∀ (R k : Type) [CommRing R] [IsDedekindDomain R] [Field k] (β : R →+* k), Function.Injective β → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k), IsPullback π p A.hom (spMap β) → ∀ N N' : LB A.left, N.IsLB → N'.IsLB → LBIso (N.pull (eSec A)) (N'.pull (eSec A)) → LBIso (N.pull π) (N'.pull π) → LBIso N N' := by
  intro R k _ _ _ β hβ A _ hA X' π p H N N' hN hN' he hπ
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  let K := FractionRing R
  let δ : K →+* k := IsFractionRing.lift hβ
  have hδ : spMap δ ≫ spMap (algebraMap R K) = spMap β := by
    have e : δ.comp (algebraMap R K) = β := RingHom.ext fun x => IsFractionRing.lift_algebraMap hβ x
    rw [← e]
    exact (Spec.map_comp _ _).symm
  have H₀ := IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))
  set π₀ := pullback.fst A.hom (spMap (algebraMap R K))
  set p₀ := pullback.snd A.hom (spMap (algebraMap R K))
  let q := H₀.lift π (p ≫ spMap δ) (by rw [Category.assoc, hδ, H.w])
  have hq : q ≫ π₀ = π := H₀.lift_fst _ _ _
  have H₁ : IsPullback q p p₀ (spMap δ) := by
    refine IsPullback.of_right ?_ (H₀.lift_snd _ _ _) H₀
    rw [hq, hδ]
    exact H
  obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, comp, linComb, div⟩ :=
    CechPicMul.exists_picardGroup
  let _ := groups
  have pull_class {S T : Scheme.{0}} (f : T ⟶ S) {L : LB S} (hL : L.IsLB) :
      (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
    simpa only [Fintype.prod_unique, zpow_one] using
      linComb S T L hL PUnit (fun _ => f) (fun _ => 1)
  obtain ⟨hD, eD⟩ := div A.left N' N hN' hN
  obtain ⟨hD₀, eD₀⟩ := pull_class π₀ hD
  have h₁ : ∃ t : LB.Gen (((LB.div N N').pull π₀).pull q), t.IsGen := by
    obtain ⟨hDq, eDq⟩ := pull_class q hD₀
    obtain ⟨hDπ, eDπ⟩ := pull_class π hD
    rw [← gen_iff X' _ hDq, eDq, eD₀, ← comp, hq, ← eDπ, gen_iff X' _ hDπ]
    exact (exists_gen_pull_div_iff π hN hN').2 hπ
  obtain ⟨t, ht⟩ := h₁
  have h₂ := FieldTriv.exists_gen_of_isPullback δ p₀ q p H₁ hD₀ t ht
  have h₃ := TrivDedekind.exists_gen_of_generic R K A hA _ π₀ p₀ H₀ _ hD
    ((exists_gen_pull_div_iff _ hN hN').2 he) h₂
  rwa [← gen_iff A.left _ hD, eD, div_eq_one, iso_iff A.left _ _ hN hN'] at h₃

end GlobalTheory.IsoDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem GenFib.nonempty_of_baseChange :
    Out.PolBaseChangeSt → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))), Nonempty (GenFib P) := by
  intro hB K _ _ P
  obtain ⟨P₀, φ, h⟩ := exists_isPolFibre hB (algebraMap (𝓞 K) K) P
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis P₀.A P₀.smoothDim
  exact ⟨⟨P₀, φ, h, v, hv⟩⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PointsSumsEqProducts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem points_sums_eq_products : (∀ (S : Scheme.{0}) (G T : Over S) [GrpObj G], (toUnit T ≫ η[G] = (1 : T ⟶ G)) ∧ (∀ a b : T ⟶ G, padd G a b = a * b) ∧ (∀ (n : ℕ) (a : T ⟶ G), pnsmulPt n a = a ^ n) ∧ ∀ (n : ℕ) (f : Fin n → (T ⟶ G)), psumPt f = (List.ofFn f).prod) ∧ ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R'), Formalism.L2.Pj.dualMap f = Chart.dualMapR f := by
  refine ⟨fun S G T _ => ⟨rfl, fun _ _ => rfl, fun n a => ?_, fun n f => ?_⟩, fun _ _ _ _ _ => rfl⟩
  · induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih =>
      rw [pow_succ, ← ih]; rfl
  · rw [List.prod_eq_foldr]; rfl

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingActIffOAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in
theorem _root_.GlobalTheory.LamF.ringAct_iff_oAct :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G],
      (∀ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, ∃ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, b.act = a.act) ∧
        ∀ b : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Out.RingAct G O, a.act = b.act := by
  intro O _ S G _ _
  exact ⟨fun a => ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ofRingAct a, rfl⟩, fun b => ⟨b.toRingAct, rfl⟩⟩

end GlobalTheory.LamF
end

