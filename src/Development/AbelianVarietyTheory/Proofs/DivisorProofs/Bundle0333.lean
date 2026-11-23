module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationDescendAway
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem units_localization_descend_away (A : Type) [CommRing A] (M : Submonoid A)
    (u : (Localization M)ˣ) :
    ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M,
      φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  obtain ⟨⟨a, m₁⟩, ha⟩ := IsLocalization.mk'_surjective M (u : Localization M)
  obtain ⟨⟨b, m₂⟩, hb⟩ := IsLocalization.mk'_surjective M ((u⁻¹ : (Localization M)ˣ) : Localization M)
  simp only at ha hb
  have hprod : IsLocalization.mk' (Localization M) (a * b) (m₁ * m₂) = 1 := by
    rw [IsLocalization.mk'_mul, ha, hb]; simp
  have h1 : algebraMap A (Localization M) (a * b) = algebraMap A (Localization M) ((m₁ * m₂ : M) : A) := by
    have := IsLocalization.mk'_spec (Localization M) (a * b) (m₁ * m₂)
    rw [hprod, one_mul] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 h1
  set m : A := (m₁ : A) * m₂ * c with hm
  have hmM : m ∈ M := M.mul_mem (M.mul_mem m₁.2 m₂.2) c.2
  have hc' : (c : A) * (a * b) = (c : A) * ((m₁ : A) * m₂) := by
    simpa [Submonoid.coe_mul] using hc
  let s := IsLocalization.Away.invSelf (S := Localization.Away m) m
  have hs : algebraMap A (Localization.Away m) m * s = 1 := IsLocalization.Away.mul_invSelf m
  let x : Localization.Away m := algebraMap A _ (a * (m₂ * c)) * s
  let y : Localization.Away m := algebraMap A _ (b * (m₁ * c)) * s
  have hxy : x * y = 1 := by
    have e : a * (m₂ * c) * (b * (m₁ * c)) = m * m := by
      rw [hm]; linear_combination ((m₁ : A) * m₂ * c) * hc'
    calc x * y = algebraMap A _ (a * (m₂ * c) * (b * (m₁ * c))) * s * s := by
          simp only [x, y, map_mul]; ring
      _ = (algebraMap A (Localization.Away m) m * s) * (algebraMap A (Localization.Away m) m * s) := by
          rw [e, map_mul]; ring
      _ = 1 := by rw [hs, one_mul]
  refine ⟨m, hmM, ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  intro φ hφ
  have hφa : ∀ r : A, φ (algebraMap A _ r) = algebraMap A (Localization M) r := fun r =>
    congrArg (fun f : A →+* Localization M => f r) hφ
  apply Units.ext
  show φ x = (u : Localization M)
  have hu : (u : Localization M) * algebraMap A _ (m₁ : A) = algebraMap A _ a := by
    rw [← ha]; exact IsLocalization.mk'_spec _ _ _
  have hφs : algebraMap A (Localization M) m * φ s = 1 := by
    rw [← hφa, ← map_mul, hs, map_one]
  have hx : φ x * algebraMap A (Localization M) (m₁ : A) = algebraMap A _ a := by
    have : φ x * algebraMap A (Localization M) (m₁ : A)
        = algebraMap A (Localization M) a * (algebraMap A (Localization M) m * φ s) := by
      simp only [x, map_mul, hφa, hm]; ring
    rw [this, hφs, mul_one]
  have hunit : IsUnit (algebraMap A (Localization M) (m₁ : A)) := IsLocalization.map_units _ m₁
  exact hunit.mul_left_inj.1 (hx.trans hu.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariablesUniformizerPowerLatticeBasisOpenVolume
section
open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss

namespace GlobalTheory.UnfoldLoss.LatVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem varLat_eq_pi (G : Grid k) (ϖ : kˣ) (n : ℕ) :
    (varLat G ϖ n : Set (Vars G)) = Set.univ.pi fun _ => Set.univ.pi fun _ => cball (ϖ ^ n) := by
  ext e
  exact ⟨fun h j _ r _ => h j r, fun h j r => h j trivial r trivial⟩

theorem eventually_cball_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∀ᶠ n : ℕ in Filter.atTop, cball (ϖ ^ n) ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 γ
  refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k ((ϖ ^ n : kˣ) : k) := hz
  rw [Units.val_pow_eq_pow_val, map_pow] at hz'
  exact (hz'.trans (pow_le_pow_of_le_one zero_le h1.le hn)).trans_lt hN

theorem varLat_basis_open_vol : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (G : Grid k) (ν : Measure k), IsUnitVol ν → ∀ ϖ : kˣ, IsUnif ϖ →
    (∀ s ∈ nhds (0 : Vars G), ∃ n : ℕ, (varLat G ϖ n : Set (Vars G)) ⊆ s) ∧
    ∀ n : ℕ, IsOpen (varLat G ϖ n : Set (Vars G)) ∧ varsVol G ν (varLat G ϖ n : Set (Vars G)) ≠ ⊤ ∧
      (varsVol G ν).real (varLat G ϖ n : Set (Vars G)) = ((resCard k : ℝ)⁻¹) ^ (n * varCount G) := by
  intro k _ _ _ _ _ _ G ν hν ϖ hϖ
  classical
  refine ⟨fun s hs => ?_, fun n => ?_⟩
  · rw [nhds_pi, Filter.mem_pi'] at hs
    obtain ⟨I, t, ht, hts⟩ := hs
    have key : ∀ j, ∀ᶠ n : ℕ in Filter.atTop, (Set.univ.pi fun _ => cball (ϖ ^ n)) ⊆ t j := fun j => by
      have hj := ht j
      rw [nhds_pi, Filter.mem_pi'] at hj
      obtain ⟨J, u, hu, hut⟩ := hj
      filter_upwards [Filter.eventually_all.2 fun r => eventually_cball_subset hϖ (hu r)] with n hn e he
      exact hut fun r _ => hn r (he r trivial)
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 key).exists
    refine ⟨n, fun e he => hts fun j _ => hn j fun r _ => he j r⟩
  · haveI := hν.1
    haveI := secondCountable k
    have h1 : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      nabs_uniformiser hϖ.irreducible rfl
    have hv : varsVol G ν (varLat G ϖ n : Set (Vars G)) =
        ((distribHaarChar k ϖ ^ (n * varCount G) : NNReal) : ENNReal) := by
      rw [varLat_eq_pi, varsVol, Measure.pi_pi]
      simp only [Measure.pi_pi, measure_cball, hν.2, mul_one, Finset.prod_const, Finset.card_univ, map_pow,
        varCount, ← Nat.card_eq_fintype_card, ENNReal.coe_pow, ← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · rw [varLat_eq_pi]
      exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _
    · rw [hv]; exact ENNReal.coe_ne_top
    · rw [Measure.real, hv, ENNReal.coe_toReal, NNReal.coe_pow, h1]

end GlobalTheory.UnfoldLoss.LatVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WExactColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactColim

abbrev altC {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) :
    CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

abbrev altM {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1}) :
    altC X F ⟶ altC Y F :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerRight g F)

theorem altM_d {T : Type 1} [Category.{0} T] {X Y : CosimplicialObject T} (g : X ⟶ Y) (F : T ⥤ AddCommGrpCat.{1})
    (n m : ℕ) (w : (altC X F).X n) :
    (altC Y F).d n m ((altM g F).f n w) = (altM g F).f m ((altC X F).d n m w) := by
  have h := ConcreteCategory.congr_hom ((altM g F).comm n m) w
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

theorem altM_comp {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM (g ≫ h) F).f n w := by
  show F.map (h.app _) (F.map (g.app _) w) = F.map (g.app _ ≫ h.app _) w
  rw [F.map_comp]
  rfl

theorem altM_comp' {T : Type 1} [Category.{0} T] {X Y Z : CosimplicialObject T} (g : X ⟶ Y) (h : Y ⟶ Z)
    (g' : X ⟶ Z) (e : g ≫ h = g') (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ) (w : (altC X F).X n) :
    (altM h F).f n ((altM g F).f n w) = (altM g' F).f n w := by
  subst e
  exact altM_comp g h F n w

theorem exact_elt {T : Type 1} [Category.{0} T] (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (n : ℕ)
    (h : (altC X F).ExactAt (n + 1)) (w : (altC X F).X (n + 1)) (hw : (altC X F).d (n + 1) (n + 2) w = 0) :
    ∃ v : (altC X F).X n, (altC X F).d n (n + 1) v = w := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem wExact_colimit : ∀ (T : Type 1) [Category.{0} T] (N : T ⥤ AddCommGrpCat.{1}), PreservesFilteredColimitsOfSize.{0, 0} N → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (U : J ⥤ T) (X : J ⥤ CosimplicialObject T) (a : U ⋙ CosimplicialObject.const T ⟶ X) (cU : Cocone U) (cX : Cocone X) (b : (CosimplicialObject.const T).obj cU.pt ⟶ cX.pt), IsColimit cU → (∀ k : SimplexCategory, Nonempty (IsColimit (((evaluation SimplexCategory T).obj k).mapCocone cX))) → (∀ j, a.app j ≫ cX.ι.app j = (CosimplicialObject.const T).map (cU.ι.app j) ≫ b) → (∀ j, WExact N (a.app j)) → WExact N b := by
  intro T _ N hN J _ _ U X a cU cX b hU hX hab hW
  have fe := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements T N).1 hN
  have hNc : ∀ {A B C : T} (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A), N.map (f ≫ g) x = N.map g (N.map f x) := by
    intros; simp
  have hab' : ∀ j (k : SimplexCategory), (a.app j).app k ≫ (cX.ι.app j).app k = cU.ι.app j ≫ b.app k := by
    intro j k
    exact NatTrans.congr_app (hab j) k
  have hnat : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (a.app j).app k ≫ (X.map f).app k = U.map f ≫ (a.app j').app k := by
    intro j j' f k
    exact (NatTrans.congr_app (a.naturality f) k).symm
  have hXι : ∀ {j j' : J} (f : j ⟶ j') (k : SimplexCategory), (X.map f).app k ≫ (cX.ι.app j').app k = (cX.ι.app j).app k := by
    intro j j' f k
    exact NatTrans.congr_app (cX.w f) k
  have feX : ∀ k : SimplexCategory, (∀ x : N.obj (cX.pt.obj k), ∃ j y, N.map ((cX.ι.app j).app k) y = x) ∧
      ∀ j (y : N.obj ((X.obj j).obj k)), N.map ((cX.ι.app j).app k) y = 0 → ∃ (j' : J) (f : j ⟶ j'), N.map ((X.map f).app k) y = 0 := by
    intro k
    exact fe J (X ⋙ (evaluation SimplexCategory T).obj k) _ (hX k).some
  have feU := fe J U cU hU
  refine ⟨?_, ?_, ?_⟩
  ·
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := feU.1 x
    have h0 : N.map ((cX.ι.app j).app (SimplexCategory.mk 0)) (N.map ((a.app j).app (SimplexCategory.mk 0)) y) = 0 := by
      rw [← hNc, hab', hNc]; simpa using hx
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h0
    rw [← hNc, hnat, hNc] at hf
    have hk := (hW k).1 (hf.trans (map_zero _).symm)
    rw [← cU.w f, hNc]
    simp only [Functor.comp_obj] at hk
    rw [hk, map_zero]
  ·
    intro y hy
    obtain ⟨j, y', rfl⟩ := (feX _).1 y
    have hδ : ∀ {Y Z : CosimplicialObject T} (g : Y ⟶ Z) (i : Fin 2),
        Y.δ (n := 0) i ≫ g.app (SimplexCategory.mk 1) = g.app (SimplexCategory.mk 0) ≫ Z.δ (n := 0) i :=
      fun g i => g.naturality _
    set d' := N.map ((X.obj j).δ (n := 0) 0) y' - N.map ((X.obj j).δ (n := 0) 1) y' with hd'
    have h1 : N.map ((cX.ι.app j).app (SimplexCategory.mk 1)) d' = 0 := by
      rw [hd', map_sub, ← hNc, ← hNc, hδ, hδ, hNc, hNc]
      exact sub_eq_zero.mpr hy
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : N.map ((X.obj k).δ (n := 0) 0) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') =
        N.map ((X.obj k).δ (n := 0) 1) (N.map ((X.map f).app (SimplexCategory.mk 0)) y') := by
      rw [← sub_eq_zero, ← hNc, ← hNc, ← hδ, ← hδ, hNc, hNc, ← map_sub]
      exact hf
    obtain ⟨x, hx⟩ := (hW k).2.1 _ h2
    refine ⟨N.map (cU.ι.app k) x, ?_⟩
    rw [← hNc, ← hab', hNc]
    simp only [Functor.comp_obj] at hx
    rw [hx, ← hNc, hXι]
  · intro n
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.ab_exact_iff]
    intro z hz
    obtain ⟨j, z', rfl⟩ := (feX _).1 z
    have h1 : (altM (cX.ι.app j) N).f (n + 2) ((altC (X.obj j) N).d (n + 1) (n + 2) z') = 0 := by
      exact (altM_d (cX.ι.app j) N (n + 1) (n + 2) z').symm.trans hz
    obtain ⟨k, f, hf⟩ := (feX _).2 j _ h1
    have h2 : (altC (X.obj k) N).d (n + 1) (n + 2) ((altM (X.map f) N).f (n + 1) z') = 0 := by
      exact (altM_d (X.map f) N (n + 1) (n + 2) z').trans hf
    obtain ⟨v, hv⟩ := exact_elt _ N n ((hW k).2.2 n) _ h2
    refine ⟨(altM (cX.ι.app k) N).f n v, ?_⟩
    show (altC cX.pt N).d n (n + 1) ((altM (cX.ι.app k) N).f n v) = (altM (cX.ι.app j) N).f (n + 1) z'
    rw [altM_d, hv]
    exact altM_comp' (X.map f) (cX.ι.app k) (cX.ι.app j) (cX.w f) N (n + 1) z'

end GlobalTheory.EtC.WExactColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLeastSquaresBound
section
open scoped ComplexOrder Matrix

namespace GlobalTheory.WeightedLS

open Matrix

variable {M g : ℕ}

theorem det_pos (L : Matrix (Fin M) (Fin g) ℝ) (hL : L.rank = g) (D : Fin M → ℝ)
    (hD : ∀ k, 0 < D k) : 0 < (L.transpose * Matrix.diagonal D * L).det := by
  have hinj : Function.Injective L.mulVec := by
    have h := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
    have h2 : Module.finrank ℝ (LinearMap.range L.mulVecLin) = g := hL
    rw [h2, Module.finrank_fin_fun] at h
    have h3 : Module.finrank ℝ (LinearMap.ker L.mulVecLin) = 0 := by omega
    have h4 : LinearMap.ker L.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h3
    exact LinearMap.ker_eq_bot.mp h4
  have hP : (Matrix.diagonal D).PosDef := Matrix.posDef_diagonal_iff.mpr hD
  have h := hP.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_pos

theorem det_eq_sum (L X : Matrix (Fin M) (Fin g) ℝ) (D : Fin M → ℝ) :
    (L.transpose * Matrix.diagonal D * X).det = ∑ S : {S : Finset (Fin M) // S.card = g},
      (∏ j, D (S.1.orderEmbOfFin S.2 j)) * ((L.submatrix (S.1.orderEmbOfFin S.2) id).det *
        (X.submatrix (S.1.orderEmbOfFin S.2) id).det) := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : (L.transpose * Matrix.diagonal D).submatrix id (S.1.orderEmbOfFin S.2) =
      (L.submatrix (S.1.orderEmbOfFin S.2) id).transpose *
        Matrix.diagonal (fun j => D (S.1.orderEmbOfFin S.2 j)) := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem block_bound (A : Matrix (Fin g) (Fin g) ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c : Fin g → ℝ) (k : Fin g),
      |A.det * (A.updateCol k c).det| ≤ K * ‖c‖ * (A.det * A.det) := by
  by_cases hA : A.det = 0
  · exact ⟨0, le_rfl, fun c k => by simp [hA]⟩
  · let f : (Fin g → ℝ) →L[ℝ] (Fin g → ℝ) := LinearMap.toContinuousLinearMap (Matrix.cramer A)
    have hp : 0 < |A.det| := abs_pos.mpr hA
    refine ⟨‖f‖ / |A.det|, by positivity, fun c k => ?_⟩
    have h1 : |(A.updateCol k c).det| ≤ ‖f‖ * ‖c‖ := by
      have h2 : (A.updateCol k c).det = f c k := by
        simp [f, Matrix.cramer_apply]
      rw [h2]
      exact (norm_le_pi_norm (f c) k).trans (f.le_opNorm c)
    rw [abs_mul, ← abs_mul_abs_self A.det]
    calc |A.det| * |(A.updateCol k c).det| ≤ |A.det| * (‖f‖ * ‖c‖) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = _ := by field_simp

theorem weighted_least_squares_bound : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g →
    ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤
        K * ‖b‖ := by
  intro M g L hL
  choose K hK0 hK using fun S : {S : Finset (Fin M) // S.card = g} =>
    block_bound (L.submatrix (S.1.orderEmbOfFin S.2) id)
  refine ⟨∑ S, K S, fun D b hD => ?_⟩
  have hKs : 0 ≤ ∑ S, K S := Finset.sum_nonneg fun S _ => hK0 S
  have hdet := det_pos L hL D hD
  set A := L.transpose * Matrix.diagonal D * L with hA
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  have hx : A.det * (A⁻¹ * L.transpose * Matrix.diagonal D).mulVec b k =
      (L.transpose * Matrix.diagonal D * L.updateCol k b).det := by
    have h1 := Matrix.det_smul_inv_mulVec_eq_cramer A ((L.transpose * Matrix.diagonal D).mulVec b)
      (isUnit_iff_ne_zero.mpr hdet.ne')
    have h2 := congrFun h1 k
    rw [Matrix.cramer_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at h2
    rw [← smul_eq_mul, ← Pi.smul_apply, h2]
    congr 1
    ext i j
    by_cases hj : j = k
    · subst hj
      simp [Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.mulVec, dotProduct]
    · simp [hA, Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.updateCol_ne hj]
  have hb : |(L.transpose * Matrix.diagonal D * L.updateCol k b).det| ≤
      (∑ S, K S) * ‖b‖ * A.det := by
    rw [hA, det_eq_sum, det_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    set e := S.1.orderEmbOfFin S.2 with he
    have hp : 0 ≤ ∏ j, D (e j) := Finset.prod_nonneg fun j _ => (hD _).le
    have hu : (L.updateCol k b).submatrix e id = (L.submatrix e id).updateCol k (b ∘ e) := by
      ext i j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Matrix.updateCol_ne hj]
    have hn : ‖b ∘ e‖ ≤ ‖b‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm b (e i)
    have hKS : K S ≤ ∑ S, K S :=
      Finset.single_le_sum (f := K) (fun S _ => hK0 S) (Finset.mem_univ S)
    rw [abs_mul, abs_of_nonneg hp, hu, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ((hK S (b ∘ e) k).trans ?_) hp
    exact mul_le_mul_of_nonneg_right (mul_le_mul hKS hn (norm_nonneg _) hKs) (mul_self_nonneg _)
  rw [← hx, abs_mul, abs_of_pos hdet, mul_comm] at hb
  exact le_of_mul_le_mul_right hb hdet

end GlobalTheory.WeightedLS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFormulaFourierQuadraticCharacter
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.WeilFormula

theorem setIntegral_addSubgroup_add_right {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (g : V → ℂ)
    {t : V} (ht : t ∈ L) :
    ∫ z in (L : Set V), g (z + t) ∂μ = ∫ z in (L : Set V), g z ∂μ := by
  simp_rw [add_comm _ t]
  rw [← integral_indicator hLo.measurableSet, ← integral_indicator hLo.measurableSet,
    ← integral_add_left_eq_self (μ := μ) ((L : Set V).indicator g) t]
  congr 1
  funext z
  by_cases hz : z ∈ L
  · rw [Set.indicator_of_mem (show z ∈ (L : Set V) from hz),
      Set.indicator_of_mem (show t + z ∈ (L : Set V) from L.add_mem ht hz)]
  · have hz' : t + z ∉ L := fun h => hz ((L.add_mem_cancel_left ht).1 h)
    rw [Set.indicator_of_notMem (show z ∉ (L : Set V) from hz),
      Set.indicator_of_notMem (show t + z ∉ (L : Set V) from hz')]

theorem weil_formula : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ (f g : X → ℂ) (s : X → X) (γ : ℂ), Continuous f → Continuous s →
    (∀ y u, f y * e y u = g u * f (y + s u)) → HasGauss μ f γ → ∀ φ ∈ SB X, ∀ x,
    four μ e (fun y => f y * four μ e φ y) x = γ * ∫ z, g (x + z) * φ z ∂μ := by
  intro X _ _ _ _ hG μ _ e he f g s γ hf hs hfg hga φ hφ x
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hφ4 : four μ e φ ∈ SB X := _root_.GlobalTheory.KSp.FourMem.four_mem_SB X hG μ e he φ hφ
  have hK1 : IsCompact (tsupport (four μ e φ)) := hφ4.2
  have hφc : IsCompact (tsupport φ) := hφ.2
  have hK2 : IsCompact (s '' ((fun z => x + z) '' tsupport φ)) :=
    (hφc.image (continuous_const.add continuous_id)).image hs
  obtain ⟨L, hLc, hLo, hKL, hLγ⟩ := hga _ (hK1.union hK2)
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have he_cont : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hφcont : Continuous φ := hφ.1.continuous
  have h0 : ∀ y, y ∉ (L : Set X) → e x y * (f y * four μ e φ y) = 0 := by
    intro y hy
    have : four μ e φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hKL (Or.inl h)))
    simp [this]
  have h1 : four μ e (fun y => f y * four μ e φ y) x
      = ∫ y in (L : Set X), ∫ z, e x y * f y * (e y z * φ z) ∂μ ∂μ := by
    calc four μ e (fun y => f y * four μ e φ y) x = ∫ y, e x y * (f y * four μ e φ y) ∂μ := rfl
      _ = ∫ y in (L : Set X), e x y * (f y * four μ e φ y) ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = _ := by
          congr 1; funext y
          simp only [four]
          rw [← mul_assoc, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
      ((μ.restrict (L : Set X)).prod μ) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hc : Continuous (Function.uncurry fun y z => e x y * f y * (e y z * φ z)) := by
      have h1' : Continuous fun p : X × X => e x p.1 := he_cont.comp (continuous_const.prodMk continuous_fst)
      exact (h1'.mul (hf.comp continuous_fst)).mul (he_cont.mul (hφcont.comp continuous_snd))
    have hon : IntegrableOn (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
        ((L : Set X) ×ˢ tsupport φ) (μ.prod μ) := hc.continuousOn.integrableOn_compact (hLc.prod hφc)
    refine hon.of_forall_sdiff_eq_zero (hLm.prod MeasurableSet.univ) ?_
    rintro ⟨y, z⟩ ⟨⟨hy, -⟩, hn⟩
    have hz : z ∉ tsupport φ := fun h => hn ⟨hy, h⟩
    simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  have h3 : ∀ z, ∫ y in (L : Set X), e x y * f y * (e y z * φ z) ∂μ = γ * (g (x + z) * φ z) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzt : z ∈ tsupport φ := subset_tsupport _ hz
      have hsL : s (x + z) ∈ L := hKL (Or.inr ⟨x + z, ⟨z, hzt, rfl⟩, rfl⟩)
      have hpt : ∀ y, e x y * f y * (e y z * φ z) = φ z * g (x + z) * f (y + s (x + z)) := by
        intro y
        have hexy : e x y * e y z = e y (x + z) := by
          rw [he.symm y (x + z), he.add, he.symm z y]
        rw [mul_assoc (φ z), ← hfg y (x + z), ← hexy]; ring
      simp_rw [hpt]
      rw [integral_const_mul, setIntegral_addSubgroup_add_right μ L hLo f hsL, hLγ]; ring
  rw [h1, integral_integral_swap hint]
  simp_rw [h3]
  rw [integral_const_mul]

end GlobalTheory.KSp.WeilFormula
end

