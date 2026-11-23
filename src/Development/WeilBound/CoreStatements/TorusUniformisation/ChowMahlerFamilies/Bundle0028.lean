module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TateIsomorphismDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.TateIsomorphismDescent

theorem exists_weilIs (S : Scheme.{0}) (P : Out.PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (hx : x ^ k = 1)
    (hy : y ^ k = 1) : ∃ c : Γ(T.left, ⊤)ˣ, Out.WeilIs P.A P.L k x y c :=
  (GlobalTheory.CommutatorPairing.existsUnique_weilIs GlobalTheory.abelianSchemeLaws_all.1.globalFns
    (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2
    S P k T x y hx hy).exists

theorem exists_root {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) {n : ℕ} (hn : 0 < n) (z : Ωˣ)
    (hz : z ^ n = 1) : ∃ w : Kˣ, Units.map i.toMonoidHom w = z := by
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial K).Splits := IsAlgClosed.splits _
  have hne : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial K) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn 1
  have hm : (z : Ω) ∈ ((Polynomial.X ^ n - Polynomial.C 1 : Polynomial K).map i).roots := by
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne)]
    simp [hz']
  rw [hs.roots_map_of_injective i.injective] at hm
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hm
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact z.ne_zero (hw.symm.trans (map_zero i))
  exact ⟨Units.mk0 w hw0, Units.ext hw⟩

end PositivityTheory.Xgn.TateIsomorphismDescent

theorem PositivityTheory.Xgn.tate_isomorphism_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)), (∀ c, IsMonHom (act c)) → ∀ (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) (x' : Sp Ω ⟶ S) (u : Over.mk x' ⟶ Over.mk x), u.left = spMap i → ∀ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n v, 0 < n → I'.ev n v = u ≫ I.ev n v := by
  intro E _ _ _ H D S P act hact K Ω _ _ _ _ _ i x x' u hu I'
  have laws := GlobalTheory.abelianSchemeLaws_all.1
  have : CharZero Ω := (RingHom.charZero_iff i.injective).1 ‹_›
  let f : (Over.mk x ⟶ P.A) →* (Over.mk x' ⟶ P.A) := MonoidHom.mk' (u ≫ ·) (MonObj.comp_mul u)
  have hinj : Function.Injective f := GlobalTheory.TorsionFieldExt.comp_injective u P.A
  have ginj : Function.Injective (Units.map i.toMonoidHom : Kˣ →* Ωˣ) := Units.map_injective i.injective
  have hu' : ∀ c : Kˣ, unitOn (Units.map i.toMonoidHom c) = Units.map u.left.appTop.hom.toMonoidHom (unitOn c) :=
    fun c => by
      rw [hu]
      exact Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)))
  have hev : ∀ (n : ℕ) (v : D.La), ∃ y : Over.mk x ⟶ P.A, (n = 0 → y = 1) ∧ (0 < n → f y = I'.ev n v) := by
    intro n v
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun _ => rfl, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨y, -, hy⟩ := GlobalTheory.TorsionFieldExt.exists_of_isAlgClosed laws P u (Nat.cast_ne_zero.2 hn.ne')
        (Nat.cast_ne_zero.2 hn.ne') (I'.ev n v) ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun h => absurd h hn.ne', fun _ => hy⟩
  choose ev ev0 evp using hev
  have hζ : ∀ n : ℕ, ∃ w : Kˣ, 0 < n → Units.map i.toMonoidHom w = I'.ζ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨w, hw⟩ := PositivityTheory.Xgn.TateIsomorphismDescent.exists_root i hn (I'.ζ n) (I'.ζ_prim n hn).pow_eq_one
      exact ⟨w, fun _ => hw⟩
  choose ζ hζ using hζ
  have tors : ∀ n, 0 < n → ∀ a, ev n a ^ n = 1 := fun n hn a => hinj (by
    rw [map_pow, evp n a hn, map_one]; exact (I'.onto n hn _).2 ⟨a, rfl⟩)
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => IsPrimitiveRoot.of_map_of_injective (f := (Units.map i.toMonoidHom : Kˣ →* Ωˣ))
              (by rw [hζ n hn]; exact I'.ζ_prim n hn) ginj
            ζ_pow := fun n m hn hm => ginj (by
              rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm])
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← evp n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => hinj (by
              rw [map_pow, evp _ a (Nat.mul_pos hn hm), evp n a hn, I'.tower n m hn hm])
            isom := fun n hn a b => ?_ }, fun n v hn => (evp n v hn).symm⟩
  · rcases Nat.eq_zero_or_pos n with h | hn
    · rw [ev0 n _ h, ev0 n _ h, ev0 n _ h, _root_.mul_one]
    · exact hinj (by rw [map_mul, evp n _ hn, evp n _ hn, evp n _ hn, I'.add])
  · rcases Nat.eq_zero_or_pos n with h | hn
    · have := hact c
      rw [ev0 n _ h, ev0 n _ h]
      exact (MonObj.one_comp (act c)).symm
    · refine hinj ?_
      rw [evp n _ hn, I'.lin, ← evp n a hn]
      exact Category.assoc u (ev n a) (act c)
  · obtain ⟨a, ha⟩ := (I'.onto n hn (f z)).1 (by rw [← map_pow, hz, map_one])
    exact ⟨a, hinj ((evp n a hn).trans ha)⟩
  · rintro ⟨a, rfl⟩
    exact tors n hn a
  · obtain ⟨c, hc⟩ := PositivityTheory.Xgn.TateIsomorphismDescent.exists_weilIs S P n _ _ _ (tors n hn a) (tors n hn b)
    obtain ⟨w, rfl⟩ : ∃ w : Kˣ, unitOn w = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val)⟩
    have h₁ := GlobalTheory.CommPairing.weilIs_pull laws.globalFns P.isAb P.isLB u hc
    rw [← hu'] at h₁
    have h₂ := I'.isom n hn a b
    rw [← evp n a hn, ← evp n b hn, ← hζ n hn, ← map_zpow] at h₂
    have e := ginj (GlobalTheory.weilIs_unique_fieldPoint S P.A P.L P.isLB Ω x' n _ _ _ _ h₁ h₂)
    rw [← e]
    exact hc
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorsionFieldOfDefinition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.TorsionFieldOfDefinition

theorem exists_field_alg (C : Type) [CommRing C] [Algebra ℚ C] [Module.Finite ℚ C] :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ ∀ (ψ : C →+* ℂ) (c : C), ψ c ∈ F := by
  classical
  have hint : ∀ c : C, IsIntegral ℚ c := fun c => Algebra.IsIntegral.isIntegral c
  let bs := Module.finBasis ℚ C
  let S : Finset ℂ := Finset.univ.biUnion (fun i => ((minpoly ℚ (bs i)).aroots ℂ).toFinset)
  have hroot : ∀ (ψ : C →+* ℂ) i, ψ (bs i) ∈ S := by
    intro ψ i
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset]
    refine ⟨i, Polynomial.mem_aroots.mpr ⟨minpoly.ne_zero (hint _), ?_⟩⟩
    have h := Polynomial.aeval_algHom_apply ψ.toRatAlgHom (bs i) (minpoly ℚ (bs i))
    rw [minpoly.aeval, map_zero] at h
    exact h
  refine ⟨IntermediateField.adjoin ℚ (S : Set ℂ), ?_, ?_⟩
  · apply IntermediateField.finiteDimensional_adjoin
    intro z hz
    have hz' : z ∈ S := hz
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset] at hz'
    obtain ⟨i, hzi⟩ := hz'
    obtain ⟨-, hz0⟩ := Polynomial.mem_aroots.mp hzi
    exact ⟨minpoly ℚ (bs i), minpoly.monic (hint _), by rwa [← Polynomial.aeval_def]⟩
  · intro ψ c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← bs.sum_repr c, map_sum]
    refine sum_mem (fun i _ => ?_)
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (IntermediateField.subset_adjoin ℚ _ (hroot ψ i))

theorem exists_field_ring (L : Type) [Field L] [NumberField L] (B : Type) [CommRing B]
    (φ : L →+* B) (hφ : φ.Finite) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ (∀ (σ : L →+* ℂ) (c : L), σ c ∈ F) ∧
      ∀ (ψ : B →+* ℂ) (c : B), ψ c ∈ F := by
  letI : Algebra L B := φ.toAlgebra
  letI : Algebra ℚ B := (φ.comp (algebraMap ℚ L)).toAlgebra
  haveI : IsScalarTower ℚ L B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite L B := hφ
  haveI : Module.Finite ℚ B := Module.Finite.trans L B
  obtain ⟨F₁, hF₁, h₁⟩ := exists_field_alg L
  obtain ⟨F₂, hF₂, h₂⟩ := exists_field_alg B
  haveI := hF₁
  haveI := hF₂
  exact ⟨F₁ ⊔ F₂, inferInstance, fun σ c => le_sup_left (a := F₁) (h₁ σ c),
    fun ψ c => le_sup_right (a := F₁) (h₂ ψ c)⟩

theorem exists_field_scheme (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (W : Scheme.{0})
    (p : W ⟶ Sp L) [IsFinite p] :
    ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F),
      (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ w : Sp ℂ ⟶ W, w ≫ p = spMap σ →
        ∃ y : Sp F ⟶ W, y ≫ p = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = w := by
  haveI : IsAffine W := isAffine_of_isAffineHom p
  obtain ⟨q, hq⟩ : ∃ q : CommRingCat.of L ⟶ Γ(W, ⊤), Spec.map q = W.isoSpec.inv ≫ p :=
    ⟨_, Spec.map_preimage _⟩
  have hfin : q.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hq]
    infer_instance
  obtain ⟨F, hF, hσF, hψF⟩ := exists_field_ring L Γ(W, ⊤) q.hom hfin
  refine ⟨F, hF, σ.codRestrict F (hσF σ), fun x => rfl, fun w hw => ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(W, ⊤) ⟶ CommRingCat.of ℂ, Spec.map g = w ≫ W.isoSpec.hom :=
    ⟨_, Spec.map_preimage _⟩
  let gF : Γ(W, ⊤) →+* F := g.hom.codRestrict F (hψF g.hom)
  refine ⟨Spec.map (CommRingCat.ofHom gF) ≫ W.isoSpec.inv, ?_, ?_⟩
  · have hqg : q ≫ g = CommRingCat.ofHom σ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, hq]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact hw
    dsimp only [spMap]
    rw [Category.assoc, ← hq, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg (fun f : CommRingCat.of L ⟶ CommRingCat.of ℂ => f.hom x) hqg
  · dsimp only [spMap]
    rw [← Category.assoc, ← Spec.map_comp]
    have hc : CommRingCat.ofHom gF ≫ CommRingCat.ofHom (algebraMap F ℂ) = g := by
      ext x
      rfl
    rw [hc, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end PositivityTheory.Xgn.TorsionFieldOfDefinition

private theorem comp_mulN_lemma {S : Scheme} {G : Over S} [GrpObj G] {X : Over S} (x : X ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, Hom.one_def]
    show x ≫ (toUnit G ≫ η) = _
    rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  | succ k ih =>
    rw [pow_succ, Hom.mul_def, ← ih]
    show x ≫ (CartesianMonoidalCategory.lift (mulN G k) (𝟙 G) ≫ μ) = _
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id]

theorem PositivityTheory.Xgn.torsion_field_of_definition : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left := by
  intro L _ _ σ P n hn
  haveI := P.isAb.comm
  haveI := P.isAb.smooth
  haveI := P.isAb.proper
  have hu : IsUnit ((n : ℕ) : Γ(Sp L, ⊤)) := by
    have h0 : IsUnit ((n : ℕ) : L) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
    have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
    rwa [map_natCast] at h1
  haveI hfin : IsFinite (torsion P.A n).hom := GlobalTheory.GrpTangent.isFinite_torsion P.A hu
  obtain ⟨F, hF, e, he, hlift⟩ :=
    PositivityTheory.Xgn.TorsionFieldOfDefinition.exists_field_scheme L σ (torsion P.A n).left (torsion P.A n).hom
  refine ⟨F, hF, e, he, fun x hx => ?_⟩
  have hx' : x ≫ mulN P.A n = (toUnit _ ≫ η : Over.mk (spMap σ) ⟶ P.A) := by
    rw [comp_mulN_lemma, hx, Hom.one_def]
  let t : Over.mk (spMap σ) ⟶ torsion P.A n := pullback.lift x (toUnit _) hx'
  obtain ⟨y, hy1, hy2⟩ := hlift t.left (Over.w t)
  refine ⟨y ≫ (torsion.ι P.A n).left, ?_, ?_⟩
  · rw [Category.assoc, Over.w (torsion.ι P.A n), hy1]
  · rw [← Category.assoc, hy2, ← Over.comp_left]
    congr 1
    exact pullback.lift_fst _ _ _
end

