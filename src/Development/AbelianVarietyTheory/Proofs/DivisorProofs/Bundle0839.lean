module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0455
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealUnitaryCovolumeSum
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUVolBound
theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_inReal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) (fun a b h => Units.ext h)
  have hsub : ∀ y : inReal Ψ G Γ, ∃ γ : GL (Fin r) E, embGL Ψ r γ = (y : realSU Ψ G).1 := by
    rintro ⟨y, hy⟩
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨γ, hγ⟩
  choose f hf using hsub
  refine Function.Injective.countable (f := f) fun a b hab => ?_
  apply Subtype.ext; apply Subtype.ext
  rw [← hf a, ← hf b, hab]

theorem tangentHaar_smul {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H]
    [MeasurableSpace H] [BorelSpace H] (c : ℝ≥0∞) (hc : c ≠ ⊤) (ν : Measure (ι → Fin r → Fin r → ℂ)) :
    tangentHaar H (c • ν) = c • tangentHaar H ν := by
  unfold tangentHaar
  rw [smul_smul]
  congr 1
  simp only [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  exact ENNReal.limsup_const_mul_of_ne_top hc

theorem covolume_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
    [MeasurableConstSMul G α] (ν : Measure α) [SMulInvariantMeasure G α ν] (c : ℝ≥0∞) (hc : c ≠ 0) :
    covolume G α (c • ν) = c * covolume G α ν := by
  by_cases h : HasFundamentalDomain G α ν
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' : IsFundamentalDomain G s (c • ν) := hs.mono (Measure.smul_absolutelyContinuous)
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]
  · have h' : ¬ HasFundamentalDomain G α (c • ν) := by
      rintro ⟨⟨s, hs⟩⟩
      exact h ⟨⟨s, hs.mono (Measure.absolutelyContinuous_smul hc)⟩⟩
    simp [covolume, h, h']

theorem abs_discr_real_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) :
    |(discr (maximalRealSubfield E) : ℝ)| = rdE E ^ fdeg E := by
  have hdiff : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top _ E).1 (by
      haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hU; infer_instance)
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  rw [hdiff, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  simp only [Ideal.absNorm_top, one_mul] at h
  have hd : dE E = |(discr (maximalRealSubfield E) : ℝ)| ^ 2 := by
    unfold dE
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
    push_cast; ring
  have hf : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  rw [rootDiscriminant_eq_rpow, hd, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _)]
  have : (((2 : ℕ) : ℝ) * (1 / (2 * (fdeg E : ℝ))) * (fdeg E : ℝ)) = 1 := by
    field_simp; norm_num
  rw [this, Real.rpow_one]

theorem exists_lie_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : SelfDualLat G Λ) :
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, e i ∈ lieLat G Λ) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨e, he, hli⟩ := _root_.GlobalTheory.suLie_finrank_ge G hΛ.1 hΛ.2.1
  choose N hN hmem using fun i => _root_.GlobalTheory.DenClear.exists_natSmul_mem_lieLat G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2
  refine ⟨fun i => (N i : E) • e i, hmem, ?_⟩
  let w : Fin (r ^ 2 - 1) → (maximalRealSubfield E)ˣ :=
    fun i => Units.mk0 (N i : maximalRealSubfield E) (by exact_mod_cast (hN i).ne')
  have hw : (fun i => (N i : E) • e i) = w • e := by
    funext i
    ext a b
    simp [w, Algebra.smul_def]
  rw [hw]
  exact hli.units_smul w

theorem sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → IsSReps X.Gm (Λ : Set (Fin r → E)) 1 s → ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) ≤ ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r X Λ x _ _ J s hr hU hΛ hx hs
  obtain ⟨e, he, hli⟩ := exists_lie_basis X.Gm Λ hΛ
  obtain ⟨hmult, hP1⟩ := hP E r X.Gm Λ X.Ψ e J s hr hU hΛ X.cmType he hli hs
  have hlie := _root_.GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie E r X Λ x e hr hU hΛ hx he hli
  obtain ⟨hPpos, hPinv⟩ := _root_.GlobalTheory.EulerLocVol.tprod_locFactor_bound E r hr hmult
  set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex
    (lieLat X.Gm Λ) : ℝ) with hm
  set P : ℝ := ∏' v, locFactor E r v with hPdef
  set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ
  set n : ℝ := (r : ℝ) ^ 2 - 1 with hn
  set μ := tangentHaar (realSU X.Ψ X.Gm) (formLie X.Ψ e) with hμ
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ fdeg E * m) with hc
  have hDpos : 0 < D := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero] at hP1
      exact zero_ne_one hP1
  have hr0 : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))
  have hcpos : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hriem : riemHaar X.Ψ X.Gm x = c • μ := by
    unfold riemHaar
    rw [hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]
  have hcov : ∀ j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm)
      (riemHaar X.Ψ X.Gm x) = c * covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j)))
      (realSU X.Ψ X.Gm) μ := by
    intro j
    haveI := countable_inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))
    rw [hriem, covolume_smul _ _ hcpos]
  simp_rw [hcov]
  rw [ENNReal.tsum_mul_left]
  set S := ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) μ
    with hS
  have ha : 0 < D ^ (-n / 2) * m * P := by positivity
  have hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos ha]
    exact (ENNReal.eq_inv_of_mul_eq_one_left hP1)
  rw [hS1, hc, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hDr : D = rdE E ^ fdeg E := abs_discr_real_eq hU
  have hrd0 : 0 ≤ rdE E := by
    unfold rdE; exact Real.rpow_nonneg (abs_nonneg _) _
  have hDn : D ^ (n / 2) = rdE E ^ ((fdeg E : ℝ) * n / 2) := by
    rw [hDr, ← Real.rpow_natCast, ← Real.rpow_mul hrd0, mul_div_assoc]
  have key : Real.sqrt r ^ fdeg E * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ fdeg E * P⁻¹ := by
    rw [neg_div, Real.rpow_neg hDpos.le]
    have : D ^ (n / 2) ≠ 0 := (Real.rpow_pos_of_pos hDpos _).ne'
    field_simp
  rw [key, hDn, mul_pow, mul_assoc]
  gcongr

end GlobalTheory.SUVolBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionAction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace TorusActRing

theorem chV_id_eq {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ : X) :
    chV (𝟙 (splitTorus (Sp k) X)) χ = charUnit (Sp k) X χ := by
  ext1
  rw [chV_val]
  simp

theorem charUnit_add' {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ ψ : X) :
    charUnit (Sp k) X (χ + ψ) = charUnit (Sp k) X χ * charUnit (Sp k) X ψ := by
  rw [← chV_id_eq, ← chV_id_eq, ← chV_id_eq, chV_add]

end TorusActRing

theorem ringHom_charEnd_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  intro k _ G _ _ E O _ act hmon h1 hmul hadd
  letI := E.addCommGroup
  have hex := fun a => GlobalTheory.TorusEndChar.main k G E (act a) (hmon a)
  choose ρ₀ hρ₀ using fun a => (hex a).exists
  have uniq : ∀ a (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      τ ≫ E.i = E.i ≫ act a → (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → σ = ρ₀ a :=
    fun a σ τ e₁ e₂ => (hex a).unique ⟨τ, e₁, e₂⟩ (hρ₀ a)
  have compχ : ∀ (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → ∀ (Z : Over (Sp k)) (s : Z ⟶ splitTorus (Sp k) E.X) χ,
      chV (s ≫ τ) χ = chV s (σ χ) :=
    fun σ τ hτ Z s χ => ((splitTorus_map_of_charHom (Sp k) E.X E.X σ).2 τ hτ).2.2 Z s χ
  have one : ρ₀ 1 = AddMonoidHom.id _ := by
    refine (uniq 1 (AddMonoidHom.id _) (𝟙 _) ?_ (fun χ => ?_)).symm
    swap
    · rw [AddMonoidHom.id_apply]; exact TorusActRing.chV_id_eq E.X χ
    rw [h1, Category.id_comp, Category.comp_id]
  have mul : ∀ a b, ρ₀ (a * b) = (ρ₀ a).comp (ρ₀ b) := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    refine (uniq (a * b) _ (τa ≫ τb) ?_ ?_).symm
    · rw [Category.assoc, hb1, ← Category.assoc, ha1, Category.assoc, hmul]
    · intro χ
      rw [compχ _ τb hb2, ha2]
      rfl
  have add : ∀ a b, ρ₀ (a + b) = ρ₀ a + ρ₀ b := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    haveI := E.i_hom
    refine (uniq (a + b) _ (τa * τb) ?_ ?_).symm
    · rw [MonObj.mul_comp, ha1, hb1, hadd, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]
    · intro χ
      rw [chV_mul, ha2, hb2, AddMonoidHom.add_apply, TorusActRing.charUnit_add']
  have zero : ρ₀ 0 = 0 := by
    have := add 0 0
    rw [add_zero] at this
    simpa using this
  refine ⟨{ toFun := fun a => (ρ₀ a).toIntLinearMap
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun a => ?_⟩
  · ext x; simp [one]
  · intro a b; ext x; simp [mul]
  · ext x; simp [zero]
  · intro a b; ext x; simp [add]
  · obtain ⟨τ, e₁, e₂⟩ := hρ₀ a
    exact ⟨τ, e₁, fun χ => e₂ χ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallOfSeparatedPresheafOpenCharts
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem small_of_separated_of_open_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ T : Scheme.{0}ᵒᵖ, Small.{0} (F.obj T) := by
  intro F hsep Ix U x hchart hcov T
  let S : F.obj T → Set (Σ (i : Ix) (V : T.unop.Opens), (V.toScheme ⟶ U i)) :=
    fun y => {q | F.map q.2.1.ι.op y = F.map q.2.2.op (x q.1)}
  refine small_of_injective (f := S) ?_
  intro y y' h
  apply hsep T.unop y y'
  intro p
  obtain ⟨i, Y, a, u, hp, ha⟩ := hcov T.unop y p
  obtain ⟨W, hW⟩ := hchart i T.unop y
  have hpW : p ∈ W := by
    obtain ⟨q, rfl⟩ := hp
    exact (hW Y a).1 ⟨u, ha⟩ q
  obtain ⟨u', hu'⟩ := (hW W.toScheme W.ι).2 (fun q => by
    have hq : W.ι q ∈ Set.range W.ι := Set.mem_range_self q
    rwa [W.range_ι] at hq)
  have hmem : (⟨i, W, u'⟩ : Σ (i : Ix) (V : T.unop.Opens), (V.toScheme ⟶ U i)) ∈ S y := hu'
  rw [h] at hmem
  refine ⟨W.toScheme, W.ι, inferInstance, ?_, ?_⟩
  · rw [W.range_ι]; exact hpW
  · exact hu'.trans hmem.symm

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.TensorDualDim

theorem finrank_dual_eq (O X : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    Module.finrank O (Module.Dual O X) = Module.finrank O X := by
  haveI : Module.FinitePresentation O X := Module.finitePresentation_of_projective O X
  let F := FractionRing O
  let f : X →ₗ[O] F ⊗[O] X := TensorProduct.mk O F X 1
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl
  let g := IsLocalizedModule.map (nonZeroDivisors O) f (Algebra.linearMap O F)
  have h2 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl
  rw [← h1, ← h2, ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    (LinearMap.extendScalarsOfIsLocalizationEquiv (nonZeroDivisors O) F).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem smoothOfRelativeDimension_tensorObj_dual : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (tensorObj (Module.Dual O X) a).hom := by
  intro S B _ _ O _ _ _ a X _ _ _ _ g hg
  have h := GlobalTheory.SerreDim.smoothOfRelativeDimension_tensor S O (Module.Dual O X) B
    (tensorObj (Module.Dual O X) a) a (tensorAct (Module.Dual O X) a) g
    ⟨GlobalTheory.Serre.isTensor (Module.Dual O X) a⟩ hg
  rwa [finrank_dual_eq] at h

end GlobalTheory.TensorDualDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymm
section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.SphPar

theorem dualLab_splitLab_getD (n k : ℕ) (i : ℕ) :
    (dualLab (splitLab n k)).getD i 0 = if i < k then 1 else 0 := by
  have h : dualLab (splitLab n k) = List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0 := by
    simp [dualLab, splitLab]
  rw [h]
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem diagonal_dualLab_splitLab {L : Type} [Field L] (n k : ℕ) (ϖ : L) :
    Matrix.diagonal (fun i : Fin n => ϖ ^ (dualLab (splitLab n k)).getD i 0) = diagJ n ϖ k := by
  unfold diagJ
  congr 1
  funext i
  rw [dualLab_splitLab_getD]
  split_ifs <;> simp

theorem Tj_eq_of_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ ϖ' : P.adicCompletion E} (h : IsUnifV E P ϖ) (h' : IsUnifV E P ϖ') :
    Tj ℂ n (Ov E P) ϖ' k = Tj ℂ n (Ov E P) ϖ k := by
  unfold IsUnifV at h h'
  have hv0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  have hv0' : Valued.v ϖ' ≠ 0 := by rw [h']; exact WithZero.coe_ne_zero
  have h0 : ϖ ≠ 0 := fun e => hv0 (by rw [e, map_zero])
  have h0' : ϖ' ≠ 0 := fun e => hv0' (by rw [e, map_zero])
  have hu : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, h', ← h, div_self hv0]
  have e : ϖ' = ϖ' / ϖ * ϖ := (div_mul_cancel₀ _ h0).symm
  rw [e]
  refine Final.TjIndep _ _ _ _ _ _ _ ?_ ?_ (div_ne_zero h0' h0)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hu, inv_one])

theorem divInd_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ : P.adicCompletion E} (h : IsUnifV E P ϖ) :
    divInd (n := n) (Ov E P) (dualLab (splitLab n k)) = Tj ℂ n (Ov E P) ϖ k := by
  funext g
  by_cases hg : HasDiv (Ov E P) (dualLab (splitLab n k)) g
  · obtain ⟨ϖ', h', hab⟩ := id hg
    rw [diagonal_dualLab_splitLab] at hab
    rw [← Tj_eq_of_isUnifV E P n k h h', divInd, Tj, Set.indicator_of_mem (by exact hg),
      Set.indicator_of_mem (by exact hab)]
  · rw [divInd, Tj, Set.indicator_of_notMem (by exact hg), Set.indicator_of_notMem]
    intro hab
    refine hg ⟨ϖ, h, ?_⟩
    rw [diagonal_dualLab_splitLab]
    exact hab

end GlobalTheory.SphPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEquivLocPart
section
namespace GlobalTheory.FinTrace

theorem stabilizer_equiv_locPart : ∀ (G : Type) [Group G] (H K : Subgroup G) (x : G),
    Nonempty (MulAction.stabilizer H (QuotientGroup.mk x : G ⧸ K) ≃ GlobalTheory.LKLoc.locPart H K x) := by
  intro G _ H K x
  have hmem : ∀ h : H, h ∈ MulAction.stabilizer H (QuotientGroup.mk x : G ⧸ K) ↔
      (h : G) ∈ GlobalTheory.LKLoc.locPart H K x := by
    intro h
    rw [MulAction.mem_stabilizer_iff]
    show ((h : G) • (QuotientGroup.mk x : G ⧸ K)) = _ ↔ _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    simp only [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      SetLike.coe_mem, true_and]
    constructor
    · intro hk
      refine ⟨_, K.inv_mem hk, ?_⟩
      group
    · rintro ⟨k, hk, e⟩
      rw [← e]
      convert K.inv_mem hk using 1
      group
  exact ⟨{ toFun := fun h => ⟨h.1, (hmem h.1).1 h.2⟩
           invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hmem _).2 g.2⟩
           left_inv := fun h => rfl
           right_inv := fun g => rfl }⟩

theorem finite_support_conj : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (f : G → ℂ), (∀ k ∈ K, ∀ g, f (g * k) = f g) →
    (Function.support fun q : G ⧸ K => f (Quotient.out q)).Finite → ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x) →
    (Function.support fun γ : Γ => f (x⁻¹ * γ * x)).Finite := by
  intro G _ Γ K f hR hs x hx
  let π : Γ → G ⧸ K := fun γ => QuotientGroup.mk (x⁻¹ * γ * x)
  have hmaps : Set.MapsTo π (Function.support fun γ : Γ => f (x⁻¹ * γ * x)) (Function.support fun q : G ⧸ K => f q.out) := by
    intro γ hγ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (x⁻¹ * γ * x)
    simp only [Function.mem_support, π, hk, hR _ k.2] at hγ ⊢
    exact hγ
  refine Set.Finite.of_finite_fibers π (hs.subset (Set.image_subset_iff.2 hmaps)) ?_
  haveI := hx
  intro q _
  by_cases hne : (π ⁻¹' {q}).Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hne
    have hsub : π ⁻¹' {q} ⊆ (fun l : GlobalTheory.LKLoc.locPart Γ K x => γ₀ * ⟨l.1, l.2.1⟩) '' Set.univ := by
      intro γ hγ
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hγ hγ₀
      have h := hγ₀.trans hγ.symm
      rw [QuotientGroup.eq] at h
      refine ⟨⟨(γ₀⁻¹ * γ : Γ), (γ₀⁻¹ * γ : Γ).2, ?_⟩, trivial, Subtype.ext (by simp)⟩
      refine ⟨_, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact ((Set.finite_univ.image _).subset hsub).subset Set.inter_subset_right
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.inter_empty]
    exact Set.finite_empty

end GlobalTheory.FinTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegral
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem psiFin_superDiag_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) →
    u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  intro E _ _ _ n u _ hk
  have hent := ((GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hk).1
  have hs : GlobalTheory.Whittaker.superDiag u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    unfold GlobalTheory.Whittaker.superDiag
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => hent i j
  have hd : sFin E (GlobalTheory.Whittaker.superDiag u) ∈ GroundTheory.Global.invDifferentAdeles E :=
    GroundTheory.Global.mem_invDifferentAdeles.mpr
      (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hs)
  unfold psiFin
  rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hd]
  have h0 : (sFin E (GlobalTheory.Whittaker.superDiag u)).1 = 0 := rfl
  rw [h0, map_zero, neg_zero, AddChar.map_zero_eq_one]
  simp

end GlobalTheory.WhitBump
end

