module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

theorem exists_uniformisation_at_point : ThetaUnifAV → Out.Laws → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF → (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) → (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') ∧ (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT _ _ hPull hPol hDat E _ _ _ H D l Xo σ g ty _ hσ hty y hy
  let b' : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  obtain ⟨o, ⟨m⟩⟩ := hPull E H D l (KA l) ℂ (baseKA l) b' σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨hab, hsm, hrig, hsym⟩ := hPol E H D l ℂ b' (Sp ℂ) (𝟙 _) o
  obtain ⟨rig, hr⟩ := id hrig
  obtain ⟨u, Hm, χ, Ef, hAH, -, h1, h2, hF, -, hE, hbij, hweil⟩ :=
    hT { A := o.t.G, isAb := hab, g := _, smoothDim := hsm, L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := hrig,
         sym := hsym, ample := o.ample, ktriv := o.ktriv } rig hr
  have hLiso : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push m.cart (𝟙_ _)
    (weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ Xo.univ.t.PP.isLB o.t.PP.isLB m.cart hLiso _) y (Category.id_comp y)
  have he₀ := isExp_push m.cart u h1 h2 Φ hΦ
  have hker₀ : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep Xo.univ.t.act u.Λ u.discrete hker₀ fun a => by
    obtain ⟨F, hF⟩ := hF (o.t.act.act a) (o.t.act.hom a)
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    rw [hΦ, hF, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  obtain ⟨hdet, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ y σ hy
  obtain ⟨h, hh⟩ := exists_equiv_of_finrank_eq (isSplitting_embeddings (E := E)) (diagRep ty) ρ fun φ => by
    rw [finrank_eigenSub_diagRep]
    by_cases hφ : φ (H.rt : E) = H.rt0
    · rw [(hty φ).1 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).1 (hφ.trans hσ.symm))]
    · rw [(hty φ).2 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).2 fun h => hφ (h.trans hσ))]
  have he := he₀.comp_equiv h
  have hlin : ∀ (a : 𝓞 E) z, Φ (u.ex (h fun k => ty k (a : E) * z k)) = Φ (u.ex (h z)) ≫ Xo.univ.t.act.act a :=
    fun a z => by rw [← hρ, ← hh, diagRep_apply]
  have hst : ∀ a, ∀ x ∈ u.Λ, ρ a x ∈ u.Λ := fun a x hx => by
    have := Xo.univ.t.act.hom a
    rw [← hker₀, hρ, (hker₀ x).2 hx, MonObj.one_comp]
  letI : SMul (𝓞 E) u.Λ := ⟨fun a x => ⟨ρ a x, hst a x x.2⟩⟩
  have hsm : ∀ (a : 𝓞 E) (x : u.Λ), ((a • x : u.Λ) : _ → ℂ) = ρ a x := fun _ _ => rfl
  letI : Module (𝓞 E) u.Λ := Module.ofMinimalAxioms
    (fun a x y => Subtype.ext (by simp [hsm])) (fun a b x => Subtype.ext (by simp [hsm]))
    (fun a b x => Subtype.ext (by simp [hsm])) (fun x => Subtype.ext (by simp [hsm]))
  let P : u.Λ →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp u.Λ.subtype.toAddMonoidHom
  have hP : ∀ x, h (P x) = x := fun x => h.apply_symm_apply _
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ u.Λ := fun z =>
    ⟨by rintro ⟨x, rfl⟩; rw [hP]; exact x.2, fun hz => ⟨⟨_, hz⟩, h.symm_apply_apply z⟩⟩
  have hker : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P.range := fun z => (hker₀ _).trans (hrange z).symm
  have hPs : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x => congrFun (h.injective (by
    rw [hP, hsm, ← diagRep_apply, hh, hP]))
  have hPi : Function.Injective P := h.symm.injective.comp Subtype.val_injective
  have hPd : DiscreteTopology P.range := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (f := fun z : P.range => (⟨h z, (hrange _).1 z.2⟩ : u.Λ))
      ((h.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _) fun z w hzw => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hzw))
  have hPf : Submodule.span ℝ (Set.range P) = ⊤ := by
    have e : Set.range P = (h.symm.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  obtain ⟨Hm', hH', hH''⟩ := exists_hermForm_comp Hm hAH.1 h.toLinearMap
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re := fun z hz => by
    rw [hH'']
    exact hAH.2.1 _ (h.map_ne_zero_iff.2 hz)
  have him : ∀ x x', (hermForm Hm' (P x) (P x')).im = Ef x x' := fun x x' => by
    rw [hH'', hE]
    exact congrArg₂ (fun a b => (hermForm Hm a b).im) (hP x) (hP x')
  have hweil' : ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P b))))
        (unitOn c) := fun k a b c hk hc => by
    rw [map_smul, map_smul, hP, hP]
    exact hΦW _ _ _ _ (hweil k a b c hk hc)
  obtain ⟨D', ε, hp, hq, hε⟩ := hDat E H u.Λ Ef D.p D.q g ty P Hm' hty hbij
    (adj_of_tateIso Xo.univ.t.PP.isLB he hker hPs hlin hweil' I) hPs hPi hPd hPf hH' hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp ε.toLinearMap.toAddMonoidHom
  have hr' : P'.range = P.range := by
    ext z
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨ε x, rfl⟩,
      by rintro ⟨x, rfl⟩; exact ⟨ε.symm x, congrArg P (ε.apply_symm_apply x)⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hPi.comp ε.injective, hr' ▸ hPd, ?_, Hm', hH', hpos, fun x x' => ?_⟩
    · exact (congrArg (fun x => P x i) (map_smul ε a x)).trans (hPs a _ i)
    · rw [← AddMonoidHom.coe_range, hr', AddMonoidHom.coe_range, hPf]
    · rw [hε]; exact him _ _
  have hker' : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P'.range := hr' ▸ hker
  have hweil'' : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P' a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P' b))))
        (unitOn c) := fun k a b c hk hc => hweil' k (ε a) (ε b) c hk (by rw [hc, hε])
  obtain ⟨f, ν, f1, f2, f3, f4, f5⟩ := similar_with_multiplier
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I
    (expTateIso he hper hker' hlin hweil'')
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  refine ⟨D', f l.M', P', fun z => Φ (u.ex (h z)), ⟨hp, hq, f, ν, f1, f2, f3, ?_, rfl⟩, hy, hper, he, hker', hlin,
    hweil'', fun a ha => (hM a ha).trans (f5 _ _ hM' (Nat.dvd_lcm_left _ _) a),
    fun a => (hA a).trans (f5 _ _ hM' (Nat.dvd_lcm_right _ _) a)⟩
  rw [← hζ, f4 _ l.A_pos]
  exact expNegUnit_zpow_val _ _

end GlobalTheory.PointUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PsiNormPull

theorem valF_eq_valR' {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := by
  rfl

theorem toStk_map_valR {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp F) (a : Γ(X, U)ˣ) :
    toStk z (ψ (valR x U a.val)) = (gm (spMap ψ ≫ x) z U a).val := by
  obtain ⟨h', e⟩ := CrdCalc.valR_spMap ψ x U h
  rw [← e, ← valF_eq_valR']
  exact toStk_valF _ U z (h' trivial) a

theorem norm_eq_one_of_isUnit {A F : Type} [CommRing A] [NormedField F] (ψ : A →+* F) (hψ : ∀ a, ‖ψ a‖ ≤ 1)
    {a : A} (ha : IsUnit a) : ‖ψ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have e : ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
  refine le_antisymm (hψ _) ?_
  calc (1 : ℝ) = ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ := e.symm
    _ ≤ ‖ψ u.val‖ * 1 := mul_le_mul_of_nonneg_left (hψ _) (norm_nonneg _)
    _ = _ := _root_.mul_one _

theorem norm_psi_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ j j' hj hj'
  let F := PadicAlgCl p
  let ψ' : V' →+* F := (algebraMap (FractionRing V') F).comp (algebraMap V' (FractionRing V'))
  have hsq : jFK (R := V') F ≫ jK V' ≫ spMap φ = jFK (R := V) F ≫ jK V := by
    refine ((congrArg (jFK (R := V') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap ?_).trans (spMap_comp _ _))
    exact RingHom.ext fun v => (hφ v).symm
  have z : Sp F := (default : PrimeSpectrum F)
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have hΦ : ⊤ ≤ ((D'.c χ).left ≫ Φ) ⁻¹ᵁ D.P.L.U j := by
    rw [show (D'.c χ).left ≫ Φ = _ from hD.c_pr χ]
    exact fun y _ => hj (Set.mem_univ ((specOf φ) y))
  let U := (D.P.L.pull Φ).U (fun _ => j) ⊓ D'.P.L.U j'
  have hU : ⊤ ≤ (D'.c χ).left ⁻¹ᵁ U := fun y _ => ⟨mem_pull.2 (hΦ (Set.mem_univ y)), hj' (Set.mem_univ y)⟩
  have m' : ∀ y, D'.xK χ y ∈ D'.P.L.U j' := fun y => hj' (Set.mem_univ (jK V' y))
  have m : ∀ y, D.xK (hD.xe χ) y ∈ D.P.L.U j := fun y => hj (Set.mem_univ (jK V y))
  have e := pmaps_psi hD F hsq χ _ (𝟙 _) z (fun _ => j) (fun _ => j')
    (fun _ => hΦ (Set.mem_univ (jK V' (jFK (R := V') F z)))) (fun _ => m' _)
  have g₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) (fun _ => -1) (D.psi (hD.xe χ)) (jFK (R := V) F)
    (𝟙 _ ≫ 𝟙 _) z (fun _ => j) (Set.mem_iInter.2 fun _ => m _)
  have g₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK χ) (fun _ => -1) (D'.psi χ) (jFK (R := V') F)
    (𝟙 _) z (fun _ => j') (Set.mem_iInter.2 fun _ => m' _)
  rw [Fintype.prod_unique] at e
  replace e := g₁.symm.trans (e.trans (congrArg₂ (· * ·) (zpow_neg_one _) g₂))
  rw [eq_inv_mul_iff_mul_eq] at e
  simp only [Category.id_comp] at e
  have a := toStk_map_valR (algebraMap (FractionRing V) F) (𝟙 _)
    (LB.wchart D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) fun _ => j) (fun y _ => Set.mem_iInter.2 fun _ => m y) z
    ((D.psi (hD.xe χ)).s fun _ => j)
  have a' := toStk_map_valR (algebraMap (FractionRing V') F) (𝟙 _)
    (LB.wchart D'.P.L (fun _ : PUnit => D'.xK χ) fun _ => j') (fun y _ => Set.mem_iInter.2 fun _ => m' y) z
    ((D'.psi χ).s fun _ => j')
  rw [Category.comp_id, ← valF_eq_valR'] at a a'
  have b := toStk_map_valR ψ' (D'.c χ).left U hU z (hD.w.s (fun _ => j, j'))
  have hpt : spMap ψ' ≫ (D'.c χ).left = jFK (R := V') F ≫ D'.xK χ :=
    (congrArg (· ≫ (D'.c χ).left) (spMap_comp _ _)).trans (Category.assoc _ _ _)
  have b' : toStk z (ψ' (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val)) =
      (gw hD.w (jFK (R := V') F ≫ D'.xK χ) z j j').val := by
    rw [← hpt]; exact b
  have hu : IsUnit (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val) := by
    exact (congrArg IsUnit (CrdCalc.valR_eq (R := V') (D'.c χ).left U hU _)).mpr ((Units.isUnit _).map _)
  have key := (toStk z).injective (a'.trans ((congrArg Units.val e).symm.trans
    ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) b' a).symm.trans (map_mul _ _ _).symm))))
  refine (congrArg norm key).trans ?_
  rw [norm_mul, norm_eq_one_of_isUnit ψ' hn hu, _root_.one_mul]
  rfl

end GlobalTheory.ZH.PsiNormPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem lift_mem_valuationSubring_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (i : K →+* L)
    (h : Function.Injective (i.comp (A.comap i).subtype)) (x : FractionRing (A.comap i)) :
    IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h x ∈ A ↔
      x ∈ Set.range (algebraMap (A.comap i) (FractionRing (A.comap i))) := by
  let f := FractionRing.algEquiv (A.comap i) K
  have hf : IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h =
      i.comp f.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A.comap i)) (RingHom.ext fun a => ?_)
    refine (IsFractionRing.lift_algebraMap h a).trans ?_
    exact congrArg i (f.commutes a).symm
  rw [hf]
  refine ⟨fun hx => ⟨⟨f x, hx⟩, f.injective (f.commutes _)⟩, ?_⟩
  rintro ⟨v, rfl⟩
  rw [← hf, IsFractionRing.lift_algebraMap]
  exact v.2

theorem intRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  intro p _ K hK
  have hmem : ∀ x : K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := fun x => mem_OO_iff _
  let e : integralClosure ℤ_[p] K ≃+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    { toFun := fun x => ⟨x.1, (hmem _).2 ((mem_integralClosure_padicInt_iff K _).1 x.2)⟩
      invFun := fun x => ⟨x.1, (mem_integralClosure_padicInt_iff K _).2 ((hmem _).1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] K)
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, fun x => ?_⟩
  · have := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal _) e).2 hc
    rwa [IsLocalRing.map_ringEquiv_maximalIdeal] at this
  · rw [← mem_OO_iff]
    exact lift_mem_valuationSubring_iff (OO p) (algebraMap K (PadicAlgCl p))
      (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsOfGeometric
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsionSection_eq_labelled_of_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (P : PolAV (Sp R)) (M : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ P.A)), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃ a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a = z) → ∀ y : baseOver (Sp R) ⟶ P.A, y ^ M = 1 → ∃ a, pt a = y := by
  intro R _ _ P M I pt h y hy
  let K := AlgebraicClosure (FractionRing R)
  let j : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hdom : IsDominant (Geo.Tor.spMap j) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have hprop : IsProper P.A.hom := P.isAb.proper
  obtain ⟨a, ha⟩ := h K (Geo.Tor.spMap j)
    ((Over.homMk (Geo.Tor.spMap j) (by simp) : Over.mk (Geo.Tor.spMap j) ⟶ baseOver (Sp R)) ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) P.A.hom
    ((Over.w (pt a)).trans (Over.w y).symm) (Geo.Tor.spMap j) (congrArg Over.Hom.left ha))⟩

end GlobalTheory
end

