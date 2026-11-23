module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedCharacterGood
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodPlaceAct

theorem chrW_pow_not_real {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Chr F E) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (h : ∀ k : ℤ, k ≠ 0 → chrW χ t (unifAt v) ^ k ≠ 1) :
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((chrW χ t (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  intro m hm r hr
  have hn : ‖((chrW χ t (unifAt v) : ℂˣ) : ℂ)‖ = 1 := by
    simp only [chrW, locChar, MonoidHom.coe_comp, Function.comp_apply]
    first | exact Circle.norm_coe _ | exact Circle.abs_coe _ | simp
  have hr1 : |r| = 1 := by
    have e := congrArg norm hr
    rw [norm_pow, hn, one_pow, Complex.norm_real, Real.norm_eq_abs] at e
    exact e.symm
  have hsq : r ^ 2 = 1 := by rw [← sq_abs, hr1, one_pow]
  apply h ((2 * m : ℕ) : ℤ) (by exact_mod_cast (by omega : 2 * m ≠ 0))
  apply Units.ext
  rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_one, pow_mul', hr]
  exact_mod_cast hsq

theorem act_omB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ t : E →ₐ[F] Fv F v,
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt v) : ℂ)) ^ m ≠ (r : ℂ)) ∧
      ∀ ι, G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v),
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omB ν₀ ν₀ g₀ 1 (ι φ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv hnr t
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.LeviAtPlace.levi_at_place F E σ B a a' G X om om' hTr v hv t
  let Bs : Base F E := { B with v₁ := v, τ₁ := t }
  have hTr' : IsTriple Bs G X om om' := ⟨{ hTr.base with }, { hTr.geo with hV := { hTr.geo.hV with }, hV' := { hTr.geo.hV' with }, hW := { hTr.geo.hW with } },
    { hTr.chars with good := hv }, hTr.weil, hTr.weil'⟩
  have hB := fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v (K g) (hK g).1
  choose S hS using hB
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA F _ → om' p Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ g φ r, φ ∈ SB _ → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have hvac := hTr.geo.hM'.vac v
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (G.M'.vac v) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hS g _ hsum).2 r r0, et, map_add (f := _), map_smul, (hS g φ hφ).2 r r1, (hS g φ' hφ').2 r r2, et]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr,
      (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]
  have hψ : Continuous B.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hψ v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hTr v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  by_cases hex : ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι
  · obtain ⟨ν, α, -, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs G X om om' hTr' K hK S h1 hlin h2 h3 h4 h5
    obtain ⟨ι₀, hι₀⟩ := hex
    refine ⟨ν, _root_.GlobalTheory.LinBarChar.unif_pow_ne_real hP F E σ B a a' G X om om' hTr v hv hnr t K hK S hS ν α ι₀ hι₀ (hC ι₀ hι₀),
      fun ι hι g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ => ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩⟩
    rw [hC ι hι g₀ φ hφ]
    funext Y
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one]
  · exact ⟨chrW X.ν t, chrW_pow_not_real _ t (fun k hk => hnr t k hk), fun ι hι => absurd ⟨ι, hι⟩ hex⟩

end GlobalTheory.GoodPlaceAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
section
noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

def logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) :
    Submodule A (Derivation ℤ A A) where
  carrier := {D | (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J}
  zero_mem' := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  add_mem' := fun {D D'} h h' =>
    ⟨fun a => by simp [h.1 a, h'.1 a], fun g hg => add_mem (h.2 g hg) (h'.2 g hg)⟩
  smul_mem' := fun r D h =>
    ⟨fun a => by simp [h.1 a], fun g hg => Ideal.mul_mem_left _ r (h.2 g hg)⟩

theorem mem_logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) (D : Derivation ℤ A A) :
    D ∈ logSub φ J ↔ (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J := Iff.rfl

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S]
include f

def ext (D : Derivation ℤ R R) : Derivation ℤ S S :=
  Classical.choose (GlobalTheory.LogDerLoc.exists_extension (B := S) f D)

theorem ext_algebraMap (D : Derivation ℤ R R) (r : R) :
    ext (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  Classical.choose_spec (GlobalTheory.LogDerLoc.exists_extension (B := S) f D) r

theorem der_ext (D₁ D₂ : Derivation ℤ S S) (h : ∀ r, D₁ (algebraMap R S r) = D₂ (algebraMap R S r)) :
    D₁ = D₂ := by
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) y
  have hu : IsUnit (algebraMap R S t) := IsLocalization.map_units S t
  have e' : y * algebraMap R S t = algebraMap R S r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : algebraMap R S t * D₁ y = algebraMap R S t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

def extL : Derivation ℤ R R →ₗ[R] Derivation ℤ S S where
  toFun := ext f
  map_add' D D' := der_ext f _ _ fun r => by
    rw [ext_algebraMap, Derivation.add_apply, Derivation.add_apply, ext_algebraMap, ext_algebraMap, map_add (f := _)]
  map_smul' c D := der_ext f _ _ fun r => by
    rw [ext_algebraMap, RingHom.id_apply, Derivation.smul_apply, Derivation.smul_apply, ext_algebraMap,
      smul_eq_mul, map_mul, Algebra.smul_def]

theorem extL_algebraMap (D : Derivation ℤ R R) (r : R) :
    extL (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  ext_algebraMap f D r

variable {k : Type} [CommRing k]

def res (φ : k →+* R) (J : Ideal R) :
    logSub φ J →ₗ[R] (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R where
  toFun D := ⟨extL f D.1, fun a => by
      rw [RingHom.comp_apply, extL_algebraMap, D.2.1 a, map_zero],
    GlobalTheory.LogDerLoc.map_mem_map (algebraMap R S) D.1 (extL f D.1) (extL_algebraMap f D.1) J D.2.2⟩
  map_add' D D' := Subtype.ext (map_add (extL (S := S) f) D.1 D'.1)
  map_smul' c D := Subtype.ext (map_smul (extL (S := S) f) c D.1)

theorem res_apply (φ : k →+* R) (J : Ideal R) (D : logSub φ J) (r : R) :
    (res (S := S) f φ J D).1 (algebraMap R S r) = algebraMap R S (D.1 r) :=
  ext_algebraMap f D.1 r

end GlobalTheory.LogDerProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocallyNormalNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.ExtGlue

open GlobalTheory.GroupGlue

theorem exists_scheme_two {Y Y₀ Y₁ Y₂ : Scheme.{0}} {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] {q₁ : Y₀ ⟶ Y₁} {q₂ : Y₀ ⟶ Y₂} (hq : IsPullback q₁ q₂ f₁ f₂)
    {G₁ : Over Y₁} {G₂ : Over Y₂} {G₀ : Over Y₀} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom q₁) (h₂ : IsPullback φ₂ G₀.hom G₂.hom q₂) :
    ∃ (G : Over Y) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom f₁ ∧
      IsPullback ψ₂ G₂.hom G.hom f₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion q₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hq.flip inferInstance
  have : IsOpenImmersion q₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hq inferInstance
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ Y := pushout.desc (G₁.hom ≫ f₁) (G₂.hom ≫ f₂) (by
    rw [h₁.w_assoc, h₂.w_assoc, hq.w])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ f₁ := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ f₂ := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = f₁ (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = f₂ (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback hq y (G₂.hom x) (hy.trans (e2 x))
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x w hw.symm
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hq (G₁.hom x) y (hy.trans (e1 x)).symm
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x w hw.symm
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

theorem exists_semiAbelian_two {Y Y₀ Y₁ Y₂ : Scheme.{0}} {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [o₁ : IsOpenImmersion f₁]
    [o₂ : IsOpenImmersion f₂] {q₁ : Y₀ ⟶ Y₁} {q₂ : Y₀ ⟶ Y₂} (hq : IsPullback q₁ q₂ f₁ f₂)
    (hcov : ∀ y : Y, y ∈ Set.range f₁ ∨ y ∈ Set.range f₂)
    {G₁ : Over Y₁} [i₁ : GrpObj G₁] {G₂ : Over Y₂} [i₂ : GrpObj G₂] {G₀ : Over Y₀} [GrpObj G₀]
    {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left} (s₁ : IsSemiAbelian G₁) (s₂ : IsSemiAbelian G₂)
    (h₁ : IsGrpPullback G₀ G₁ q₁ φ₁) (h₂ : IsGrpPullback G₀ G₂ q₂ φ₂) :
    ∃ (G : Over Y) (_ : GrpObj G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧
      IsGrpPullback G₁ G f₁ ψ₁ ∧ IsGrpPullback G₂ G f₂ ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme_two hq h₁.1 h₂.1
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ Y₁} {v : S ⟶ Y₂} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ w : S ⟶ Y₀, w ≫ q₁ = u ∧ w ≫ q₂ = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    have e : u ≫ f₁ = v ≫ f₂ := by
      rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
    exact ⟨hq.lift u v e, hq.lift_fst _ _ _, hq.lift_snd _ _ _⟩
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ Y₀) (a : Over.mk (w ≫ q₁) ⟶ G₁) (b : Over.mk (w ≫ q₂) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ Y₁} {v : S ⟶ Y₂} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec Y₁ Y₂ i
  let t : ∀ i, T i ⟶ Y := fun i => Bool.rec (motive := fun i => T i ⟶ Y) f₁ f₂ i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    exacts [o₁, o₂]
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hcov x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  exact ⟨G, iG, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ⟩

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {k : S'' ⟶ S} (w : g ≫ f = k) {F : G''.left ⟶ G.left}
    (h : IsGrpPullback G'' G k F) : ∃ e, IsGrpPullback G'' ((Over.pullback f).obj G) g e := by
  subst w
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor f g h⟩

theorem isDominant_of_isPullback {X X₁ Y Y₁ : Scheme.{0}} {k : X₁ ⟶ X} {j₁ : X₁ ⟶ Y₁} {j : X ⟶ Y} {f : Y₁ ⟶ Y}
    [IsOpenImmersion f] (hj : IsDominant j) (h : IsPullback k j₁ j f) : IsDominant j₁ := by
  refine ⟨(hj.denseRange.preimage f.isOpenEmbedding.isOpenMap).mono ?_⟩
  rintro y ⟨x, hx⟩
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback h x y hx
  exact ⟨z, hz⟩

theorem isNoetherian_of_isOpenImmersion {Y S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (f : Y ⟶ S)
    [IsOpenImmersion f] : AlgebraicGeometry.IsNoetherian Y := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion f
  have : TopologicalSpace.NoetherianSpace Y := f.isOpenEmbedding.isInducing.noetherianSpace
  exact {}

theorem hasExt_two {X X₁ Y Y₁ Y₂ : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y₁]
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₁) {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] (hcov : ∀ y : Y, y ∈ Set.range f₁ ∨ y ∈ Set.range f₂) {j₂ : X ⟶ Y₂} {k : X₁ ⟶ X}
    {j₁ : X₁ ⟶ Y₁} [IsOpenImmersion j₁] [IsDominant j₁] (w : k ≫ j₂ ≫ f₂ = j₁ ≫ f₁) {A : Over X} [GrpObj A]
    (h₁ : HasExt j₁ ((Over.pullback k).obj A)) (h₂ : HasExt j₂ A) : HasExt (j₂ ≫ f₂) A := by
  obtain ⟨G₁, i₁, e₁, s₁, g₁⟩ := h₁
  obtain ⟨G₂, i₂, e₂, s₂, g₂⟩ := h₂
  let j₀ : X₁ ⟶ pullback f₁ f₂ := pullback.lift j₁ (k ≫ j₂) (by rw [Category.assoc, w])
  have w₁ : j₀ ≫ pullback.fst f₁ f₂ = j₁ := pullback.lift_fst _ _ _
  have w₂ : j₀ ≫ pullback.snd f₁ f₂ = k ≫ j₂ := pullback.lift_snd _ _ _
  have : IsOpenImmersion (j₀ ≫ pullback.fst f₁ f₂) := by rw [w₁]; infer_instance
  have : IsOpenImmersion j₀ := IsOpenImmersion.of_comp j₀ (pullback.fst f₁ f₂)
  have : IsDominant (j₀ ≫ pullback.fst f₁ f₂) := by rw [w₁]; infer_instance
  have : IsDominant j₀ := IsDominant.of_comp_of_isOpenImmersion j₀ (pullback.fst f₁ f₂)
  have := isNoetherian_of_isOpenImmersion (pullback.fst f₁ f₂)
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have hn₀ := GlobalTheory.IsNormalScheme.of_isOpenImmersion (pullback.fst f₁ f₂)
  obtain ⟨a₁, ha₁⟩ := exists_factor _ _ w₁ g₁
  obtain ⟨a₂, ha₂⟩ := exists_factor _ _ w₂ ((isGrpPullback_pullback A k).comp g₂)
  obtain ⟨E, ⟨hE, -⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsSemiAbelian.pullback _ G₁ s₁) (IsSemiAbelian.pullback _ G₂ s₂) ha₁ ha₂
  obtain ⟨G, iG, ψ₁, ψ₂, s, -, g, -⟩ := exists_semiAbelian_two (IsPullback.of_hasPullback f₁ f₂) hcov s₁ s₂
    (isGrpPullback_pullback G₁ _)
    (((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso E).comp (isGrpPullback_pullback G₂ _)).congr
      (Category.id_comp _) rfl)
  exact ⟨G, iG, e₂ ≫ ψ₂, s, g₂.comp g⟩

theorem hasExt_of_locally : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A)) → HasExt j A := by
  intro X S _ hn j _ hj A _ hA hloc
  classical
  choose U hU hE using hloc
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have key : ∀ t : Finset S, ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (_ : IsOpenImmersion f) (i : X ⟶ Y), i ≫ f = j ∧
      HasExt i A ∧ ∀ s ∈ t, (U s : Set S) ⊆ Set.range f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨X, j, inferInstance, 𝟙 X, Category.id_comp _, ⟨A, inferInstance, _, isSemiAbelian_of_isAbelianScheme A hA,
        @ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso _ A A _ _ (Iso.refl A) (inferInstanceAs (IsMonHom (𝟙 A)))⟩,
        by simp⟩
    | insert s t _ ih =>
      obtain ⟨Y, f, _, i, hi, hext, ht⟩ := ih
      let W : S.Opens := U s ⊔ f.opensRange
      have r₂ : Set.range f ⊆ Set.range W.ι := by
        rw [Scheme.Opens.range_ι]
        exact fun y hy => Or.inr hy
      let f₁ : (U s).toScheme ⟶ W.toScheme := S.homOfLE le_sup_left
      let f₂ : Y ⟶ W.toScheme := IsOpenImmersion.lift W.ι f r₂
      have w₁ : f₁ ≫ W.ι = (U s).ι := Scheme.homOfLE_ι _ _
      have w₂ : f₂ ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
      have : IsOpenImmersion (f₂ ≫ W.ι) := by rw [w₂]; infer_instance
      have : IsOpenImmersion f₂ := IsOpenImmersion.of_comp f₂ W.ι
      have := isNoetherian_of_isOpenImmersion (U s).ι
      have : IsDominant (j ∣_ U s) := isDominant_of_isPullback hj (isPullback_morphismRestrict j (U s)).flip
      refine ⟨W, W.ι, inferInstance, i ≫ f₂, by rw [Category.assoc, w₂, hi], ?_, ?_⟩
      · refine hasExt_two (f₁ := f₁) (GlobalTheory.IsNormalScheme.pred _) ?_ ?_ (hE s) hext
        · rintro ⟨y, hy | ⟨z, hz⟩⟩
          · exact Or.inl ⟨⟨y, hy⟩, W.ι.isOpenEmbedding.injective (congrArg (fun g => g ⟨y, hy⟩) w₁)⟩
          · exact Or.inr ⟨z, W.ι.isOpenEmbedding.injective ((congrArg (fun g => g z) w₂).trans hz)⟩
        · rw [← cancel_mono W.ι]
          simp only [Category.assoc, w₁, w₂, hi, morphismRestrict_ι]
      · intro s' hs'
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · rw [Scheme.Opens.range_ι]
          exact fun y hy => Or.inl hy
        · exact (ht s' hs').trans r₂
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s : S => (U s : Set S)) (fun s => (U s).isOpen)
    (fun s _ => Set.mem_iUnion.2 ⟨s, hU s⟩)
  obtain ⟨Y, f, _, i, hi, ⟨G, iG, e, s, g⟩, hf⟩ := key t
  have : Surjective f := ⟨fun y => by
    obtain ⟨s, hs, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact hf s hs hy⟩
  have : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨a, ha⟩ := exists_factor (inv f) j (k := i) (by rw [← hi]; simp) g
  exact ⟨_, inferInstance, a, IsSemiAbelian.pullback _ G s, ha⟩

end GlobalTheory.ExtGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyExpLogCoverBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open GlobalTheory.TanPtMod

namespace GlobalTheory.UPel.HT.ES.WTors

theorem killedBy_iff_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy o w x := by
  constructor
  · intro h a ha
    exact h _ (Ideal.mem_map_of_mem _ ha)
  · intro h a ha
    simp only [GlobalTheory.IwLevel.htAct_act]
    refine Submodule.span_induction (p := fun y _ => x ≫ o.act.act y = 1) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨c, hc, rfl⟩
      exact h c hc
    · have h0 : o.act.act 0 = 1 := by
        have := o.act.add 0 0
        rw [add_zero] at this
        exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
      rw [h0, comp_one]
    · intro y z _ _ hy hz
      rw [o.act.add, comp_mul, hy, hz, _root_.mul_one]
    · intro c y _ hy
      haveI := o.act.hom c
      rw [smul_eq_mul, o.act.mul, ← Category.assoc, hy, one_comp]

end GlobalTheory.UPel.HT.ES.WTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_eq_span_on_basicOpens_of_stalk_principal : ∀ (X : Scheme.{0}) (I : X.IdealSheafData) (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (d : Γ(X, U.1)), IsNoetherianRing Γ(X, U.1) → (I.ideal U).map (X.presheaf.germ U.1 x₀ hx).hom = Ideal.span {(X.presheaf.germ U.1 x₀ hx).hom d} → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ ∀ t : Γ(X, U.1), X.basicOpen t ≤ X.basicOpen s → I.ideal (X.affineBasicOpen t) = Ideal.span {resG X (X.basicOpen_le t) d} := by
  first | exact @GlobalTheory.IdealSpread.ideal_eq_span_of_germ | exact GlobalTheory.IdealSpread.ideal_eq_span_of_germ | (intros; apply GlobalTheory.IdealSpread.ideal_eq_span_of_germ <;> assumption)
end

