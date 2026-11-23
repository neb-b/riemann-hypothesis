module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalArchRestrictionSpaceOfWei
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem isAdmissibleBase_of_completeNormalLocalCharZero (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (h : IsCN V₁) :
    GlobalTheory.LN.admitted V₁ (maximalIdeal V₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  exact ⟨⟨h1, inferInstance, h2, h3⟩, h3, h4, inferInstance, inferInstance⟩

theorem exists_unif_pow8 : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ D : DegData V₁ (maximalIdeal V₁), Nonempty (Unif (maximalIdeal V₁) D P (powObj G₀ 8)) := by
  intro g n o _ ζ F W hW V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb P hP
  have hL := GlobalTheory.abelianSchemeLaws_all
  let P₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.1.globalFns
  obtain ⟨Pc, hPc⟩ := _root_.GlobalTheory.PowE8.exists_cp_e8LB _ G₀ P₀ W
  obtain ⟨gen, hgen, hA⟩ := _root_.GlobalTheory.SharpGen.gen_eighthPower g n o ζ F W V₁ D₀ G₀ A₀ U₀ y α α₂ hpb hsq hlb P hP
  have hW8 : GlobalTheory.LN.HypW (powObj G₀ 8) Pc.L.L := hPc ▸ _root_.GlobalTheory.PowE8.hypW_e8LB _ G₀ P₀ W hW
  have hT : GlobalTheory.LN.ThetaNZ (powObj G₀ 8) Pc.L.L :=
    hPc ▸ _root_.GlobalTheory.PowE8.thetaNZ_e8LB hL.1 hL.2 GlobalTheory.LN.ega_holds V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hA' : LBIso (P.L.pull gen.hom.left) (Pc.L.L.pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := hPc ▸ hA
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  obtain ⟨D, U, -, -⟩ := GlobalTheory.PrimeUnif.exists_unif hL.1 hL.2 GlobalTheory.laws3 GlobalTheory.LN.ega_holds GlobalTheory.uniformisation_total_closed V₁
    (maximalIdeal V₁) (isAdmissibleBase_of_completeNormalLocalCharZero V₁ hCN) inferInstance (powObj G₀ 8) Pc
    (GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS) hW8
    (_root_.GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power V₁ G₀ _ (_root_.GlobalTheory.SplitRed.splitOver_of_unif V₁ hCN D₀ G₀ A₀ U₀ hS)) hT P gen hgen hA'
  exact ⟨D, ⟨U⟩⟩

end GlobalTheory.PowE8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectors
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.forms_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → FiniteDimensional ℂ (forms S lam K') ∧ ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)), (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ π i ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ fixed (RF E n) (globLev S K')) ∧ (⨆ i, π i ⊓ fixed (RF E n) (globLev S K')) = forms S lam K' ∧ ∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → π₀ ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∃ i, ∀ w (σ : SmIrr (UL n w)), IsCompU π₀ w σ → IsCompU (π i) w σ := by
  intro E _ _ _ hU n _ S _ lam K' hK
  have hLo := GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK
  obtain ⟨C, hCf, hC⟩ := _root_.GlobalTheory.DefU.CoefSp.coef_space E n lam
  have hcls : ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n,
      ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
    intro L hL
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n L hL
    refine ⟨S₀, fun g => ?_⟩
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS₀ g
    exact ⟨γ, hγ, s, hs, k, hk, x, hx, by rw [mul_assoc (γ * s) x, ← GlobalTheory.DefU.fin_mul_inf k.2 hx, ← mul_assoc]⟩
  have hfin := GlobalTheory.UnitaryBC.finiteDimensional_levelForms E n hcls _ hLo C hCf
  have hmemF : ∀ φ : UA E n → ℂ, φ ∈ fixed (RF E n) (globLev S K') ↔ ∀ k ∈ globLev S K', RU E n (k : UA E n) φ = φ := by
    intro φ
    change (∀ h : globLev S K', _) ↔ _
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k.1 k.2⟩
  have hle : forms S lam K' ≤ Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ globLev S K', ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} := by
    refine iSup₂_le fun π hπ φ hφ => Submodule.subset_span ⟨(hπ.1.aut φ hφ.1).left, fun k hk g => ?_, hC π hπ.1 hπ.2 φ hφ.1⟩
    exact congrFun ((hmemF φ).1 hφ.2 k hk) g
  haveI : FiniteDimensional ℂ (forms S lam K') := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  obtain ⟨ι, hι, π, h1, h2, h3, h4⟩ := _root_.GlobalTheory.AbsDec.fixed_decomposition (RU E n) {x | ∃ k ∈ globLev S K', x = ((k : finU (E := E) (n := n)) : UA E n)}
    (fixed (RF E n) (globLev S K')) (fun φ => by
      rw [hmemF]
      exact ⟨fun h x ⟨k, hk, e⟩ => e ▸ h k hk, fun h k hk => h _ ⟨k, hk, rfl⟩⟩)
    {π | IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)}
    (fun P hP => ⟨hP.1.ne_bot, hP.1.stable, hP.1.irred⟩) (by assumption)
  refine ⟨ι, hι, π, fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2⟩, h2, h3, fun π₀ hπ₀ hw₀ hne => ?_⟩
  obtain ⟨i, T, hT1, hT2, hT3⟩ := h4 π₀ ⟨hπ₀, hw₀⟩ hne
  refine ⟨i, fun w σ ⟨p, hp, hirr, f, hf0, hfπ, hfe⟩ => ⟨p, hp, hirr, T ∘ₗ f, fun h => hf0 ?_, fun v => hT1 _ (hfπ v), fun x v => ?_⟩⟩
  · ext v : 1
    exact hT2 _ (hfπ v) (LinearMap.congr_fun h v)
  · rw [LinearMap.comp_apply, hfe x v]
    exact hT3 _ _ (hfπ v)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeLineLatticeTrivialMod
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.ModLim

variable {p : ℕ} [Fact p.Prime]



theorem exists_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  first
  | exact @_root_.GlobalTheory.AdelicLimitCompactness.main
  | exact _root_.GlobalTheory.AdelicLimitCompactness.main
  | (apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdelicLimitCompactness.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdelicLimitCompactness.main ..)

end GlobalTheory.LKGeo.ModLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColengthLemmas

variable {R : Type} [CommRing R]

theorem length_comp_range {A B C : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (u : B →ₗ[R] A) (v : C →ₗ[R] B) (hu : Function.Injective u) :
    Module.length R (A ⧸ LinearMap.range (u ∘ₗ v)) =
      Module.length R (A ⧸ LinearMap.range u) + Module.length R (B ⧸ LinearMap.range v) := by
  have hle : LinearMap.range v ≤ (LinearMap.range (u ∘ₗ v)).comap u := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hle2 : LinearMap.range (u ∘ₗ v) ≤ LinearMap.range u := LinearMap.range_comp_le_range v u
  let f := (LinearMap.range v).mapQ (LinearMap.range (u ∘ₗ v)) u hle
  let g := Submodule.factor hle2
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨c, hu hc⟩
  have hg : Function.Surjective g := Submodule.factor_surjective hle2
  have hex : Function.Exact f g := by
    intro x
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    constructor
    · intro h
      have h' : a ∈ LinearMap.range u := by
        simpa [g, Submodule.factor_mk, Submodule.Quotient.mk_eq_zero] using h
      obtain ⟨b, rfl⟩ := h'
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [← hy]
      show g (Submodule.Quotient.mk (u b)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem eq_of_le_of_length_eq {A : Type} [AddCommGroup A] [Module R A] (L L' : Submodule R A)
    (h : L ≤ L') (hl : Module.length R (A ⧸ L) = Module.length R (A ⧸ L'))
    (ht : Module.length R (A ⧸ L) ≠ ⊤) : L = L' := by
  let g := Submodule.factor h
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (LinearMap.ker g).injective_subtype (Submodule.factor_surjective h)
    (LinearMap.exact_subtype_ker_map g)
  have h0 : Module.length R (LinearMap.ker g) = 0 := by
    rw [← hl] at e
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 ht
    rw [← hn] at e
    generalize Module.length R (LinearMap.ker g) = b at e ⊢
    induction b using ENat.recTopCoe with
    | top => simp at e
    | coe b =>
      norm_cast at e ⊢
      omega
  rw [Module.length_eq_zero_iff] at h0
  refine le_antisymm h fun x hx => ?_
  have hmem : (Submodule.Quotient.mk x : A ⧸ L) ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have h1 : (⟨Submodule.Quotient.mk x, hmem⟩ : LinearMap.ker g) = 0 := Subsingleton.elim _ _
  have h2 : (Submodule.Quotient.mk x : A ⧸ L) = 0 := congrArg Subtype.val h1
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem length_quot_smul_range_free (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (a : O) :
    Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) =
      (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem length_quot_p_pow (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (n : ℕ) : Module.length (WittVector p k) (WittVector p k ⧸ Ideal.span {(p : WittVector p k) ^ n}) = n := by
  rw [← Ideal.span_singleton_pow, ← (WittVector.irreducible p).maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal _ n

end GlobalTheory.Dieu.ColengthLemmas

namespace GlobalTheory.Dieu

open GlobalTheory.Dieu.ColengthLemmas in
theorem colength_add_and_pow_and_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B C : Type) [AddCommGroup A] [Module (WittVector p k) A] [AddCommGroup B] [Module (WittVector p k) B] [AddCommGroup C] [Module (WittVector p k) C], (∀ (u : B →ₗ[(WittVector p k)] A) (v : C →ₗ[(WittVector p k)] B), Function.Injective u → Module.length (WittVector p k) (A ⧸ LinearMap.range (u ∘ₗ v)) = Module.length (WittVector p k) (A ⧸ LinearMap.range u) + Module.length (WittVector p k) (B ⧸ LinearMap.range v)) ∧ (Module.Free (WittVector p k) A → Module.Finite (WittVector p k) A → ∀ (n : ℕ) (u : A →ₗ[(WittVector p k)] A), (∀ a, u a = p ^ n • a) → Module.length (WittVector p k) (A ⧸ LinearMap.range u) = (n * Module.finrank (WittVector p k) A : ℕ)) ∧ ∀ L L' : Submodule (WittVector p k) A, L ≤ L' → Module.length (WittVector p k) (A ⧸ L) = Module.length (WittVector p k) (A ⧸ L') → Module.length (WittVector p k) (A ⧸ L) ≠ ⊤ → L = L' := by
  intro p _ k _ _ _ A B C _ _ _ _ _ _
  refine ⟨fun u v hu => length_comp_range u v hu, fun _ _ n u hu => ?_,
    fun L L' h hl ht => eq_of_le_of_length_eq L L' h hl ht⟩
  have hu' : u = ((p : WittVector p k) ^ n) • (LinearMap.id : A →ₗ[WittVector p k] A) := by
    ext a
    rw [hu a, LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [hu', length_quot_smul_range_free, length_quot_p_pow]
  push_cast
  ring

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorColengthRangeEqDetValuation
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColenDet

theorem map_eq_unit_mul_pow {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    ψ x = ψ (PadicInt.unitCoeff hx : ℤ_[p]) * (p : WittVector p k) ^ x.valuation := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, map_natCast]

theorem addVal_map {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal (WittVector p k) (ψ x) = (x.valuation : ℕ∞) := by
  rw [map_eq_unit_mul_pow ψ hx, AddValuation.map_mul, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible p),
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr ((PadicInt.unitCoeff hx).isUnit.map ψ)]
  simp

theorem colength_det : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  intro p _ k _ _ _ N _ _ _ _ ψ u d hdet
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := addVal_map ψ h0
    rw [hx, AddValuation.map_zero] at h1
    exact ENat.top_ne_coe _ h1
  have hlen := GlobalTheory.length_quot_range_eq_addVal_det u
  refine ⟨fun e he => ?_, fun hu => ?_, hψ⟩
  · rw [hlen, hdet] at he
    have hd : d ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at he
      exact ENat.top_ne_coe _ he
    rw [addVal_map ψ hd] at he
    have he' : d.valuation = e := by exact_mod_cast he
    rw [PadicInt.norm_eq_zpow_neg_valuation hd, he']
  · have h0 : LinearMap.det u = 0 := by
      by_contra h
      apply hu
      rwa [LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot] at h
    exact hψ (by rw [← hdet, h0, map_zero])

end GlobalTheory.Dieu.ColenDet
end

