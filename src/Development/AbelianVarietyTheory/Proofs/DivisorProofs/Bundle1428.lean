module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfThickeningsLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AlgGroup

open GlobalTheory.LN GlobalTheory.UU GlobalTheory.AbLaw.Seesaw

theorem isPullback_of_isGrpPullback {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem isAbelianScheme_of_thickenings_local (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) (hc : IsAdicComplete I R)
    (hc' : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hY : ∀ e, IsAbelianScheme (Y e))
    (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e))
    (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left) (hB : IsProjBy B.hom)
    (hs : Smooth B.hom) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e) :
    ∃ _ : GrpObj B, IsAbelianScheme B ∧ ∀ e, IsGrpPullback (Y e) B (thick R I e) (b e) := by
  have hM : MorAlgSt := GlobalTheory.LN.ega_holds.2.1
  have hpr : IsProper B.hom := isProper_of_isProjBy R B.left B.hom hB
  have hs₂ : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom)
    infer_instance
  obtain ⟨mu, hm⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (FreeGroup.of true * FreeGroup.of false) (B ⊗ B) (isProjBy_tensor R B B hB hB) hs₂
    (fun i => bif i then fst B B else snd B B)
  obtain ⟨io, hi⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (FreeGroup.of ())⁻¹ B hB hs (fun _ => 𝟙 B)
  obtain ⟨un, hu⟩ := exists_word hM hI hc hc' hβ hB hb hβb
    (1 : FreeGroup Empty) (𝟙_ _) (isProjBy_id R) (inferInstanceAs (Smooth (𝟙 _))) Empty.elim
  obtain ⟨G, hG, hG'⟩ := exists_grpObj hI (fun e => (hY e).comm) hpr hb mu io un
    (fun e T x y x₀ y₀ hx hy => by
      have := hm e T (lift x₀ y₀) (fun i => bif i then x else y) (fun i => by
        cases i
        · simpa using hy
        · simpa using hx)
      rwa [map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at this)
    (fun e T x x₀ hx => by
      have := hi e T x₀ (fun _ => x) (fun _ => by rwa [Category.comp_id])
      rwa [map_inv, FreeGroup.lift_apply_of] at this)
    (fun e T => by
      have := hu e T (toUnit _) Empty.elim (fun i => i.elim)
      rwa [map_one] at this)
  refine ⟨G, ⟨hG, hs, hpr, ?_⟩, hG'⟩
  exact geometricallyConnected_of_quotient R (I ^ (0 + 1)) (by simpa using hI) B hs hB (Y 0) (b 0) (hb 0)
    (hY 0).geomConnected

theorem exists_abelianScheme_of_tower : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsAbelianScheme (Y e)) → (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans R I e) (β e)) → ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro R _ _ _ _ I hI hc hc' Y _ β hY hβ N hN hv hA
  choose v hv using hv
  have hAlg : GlobalTheory.LN.AlgSt := GlobalTheory.LN.ega_holds.1
  obtain ⟨B, M, b, hB, hs, hM, hA', hb, hβb, hiso⟩ := hAlg R I hI hc hc' Y β N v
    (fun e => isPullback_of_isGrpPullback (hβ e)) (fun e => (hY e).smooth) (fun e => ⟨hN e, hv e⟩) hA
  obtain ⟨G, hG, hG'⟩ :=
    isAbelianScheme_of_thickenings_local R I hI hc hc' Y β hY hβ B b hB hs hb hβb
  exact ⟨B, G, M, b, hG, hM, hA', hG', hβb, hiso⟩

end GlobalTheory.AlgGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorAct
section
open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspStabFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zfin_of_comm (T : Module.End ℂ (Sm E a)) (hT : ∀ z ∈ Zalg E a, z * T = T * z) {φ : Sm E a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (T φ)) '' Zalg E a)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
    Zalg E a)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, (LinearMap.congr_fun (hT z hz) φ).symm⟩

theorem zalg_comm_fin (k : GL (Fin a) (Af E)) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    z * finRep E a k = finRep E a k * z := by
  let S := Subalgebra.centralizer ℂ ({finRep E a k} : Set (Module.End ℂ (Sm E a)))
  have hL : ∀ X, lie E a X ∈ S := fun X T hT => by
    rw [Set.mem_singleton_iff.1 hT]; exact (lie_rt_fin X k).symm
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have hS : Zalg E a ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hS hz (finRep E a k) rfl).symm

theorem level_of_le {φ ψ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ})
    (hle : ∀ k, finRep E a k φ = φ → finRep E a k ψ = ψ) : IsOpen {k | finRep E a k ψ = ψ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.mem_nhds (by simp)) fun k hk => hle k hk)

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

theorem height_mul_le_const (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖, by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_mul_const {f : GL (Fin a) (Cinf E) → ℂ} (c : GL (Fin a) (Cinf E))
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (y * c)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  obtain ⟨B, hB, hB'⟩ := height_mul_le_const c
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => (hC _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * c)]) (hB' y) N) C0

theorem isCuspForm_act' (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E a) (φ : Sm E a) (h : IsCuspForm φ) : IsCuspForm (act o φ) := by
  obtain ⟨hA, hC⟩ := h
  cases o with
  | fin k =>
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
    · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, hA.left]
    · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
        ext k'
        simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply]
        · intro e
          have := congrArg (finRep E a k) e
          rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
            mul_inv_cancel, map_one, Module.End.one_apply] at this
      change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
      rw [e]
      exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := hA.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
        (finRep E a k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
    · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
      refine ⟨C, N, fun y => ?_⟩
      change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
    · intro r h0 h1 _ _ μ 𝓕 hμ hF g
      change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
      simp_rw [mul_assoc]
      exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)
  | cpt c =>
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
    · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
      rw [mul_assoc, hA.left]
    · exact level_of_le hA.level fun k hk => by
        change finRep E a k (cptRep E a c φ) = cptRep E a c φ
        rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
    · have := hA.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E a c' * cptRep E a c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => _root_.GlobalTheory.ZalgCpt.zalg_comm_cptRep E a c z hz) hA.zfin
    · obtain ⟨C, N, h1⟩ := growth_mul_const (Unitary.toUnits c) (hA.growth g)
      refine ⟨C, N, fun y => ?_⟩
      change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
    · intro r h0 h1 _ _ μ 𝓕 hμ hF g
      change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
      simp_rw [mul_assoc]
      exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))
  | lie X =>
    refine ⟨⟨fun γ g => ?_, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ hA.kfin, zfin_of_comm _ (fun z hz => _root_.GlobalTheory.CuspRep.Zalg_mul_lie E a X z hz) hA.zfin, GlobalTheory.AutGrowth.lie_growth_of_finite hP E a X φ hA⟩,
      _root_.GlobalTheory.CuspRep.isCuspidal_lie_of_isCuspForm E a X φ ⟨hA, hC⟩⟩
    · change lieD X φ.1 (ratGL E a γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, hA.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le hA.level fun k hk => by
        change finRep E a k (lie E a X φ) = lie E a X φ
        change (rt E a (finGL E a k) * lie E a X) φ = _
        rw [← lie_rt_fin, Module.End.mul_apply]
        exact congrArg (lie E a X) hk

end GlobalTheory.CuspStabFin

theorem GlobalTheory.CuspStabFin.isCuspForm_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (o : GlobalTheory.CuspRep.Op E a) (φ : GlobalTheory.CuspRep.Sm E a),
    GlobalTheory.CuspRep.IsCuspForm φ → GlobalTheory.CuspRep.IsCuspForm (GlobalTheory.CuspRep.act o φ) :=
  fun hP _ _ _ _ _ o φ h => GlobalTheory.CuspStabFin.isCuspForm_act' hP o φ h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

open scoped ContDiff

namespace GlobalTheory.CxForm.FormMul

theorem isForm_mul : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  intro M _ n A α β hα hβ
  refine ⟨fun i S => ?_, fun x x' h => ?_⟩
  · have e : (fun v => (bas n).repr (A.loc (α * β) i v) S) = fun v => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
        (bas n).repr (A.loc α i v) p.1 * (bas n).repr (A.loc β i v) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun v => by rw [loc_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun p _ => ((hα.smooth i p.1).mul (hβ.smooth i p.2)).mul contDiffOn_const
  · show α x * β x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]

end GlobalTheory.CxForm.FormMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeTorsionCoprimeIdealsProductStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O] (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ → ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) → ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  first | (exact @GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (exact GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (intros; apply GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusPart

def GoodCover {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (u : splitTorus S X ⟶ G) : Prop :=
  ∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen u V

def IsKer {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] (u : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧ IsPullback u (toUnit _) q η[B]

def TorPol {O : Type} [CommRing O] (c : O →+* O) {S : Scheme.{0}} {G : Over S} [GrpObj G] (i : OAct O G) {X : Type}
    [AddCommGroup X] (u : splitTorus S X ⟶ G) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∃ (G' : Over (Sp K)) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left) (u' : splitTorus (Sp K) X ⟶ G')
    (P : Out.PolAV (Sp K)) (q : G' ⟶ P.A) (j : OAct O P.A),
    IsActPull i' i x φ ∧ TorusCompat x φ u' u ∧ IsKer u' q ∧ (∀ a, i'.act a ≫ q = q ≫ j.act a) ∧ IsRosati c P j

def QFin {S : Scheme.{0}} (Z : Over S) : Prop :=
  Flat Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ LocallyQuasiFinite Z.hom

def RatOver {S : Scheme.{0}} (Z : Over S) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∀ (Ω : Type) [Field Ω] (β : K →+* Ω) (y : Sp Ω ⟶ Z.left), y ≫ Z.hom = spMap β ≫ x →
    ∃ y₁ : Sp K ⟶ Z.left, y₁ ≫ Z.hom = x ∧ spMap β ≫ y₁ = y

def WtGeneric : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G),
    IsIntegral (splitTorus S X ⊗ G).left → ∀ (V : G.left.Opens) (f : Γ(G.left, V)) (χ : X) (Z : Over S)
      (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), IsDominant (lift t g).left →
      ∀ (h₁ : ⊤ ≤ ((t ≫ u) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
        (((t ≫ u) * g).left.appLE _ ⊤ h₁).hom f =
          t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom f → Wt u V f χ

theorem isKer_of_isQuot {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsQuot u q) : IsKer u q :=
  have := h.2.2.2.2.1
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, inferInstance, h.2.2.2.2.2.1⟩

theorem isKer_torusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (T : TorusExtension G) :
    letI := T.addCommGroup; letI := T.grpB; IsKer T.i T.q :=
  ⟨T.q_hom, T.q_flat, T.q_surjective, T.q_quasiCompact, T.isKernel⟩

theorem IsKer.comp_iso {S : Scheme.{0}} {T G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B'] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) (e : B ≅ B') (he : IsMonHom (q ≫ e.hom)) : IsKer u (q ≫ e.hom) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨he, by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, h₅.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (by simp) ?_⟩
  rw [Iso.refl_hom, Category.id_comp, ← IsMonHom.one_hom q, Category.assoc, IsMonHom.one_hom]

theorem IsKer.baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G]
    [GrpObj B] {G' B' : Over S'} [GrpObj G'] [GrpObj B'] {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left}
    (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback B' B f ψ) {u : splitTorus S X ⟶ G} {u' : splitTorus S' X ⟶ G'}
    (hT : TorusCompat f φ u' u) {q : G ⟶ B} (h : IsKer u q) :
    ∃ q' : G' ⟶ B', IsKer u' q' ∧ IsPullback φ q'.left q.left ψ := by
  obtain ⟨e, he, heF⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  obtain ⟨d, hd, hdF⟩ := grpPullback_iso (isGrpPullback_pullback B f) hψ
  obtain ⟨_, _, _, _, h₅⟩ := h
  have sq := isPullback_pullback_map_left f q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : u' ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map u := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f u).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (u'.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ u.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback u' (toUnit _) (e.hom ≫ (Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
    refine (isPullback_kernel_baseChange f h₅).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have hK : IsKer u' (e.hom ≫ (Over.pullback f).map q) := ⟨inferInstance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance, hk⟩
  refine ⟨_, hK.comp_iso d inferInstance, ?_⟩
  refine IsPullback.of_bot (v₂₁ := B'.hom) (v₂₂ := B.hom) ?_ ?_ hψ.1
  · rw [Over.w, Over.w]
    exact hφ.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hdF, ← heF, Category.assoc]
    exact congrArg (_ ≫ ·) sq.w

theorem IsKer.exists_oAct {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) {O : Type} [CommRing O] (i : OAct O G) (hu : ∀ a, u ≫ i.act a ≫ q = toUnit _ ≫ η[B]) :
    ∃ j : OAct O B, ∀ a, i.act a ≫ q = q ≫ j.act a := by
  obtain ⟨_, _, _, _, h₅⟩ := h
  have := i.hom
  have : Epi q := FlatQuotient.epi_of_flat_surjective q
  choose fB hm hfB using fun a => FlatQuotient.exists_desc q u (i.act a ≫ q) h₅ (hu a)
  refine ⟨⟨fB, hm, ?_, fun a b => ?_, fun a b => ?_⟩, fun a => (hfB a).symm⟩
  · rw [← cancel_epi q, hfB, i.one, Category.comp_id, Category.id_comp]
  · rw [← cancel_epi q, hfB, i.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · rw [← cancel_epi q, hfB, MonObj.comp_mul, hfB, hfB, i.add, MonObj.mul_comp]

theorem exists_isActPull {O : Type} [CommRing O] {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G]
    [IsCommMonObj G] (i : OAct O G) : IsActPull (OAct.pullback f G i) i f (pullback.fst G.hom f) :=
  ⟨isGrpPullback_pullback G f, fun _ => pullback.lift_fst _ _ _⟩

end GlobalTheory.TorusPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNefLineBundle_of_baseChange_field : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ L : LB Y, L.IsLB → (letI := algebraΓOfHom q; IsNef E (L.pull π)) → (letI := algebraΓOfHom p; IsNef k L) := by
  first | exact @GlobalTheory.NefFieldDescent.isNef_of_baseChange | exact GlobalTheory.NefFieldDescent.isNef_of_baseChange | (intros; apply GlobalTheory.NefFieldDescent.isNef_of_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIsQuotOfFinrankEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS

theorem isProper_of_isQuot_of_finrank_eq_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → Module.finrank ℤ X = 0 → IsProper G.hom := by
  intro k _ _ G _ X _ _ _ B _ i q hQ hB hX
  obtain ⟨hi, hq, hf, hsu, ha, hp, -⟩ := hQ
  have hsub : Subsingleton X := Module.finrank_zero_iff.1 hX
  have : Mono q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := by
      apply (GlobalTheory.splitTorusPointsEquiv (Sp k) X Y).injective
      refine MonoidHom.ext fun a => ?_
      have ha1 : a = 1 := by
        show a = Multiplicative.ofAdd 0
        rw [← ofAdd_toAdd a, Subsingleton.elim (Multiplicative.toAdd a) 0]
      rw [ha1, map_one, map_one]
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
  have := hB.proper
  have : Flat q.left := hf
  have : Surjective q.left := hsu
  have : IsAffineHom q.left := ha
  have : IsIso q.left := Flat.isIso_of_surjective_of_mono q.left
  rw [← Over.w q]
  infer_instance

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeOfPointCount
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_degree_of_point_count : ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  first | (exact @GlobalTheory.FinEtRank.isIsogDeg_of_card) | (exact GlobalTheory.FinEtRank.isIsogDeg_of_card) | (intros; apply GlobalTheory.FinEtRank.isIsogDeg_of_card <;> assumption)
end

