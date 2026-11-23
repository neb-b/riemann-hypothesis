module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.FormCochPullPf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem formCoch_pull_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (hle : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO V (τ ∘ i)) (a n : ℕ)
    (c : (Glob.formCos p V a).X n),
    pullCoch u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ n (formCoch p V a n c) =
      formCoch q U a n (fun i => GlobalTheory.HodgeCoh.formRes q (hle i) a
        (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))) := by
  intro K _ X Y q p u hu κ ι V U τ hτ hle a n c
  funext i
  have key : ∀ (W : Y.Opens) (x : GlobalTheory.CechDR.OmU p W a),
      (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom.app (op W) (toOm p a W x) =
        toOm q a (u ⁻¹ᵁ W) (GlobalTheory.HodgeCoh.formPull hu W a x) :=
    fun W x => GlobalTheory.HodgeCoh.omegaPull_toOmega hu a W x
  change res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_map u.base V U τ hτ i) ((GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom.app _
      (res (modulesAb (GlobalTheory.HodgeCoh.Omega p a)).obj (inter_le_capO V (τ ∘ i)) (toOm p a (Pb.capO V (τ ∘ i)) (c (τ ∘ i))))) =
    res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i) (toOm q a (Pb.capO U i)
      (GlobalTheory.HodgeCoh.formRes q (hle i) a (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))))
  have e1 := app_res_map u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom (inter_le_capO V (τ ∘ i))
    (toOm p a (Pb.capO V (τ ∘ i)) (c (τ ∘ i)))
  have e2 := key (Pb.capO V (τ ∘ i)) (c (τ ∘ i))
  have e3 := toOm_formRes q a (hle i) (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))
  refine (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_map u.base V U τ hτ i))
    (e1.trans (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj _) e2))).trans
      (Eq.trans ?_ (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i)) e3).symm)
  exact (res_res _ _ _ _).trans (res_res _ _ _ _).symm

end CrystallineSemistableComparison.Om.Cech
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.InjectiveSequenceLift
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem cechOmAdd_smul (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j), cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x) : type_of% @h := @h

theorem cechOm_pull (h : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (hV : iSup V = ⊤)
    (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → κ), IsAffineOpen (⨅ a, V (i a))) (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (a j : ℕ) (x : CO p V a j),
    cechOmAdd q U hU hUaff a j (cechPull hu V U τ hτ a j x) = pullC u hu a j (cechOmAdd p V hV hVaff a j x)) : type_of% @h := @h

theorem formToCO_bijective (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j)) : type_of% @h := @h

theorem formToCO_smul (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (a j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j),
    formToCO q U a j (r • x) = r • formToCO q U a j x) : type_of% @h := @h

theorem formCoch_pull (h : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (hle : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO V (τ ∘ i)) (a n : ℕ)
    (c : (Glob.formCos p V a).X n),
    pullCoch u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ n (formCoch p V a n c) =
      formCoch q U a n (fun i => GlobalTheory.HodgeCoh.formRes q (hle i) a
        (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i))))) : type_of% @h := @h

end CrystallineSemistableComparison.Om.Cech
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PfOmega
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem hPull_omega_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ)
    (y : Sheaf.H.{0} ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j),
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm (hPull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j y) =
      pullC u hu a j ((GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm y) := by
  intro K _ X Y q p u hu a j y
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨w, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j
    isTerminalTop).surjective y
  obtain ⟨z, rfl⟩ := (GlobalTheory.cohOn.toH' (GlobalTheory.HodgeCoh.Omega p a) ⊤ j).surjective w
  have hz : (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm
      (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)) = z :=
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm_apply_apply z
  rw [hz]
  change GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop
      (GlobalTheory.SheafPull.pull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j (homOfLE le_top)
        ((GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop).symm
          (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)))) =
    GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ _ j (GlobalTheory.HodgeCoh.hodgePull hu a j z))
  rw [AddEquiv.symm_apply_apply]
  congr 1

end CrystallineSemistableComparison.Om.Cech
end
end

