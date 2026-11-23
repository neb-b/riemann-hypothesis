module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
section
noncomputable section

open NumberField IsDedekindDomain Module

namespace GlobalTheory.GoodLat

section General

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (N : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (N : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 N x hx; exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span)
  | exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span ..)

theorem isLattice_comap [IsNoetherianRing R] {U : Type} [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
    (N : Submodule R V) (hN : Submodule.IsLattice K N) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    Submodule.IsLattice K (N.comap (f.restrictScalars R)) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars R) hf ?_
    exact hN.fg.of_le (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end General

section Forms

open Formalism.IndefR.Arith
open Formalism.DivisionValues.exponent_index_lattice (span_comap_eq_top)

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)


omit [Fintype G0] in
theorem isLattice_span_MK (hK : A.IsKsForm) (hM : A.MKFull) :
    Submodule.IsLattice LL (Submodule.span (𝓞 LL) (A.MK : Set WL)) := by
  obtain ⟨⟨s, hs⟩, hsp⟩ := hM
  refine ⟨⟨s, le_antisymm (Submodule.span_mono (hs ▸ Submodule.subset_span)) (Submodule.span_le.2 ?_)⟩, ?_⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih =>
      have e : a • x = (algebraMap (𝓞 Ks) (𝓞 LL) a) • x := by
        rw [← algebraMap_smul Ks a x, ← algebraMap_smul LL (algebraMap (𝓞 Ks) Ks a) x,
          ← algebraMap_smul LL (algebraMap (𝓞 Ks) (𝓞 LL) a) x]
        rfl
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ ih
  · obtain ⟨n, b, hb, -, -, -, h4⟩ := hK
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

private theorem span_MK_eq_top (hK : A.IsKsForm) (hM : A.MKFull) :
    Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) = ⊤ := by
  obtain ⟨n, b, hb, -, -, -, hbt⟩ := hK
  apply top_unique
  rw [← hbt]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  have hx : b i ∈ Submodule.span Ks (A.MK : Set WL) := hM.2 ▸ hb i
  have hs : Submodule.span Ks (A.MK : Set WL) ≤
      (Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL)).restrictScalars Ks := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span (Submodule.subset_span hx)
  exact hs hx

theorem isFullLattice_Mcoord (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)
    {d : ℕ} (b : Fin d → WL) (hb : LinearIndependent LL b) (hW : ∀ i, b i ∈ A.Wgood J0 lam0 eC) :
    Submodule.IsFullLattice LL (A.Mcoord J0 lam0 eC b) := by
  let f := (Fintype.linearCombination LL b).restrictScalars (𝓞 LL)
  have e : A.Mcoord J0 lam0 eC b = (Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      f := by
    ext c
    have hc : Fintype.linearCombination LL b c ∈ A.Wgood J0 lam0 eC := by
      rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hW i)
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hc.1⟩, hc.2⟩⟩
  rw [e]
  have hf : Function.Injective f := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun c hc => funext ?_)
    exact Fintype.linearIndependent_iff.1 hb c hc
  refine { toIsLattice := isLattice_comap _ (isLattice_span_MK A hK hM) (Fintype.linearCombination LL b) hf
           span_eq_top := span_comap_eq_top (Fintype.linearCombination LL b) _ (span_MK_eq_top A hK hM) }

theorem mj_full (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) :
    (A.Mj J0 lam0 eC).FG ∧ Submodule.span LL (A.Mj J0 lam0 eC : Set WL) = A.Wgood J0 lam0 eC := by
  have h := isLattice_comap _ (isLattice_span_MK A hK hM) (A.Wgood J0 lam0 eC).subtype Subtype.val_injective
  have e : A.Mj J0 lam0 eC = ((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))).map
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL)) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hx.1.2, hx.2⟩, hx.1.1, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact ⟨⟨hy, y.2.1⟩, y.2.2⟩⟩
  refine ⟨e ▸ h.fg.map _, ?_⟩
  rw [e]
  show Submodule.span LL ((A.Wgood J0 lam0 eC).subtype '' _) = _
  rw [Submodule.span_image]
  have hspan := span_MK_eq_top A hK hM
  have htop : Submodule.span LL
      (((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))) : Set (A.Wgood J0 lam0 eC)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_smul_mem (Submodule.span (𝓞 LL) (A.MK : Set WL))
      (show (x : WL) ∈ Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) by rw [hspan]; trivial)
    have ha' : algebraMap (𝓞 LL) LL a ≠ 0 := by
      intro hz
      apply ha
      apply FaithfulSMul.algebraMap_injective (𝓞 LL) LL
      simpa using hz
    have hx : a • x ∈ ((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))) := hax
    have hx' := Submodule.smul_mem (Submodule.span LL
      (((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))) : Set (A.Wgood J0 lam0 eC)))
      (algebraMap (𝓞 LL) LL a)⁻¹ (Submodule.subset_span hx)
    rw [← algebraMap_smul LL a x, smul_smul, inv_mul_cancel₀ ha', one_smul] at hx'
    exact hx'
  rw [htop, Submodule.map_subtype_top]

end Forms

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mLat_of_full {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hK : ∀ i, (R.FW i).IsKsForm) (hM : ∀ i, (R.FW i).MKFull) (b : Bool) : (R.toCx F).MLat b := fun i =>
  isFullLattice_Mcoord (R.FW i) (hK i) (hM i) _ _ _ (R.bL F b i)
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))
    fun k => (Module.finBasis D.what₂.LL (R.WL F b i) k).2

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem mkFull_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (i : Fin D.R.m) : (R.FW i).MKFull := by
  refine mkFull_of _ ((R.FW i).WK.subtype ∘ₗ (t.e i).toLinearMap) ?_ (fun x => ?_) (hl i)
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_subtype_top]
  · constructor
    · intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx.1⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      have h1 := (t.mem_MK i f).1 (hfx ▸ hx)
      exact ⟨f, fun la v hv => h1 la ⟨v, hv⟩, hfx⟩
    · rintro ⟨f, hf, rfl⟩
      exact (t.mem_MK i f).2 fun la y => hf la y.1 y.2

theorem mLat_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (F : Face D A) (b : Bool) : (R.toCx F).MLat b :=
  mLat_of_full R F t.ks (mkFull_of_tie t hl) b

end Record

end GlobalTheory.GoodLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelBasisEveryGeometricPointLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelSpread

theorem eq_one_of_point (O : Type) [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (n : ℕ) (hn : IsUnit (n : O)) (s : 𝟙_ (Over (Sp O)) ⟶ A)
    (hs : s ^ n = 1) (k : Type) [Field k] (x : Sp k ⟶ Sp O) (hx : toUnit (Over.mk x) ≫ s = 1) :
    s = 1 := by
  haveI := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing O
  have hn' : IsUnit (n : Γ(Sp O, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
    simpa using this
  obtain ⟨⟨-, het⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion (hG := hA) A hn'
  haveI := hA.proper
  haveI : IsSeparated ((mulN A n).left ≫ A.hom) := by
    rw [Over.w (mulN A n)]; infer_instance
  haveI : IsSeparated (mulN A n).left := IsSeparated.of_comp _ A.hom
  have hab : s ≫ mulN A n = (1 : 𝟙_ (Over (Sp O)) ⟶ A) ≫ mulN A n := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, hs, one_pow]
  have hj : toUnit (Over.mk x) ≫ s = toUnit (Over.mk x) ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A) := by
    rw [hx, MonObj.comp_one]
  exact Over.OverMorphism.ext (GlobalTheory.eq_of_connected_of_unramified_of_point (T := Sp O) (mulN A n).left
    (congrArg (·.left) hab) x (congrArg (·.left) hj))

end GlobalTheory.LevelSpread

namespace GlobalTheory.LevelSpread

theorem card_of_basis {I G : Type} [Fintype I] [Group G] {n : ℕ} (hn : n ≠ 0) (f : (I → ℤ) → G)
    (add : ∀ a b, f (a + b) = f a * f b) (tors : ∀ a, f a ^ n = 1)
    (ker : ∀ a, f a = 1 ↔ ∃ b, a = n • b) (onto : ∀ u : G, u ^ n = 1 → ∃ a, f a = u) :
    Nat.card {u : G // u ^ n = 1} = n ^ Fintype.card I := by
  haveI : NeZero n := ⟨hn⟩
  let F : (I → ZMod n) → {u : G // u ^ n = 1} := fun c => ⟨f fun i => (c i).val, tors _⟩
  have hF : Function.Injective F := fun c c' e => by
    have e₁ : f (fun i => (c i).val) = f fun i => (c' i).val := congrArg Subtype.val e
    have e₂ := add ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => (c' i).val
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod n)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hS : Function.Surjective F := by
    rintro ⟨u, hu⟩
    obtain ⟨a, rfl⟩ := onto u hu
    refine ⟨fun i => (a i : ZMod n), Subtype.ext ?_⟩
    show f (fun i => ((a i : ZMod n).val : ℤ)) = f a
    have hd : ∃ b, (fun i => ((a i : ZMod n).val : ℤ)) - a = n • b := by
      have : ∀ i, (n : ℤ) ∣ ((a i : ZMod n).val : ℤ) - a i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, sub_self]
      choose b hb using this
      exact ⟨b, funext fun i => by simpa using hb i⟩
    have e := add ((fun i => ((a i : ZMod n).val : ℤ)) - a) a
    rw [sub_add_cancel, (ker _).2 hd, _root_.one_mul] at e
    exact e
  rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hS⟩), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card]

theorem basis_at_every_point : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (g n : ℕ), IsUnit (n : O) → ∀ (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp O)) ⟶ A)), (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ n = 1) → ∀ (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (x₀ : Sp k₀ ⟶ Sp O), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = n • b)) → (∀ u : Over.mk x₀ ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp O), (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ u : Over.mk x ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) := by
  intro O _ _ _ A _ _ hA g n hn lev add tors k₀ _ _ x₀ ker₀ onto₀ k _ _ x
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := O) (by simpa using hn)
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have pw : ∀ (b : Fin g ⊕ Fin g → ℤ) (m : ℕ), lev (m • b) = lev b ^ m := fun b m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, lev0]
    | succ m ih => rw [succ_nsmul, add, ih, pow_succ]
  have hunit : ∀ (F : Type) [Field F] (p : Sp F ⟶ Sp O), (n : F) ≠ 0 := fun F _ p => by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective p
    have := (hn.map φ.hom).ne_zero
    simpa using this
  have ker : ∀ a, toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b := fun a => by
    refine ⟨fun h => (ker₀ a).1 ?_, ?_⟩
    · rw [GlobalTheory.LevelSpread.eq_one_of_point O A hA n hn (lev a) (tors a) k x h, MonObj.comp_one]
    · rintro ⟨b, rfl⟩
      rw [pw, tors, MonObj.comp_one]
  refine ⟨ker, fun u hu => ?_⟩
  haveI := hA.proper
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim O A hA
  have hsa : IsSemiAbelian A := by
    refine ⟨hA.comm, hA.smooth, inferInstance, inferInstance, hA.geomConnected, ?_⟩
    intro Ω _ _ p
    have hab : IsAbelianScheme ((Over.pullback p).obj A) := by
      have := hA.comm
      have := hA.smooth
      have := hA.proper
      have := hA.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd A.hom p)
        infer_instance
      · change IsProper (pullback.snd A.hom p)
        infer_instance
      · change GeometricallyConnected (pullback.snd A.hom p)
        infer_instance
    exact ⟨GlobalTheory.torusExtensionOfAbelian _ hab⟩
  have c₀ := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k₀ x₀ inferInstance n
    (hunit k₀ x₀)
  have c := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k x inferInstance n
    (hunit k x)
  have b₀ := card_of_basis hn0 (fun a => toUnit (Over.mk x₀) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    ker₀ onto₀
  exact GlobalTheory.SiegelOfPolarised.onto_torsion hn0 (fun a => toUnit (Over.mk x) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    (fun a => (ker a).1) (c.trans (c₀.symm.trans b₀)) u hu

end GlobalTheory.LevelSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionsProductBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMatEx

theorem liftTop (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg)
    (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left) (hpb : IsPullback φA' A'.hom A.hom t) :
    ∃ ψ : A'.left ⟶ (topS Rg ⊗ A).left, ψ ≫ (snd (topS Rg) A).left = φA' := by
  let a0 : A'.left ⟶ (⊤ : (Sp Rg).Opens).toScheme :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι (A'.hom ≫ t) (by simp)
  let X : Over (Sp Rg) := Over.mk (A'.hom ≫ t)
  let a : X ⟶ topS Rg := Over.homMk a0 (by simp only [a0, X, topS, overRes, baseOver, Over.mk_hom, Category.comp_id]; exact IsOpenImmersion.lift_fac _ _ _)
  let b : X ⟶ A := Over.homMk φA' hpb.w
  refine ⟨(lift a b).left, ?_⟩
  rw [← Over.comp_left, lift_snd]
  rfl

theorem zero_comp (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (R : Type) [CommRing R]
    (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (h : IsGrpPullback A' A t φA') :
    zeroPt A' ≫ φA' = t ≫ eSec A := by
  let T : Over (Sp R) := 𝟙_ (Over (Sp R))
  let u : Over.mk (T.hom ≫ t) ⟶ A := Over.homMk ((1 : T ⟶ A').left ≫ φA') (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have hu1 : u = 1 := mul_eq_left.1 hu
  have e := congrArg (fun x => Over.Hom.left x) hu1
  simp only [u, Over.homMk_left] at e
  rw [Hom.one_def, Hom.one_def] at e
  simp at e
  exact e
end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMatEx

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V)
    (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (h.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMat
open GlobalTheory.HomFixMatEx

theorem exists_isMat : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M t A' B' φA' φB' Φ' → ∃ c, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' hT
  obtain ⟨_, _, hL, hM, heA, heB, _, _, _, hbA, _⟩ := hH
  obtain ⟨hpA, hpB, hΦ, hiso⟩ := hT
  obtain ⟨ψA, hψA⟩ := liftTop Rg A R t A' φA' hpA.1
  obtain ⟨ψB, hψB⟩ := liftTop Rg B R t B' φB' hpB.1
  obtain ⟨w, hw⟩ := hiso
  have eg : (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = Φ'.left ≫ φB' := by rw [Category.assoc, hψB]
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB), α₀.IsGen := by
    have := GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts L M φA' Φ'.left φB' k w hw
    show ∃ α₀ : LB.Gen (LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
      (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))), α₀.IsGen
    rw [eg, hψA]; exact this
  have hΦ0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
    haveI := hΦ
    exact congrArg Over.Hom.left (IsMonHom.one_hom (f := Φ'))
  have hz1 : zeroPt A' ≫ (ψA ≫ (snd (topS Rg) A).left) = t ≫ eSec A := by
    rw [hψA]; exact zero_comp Rg A R t A' φA' hpA
  have hz2 : zeroPt A' ≫ ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) = t ≫ eSec B := by
    rw [eg, ← Category.assoc, hΦ0]; exact zero_comp Rg B R t B' φB' hpB
  have hzπ : zeroPt A' ≫ A'.hom = 𝟙 (Sp R) := Over.w η[A']
  obtain ⟨α, hα, hrig⟩ := GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator (Z₀ := Sp Rg) L M (ψA ≫ (snd (topS Rg) A).left)
    ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (eSec A) (eSec B) t (zeroPt A') A'.hom k eA eB α₀
    hL hM heA heB hα₀ hzπ hz1 hz2
  have key : ∀ j : Fin mB, ∃ cj : Fin mA → Γ(Sp R, ⊤), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (cj i) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro j
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback M (snd (topS Rg) B).left (Φ'.left ≫ ψB) (k : ℤ) (bB j)
    obtain ⟨s, hs⟩ := _root_.GlobalTheory.HomFixMat.divSec_exists L M (ψA ≫ (snd (topS Rg) A).left) ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)
      (k : ℤ) α hα hL hM σ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis Rg A L k mA bA hbA R t A' φA' hpA.1 ψA hψA s
    refine ⟨c, fun p => ?_⟩
    have e1 := hs p
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hσ p.1, hc p.2, map_sum] at e1
    erw [res_appLE] at e1
    simp only [map_mul] at e1
    erw [e1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · exact res_appLE _ _ _ _
    · exact res_appLE _ _ _ _
  choose cj hcj using key
  exact ⟨fun i j => cj j i, ψA, ψB, α, hψA, hψB, hα, hrig, fun j p => hcj j p⟩

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProd
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

noncomputable section

theorem measurePreserving_curry_lowCoord (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

theorem lintegral_prod_zOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  intro E _ _ _ r X h hh
  set e := Fintype.equivFin (Ent X) with he
  set G : (Fin (nd X) → ℂ) → ℝ≥0∞ := fun y => ∏ τ, h (fun p => y (e ⟨τ, p⟩)) with hG
  have hGm : Measurable G :=
    Finset.measurable_prod _ fun τ _ => hh.comp (Measurable.of_eval fun p => measurable_pi_apply _)
  have s1 : ∫⁻ z : V (nd X), ∏ τ, h (zOf X z τ) = ∫⁻ y, G y :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))).lintegral_comp hGm
  set K : (X.Ψ → Low r → ℂ) → ℝ≥0∞ := fun g => ∏ τ, h (g τ) with hK
  have hKm : Measurable K := Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_apply τ)
  have s2 : ∫⁻ y, G y = ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) := by
    refine ((volume_measurePreserving_piCongrLeft (fun _ => ℂ) e).lintegral_comp hGm).symm.trans
      (lintegral_congr fun f => ?_)
    simp only [hG, hK, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  have s3 : ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) = ∫⁻ g, K g :=
    (measurePreserving_curry_lowCoord X.Ψ (Low r)).lintegral_comp hKm
  rw [s1, s2, s3, hK, volume_pi]
  exact GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod fun _ => hh.aemeasurable

end

end GlobalTheory.IntBall
end

