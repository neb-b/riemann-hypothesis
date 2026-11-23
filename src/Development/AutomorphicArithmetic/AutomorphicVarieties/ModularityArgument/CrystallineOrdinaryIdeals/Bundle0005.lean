module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositive
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.cocycle_eq_crys_add_sub : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {W : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul E W] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρW : Representation E G W) (ρ : Representation E G V), ContAction ρW → ContAction ρ → Positive φ ρW → Positive φ ρ → ∀ i : W →ₗ[E] V, Function.Injective i → (∀ g x, i (ρW g x) = ρ g (i x)) → finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) → ∀ c ∈ Z1 ρ, ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ W _ _ _ _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρW ρ hcW hc hpW hp i hi hiρ hdim c hcZ
  obtain ⟨hfinW, hdW⟩ := _root_.GlobalTheory.cocycleDim_positive hP φ hφ ρW hcW hpW
  obtain ⟨hfin, hd⟩ := _root_.GlobalTheory.cocycleDim_positive hP φ hφ ρ hc hp
  have hic : Continuous i := IsModuleTopology.continuous_of_linearMap (i.restrictScalars ℚ_[l])
  let S := (finiteCocycles φ ρ).comap (Z1 ρ).subtype
  let SW := (finiteCocycles φ ρW).comap (Z1 ρW).subtype
  let M : Z1 ρW →ₗ[E] Z1 ρ := LinearMap.codRestrict (Z1 ρ) ((LinearMap.compLeft i G).comp (Z1 ρW).subtype)
    (fun c' => ⟨hic.comp c'.2.1, fun g h => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.compLeft_apply, Function.comp_apply,
        c'.2.2 g h, map_add, hiρ]⟩)
  have hM : ∀ c' g, ((M c' : Z1 ρ) : G → V) g = i ((c' : G → W) g) := fun _ _ => rfl
  let L : Z1 ρW →ₗ[E] Z1 ρ ⧸ S := S.mkQ ∘ₗ M
  have hker : LinearMap.ker L = SW := by
    ext c'
    simp only [L, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      S, SW, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      exact (posExact hP φ hφ ρW ρ hcW hc hpW i hiρ).2 hi hp _ c'.2 h
    · intro h
      exact (z1fMap φ ρW ρ).2 (i.restrictScalars ℚ_[l]) (fun g x => hiρ g x) _ h
  have eW : SW ≃ₗ[E] finiteCocycles φ ρW := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have eV : S ≃ₗ[E] finiteCocycles φ ρ := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_quotient_add_finrank S
  rw [hker, eW.finrank_eq] at h1
  rw [eV.finrank_eq] at h2
  have hr : LinearMap.range L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨c', hc'⟩ : S.mkQ ⟨c, hcZ⟩ ∈ LinearMap.range L := hr ▸ Submodule.mem_top
  refine ⟨c', c'.2, ?_⟩
  have := (Submodule.Quotient.eq S).1 hc'.symm
  simp only [S, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvalues
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h), Continuous x → IsCr φ (ext2 (κ 0) (κ 1) x hx) → ∀ y z : G → B, (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → (fun g => (z g, y g)) ∈ finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκc hine x hx hxc hcr y z hzy hy
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  have cd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκc i) (hκc j)
  have ined : ∀ i j g, φ g ∈ Iq l →
      (κ i / κ j) g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) := fun i j g hg => by
    rw [MonoidHom.div_apply, hine g hg i, hine g hg j, zpow_sub, div_eq_mul_inv]
  have crk : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκc i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hine g hg, smul_eq_mul]
  have crd : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (cd i j)) ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) fun g hg v => by
      rw [chRep_apply, ined i j g hg, smul_eq_mul]
  have hxf := (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκc 0) (hκc 1) x hx hxc (crk 0) (crk 1)).1 hcr
  have ed : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hx' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [ed]; exact hx
  have eM : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx) = ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    simp only [twist_apply, characterExtensionRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  rw [eM] at hzy ⊢
  set M := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' with hM
  have cM : ContAction M := contAction_charExtension_of_continuous_cocycle (cd 0 2) (cd 1 2) hx' hxc
  have crM : IsCr φ M :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (cd 0 2) (cd 1 2) x hx' hxc (crd 0 2) (crd 1 2)).2 (by rw [ed]; exact hxf)
  have hin02 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 2) g = cycA l l B (φ g) ^ (2 * (e : ℤ)) := fun g hg => by
    rw [ined 0 2 g hg, w0, w2]; congr 1; ring
  have hin12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B (φ g) ^ (e : ℤ) := fun g hg => by
    rw [ined 1 2 g hg, w1, w2]; congr 1; ring
  have pM : Positive φ (resCoef E M) := ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cM).1 crM,
    GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension φ hφ π hπ (κ 0 / κ 2) (κ 1 / κ 2) (cd 0 2) (cd 1 2) (2 * (e : ℤ)) e (by omega)
      (by exact_mod_cast he) hin02 hin12 x hx'⟩
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E M) (resCoef E (chRep (κ 1 / κ 2))) cM
    (contAction_chRep (cd 1 2)) pM (LinearMap.snd E B B) (fun g v => rfl)).1 Prod.snd_surjective y hy
  have hcM : c ∈ UpperTheory.V.Loc.finiteCocycles φ M := hc
  have hc2 : ∀ g, (c g).2 = y g := fun g => congrFun hcy g
  have hzc : Continuous z := hzy.1.fst
  have hcc : Continuous fun g => (c g).1 := hcM.1.1.fst
  have hzm : ∀ g h, z (g * h) =
      z g + ((((κ 0 / κ 2) g : Bˣ) : B) * z h + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h =>
    congrArg Prod.fst (hzy.2 g h)
  have hcm : ∀ g h, (c (g * h)).1 =
      (c g).1 + ((((κ 0 / κ 2) g : Bˣ) : B) * (c h).1 + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h => by
    rw [← hc2 h]
    exact congrArg Prod.fst (hcM.1.2 g h)
  have hd : z - (fun g => (c g).1) ∈ Z1 (chRep (κ 0 / κ 2)) := by
    refine ⟨hzc.sub hcc, fun g h => ?_⟩
    simp only [Pi.sub_apply, hzm, hcm, chRep_apply]
    ring
  have hd' : z - (fun g => (c g).1) ∈ Z1 (resCoef E (chRep (κ 0 / κ 2))) := hd
  obtain ⟨hcχ, pχ⟩ := _root_.GlobalTheory.PosModule.main φ hφ π hπ (κ 0 / κ 2) (cd 0 2) (2 * (e : ℤ)) (by omega) hin02
    (resCoef E (chRep (κ 0 / κ 2))) (fun g v => rfl)
  obtain ⟨hfin, hdim⟩ := _root_.GlobalTheory.cocycleDim_positive hP φ hφ (resCoef E (chRep (κ 0 / κ 2))) hcχ pχ
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have hD : H0dual ((cycA l l E).comp φ) (resCoef E (chRep (κ 0 / κ 2))) = ⊥ := by
    have hopen : IsOpen ((φ.range : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [MonoidHom.coe_range]; exact hφ.isOpen_range
    obtain ⟨s, ⟨⟨g, rfl⟩, hs⟩, hfo⟩ := ((cycInertia l).2 φ.range hopen).2
    refine eq_bot_iff.2 fun F hF => ?_
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun v => ?_
    have h1 := hF g v
    simp only [MonoidHom.comp_apply] at h1
    have hχg : (((κ 0 / κ 2) g : Bˣ) : B) = algebraMap E B (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) := by
      rw [hin02 g hs, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]; rfl
    have h2 : F (resCoef E (chRep (κ 0 / κ 2)) g v) = (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) * F v := by
      change F ((((κ 0 / κ 2) g : Bˣ) : B) * v) = _
      rw [hχg, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [h2] at h1
    have hne : cycA l l E (φ g) ^ (2 * (e : ℤ)) ≠ cycA l l E (φ g) := by
      intro h
      have h3 : cyc l l (φ g) ^ (2 * (e : ℤ) - 1) = 1 := by
        apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
        rw [map_zpow, map_one]
        change cycA l l E (φ g) ^ (2 * (e : ℤ) - 1) = 1
        rw [zpow_sub_one, h, mul_inv_cancel]
      exact hfo (isOfFinOrder_iff_zpow_eq_one.2 ⟨_, by omega, h3⟩)
    have h4 : ((((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) - (cycA l l E (φ g) : E)) * F v = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (Units.ext (sub_eq_zero.1 h5)) hne
    · simpa using h5
  rw [hD, finrank_bot, add_zero] at hdim
  have hle : UpperTheory.V.Loc.finiteCocycles φ (resCoef E (chRep (κ 0 / κ 2))) ≤ Z1 (resCoef E (chRep (κ 0 / κ 2))) :=
    fun c h => h.1
  haveI := hfin
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim.symm
  have hdf : z - (fun g => (c g).1) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 2)) := by
    rw [← heq] at hd'
    exact (z1fMap φ (resCoef E (chRep (κ 0 / κ 2))) (chRep (κ 0 / κ 2))).2 LinearMap.id (fun _ _ => rfl) _ hd'
  have inl : ∀ g v, LinearMap.inl E B B (chRep (κ 0 / κ 2) g v) = M g (LinearMap.inl E B B v) := fun g v => by
    simp [hM, characterExtensionRep_apply, chRep_apply]
  have h1 := (z1fMap φ (chRep (κ 0 / κ 2)) M).2 ((LinearMap.inl E B B).restrictScalars ℚ_[l]) inl _ hdf
  have h2 := add_mem h1 hcM
  convert h2 using 1
  funext g
  ext <;> simp [hc2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
      (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C]
      (r : GQ l →* GG (m := 3) (R := C)) (h : GL (Fin 3) C), HasMult D.η r →
      D.ordIdeal (conjBy h r) = D.ordIdeal r ∧
        (∀ a, D.dd (conjBy h r) a = D.dd r a) ∧ D.del (conjBy h r) = D.del r := by
  intro l _ O _ _ _ D C _ _ r h hr
  have hone : ∀ s ∈ D.HL, (r s).right = 1 := by
    intro s hs
    rw [hr s]
    exact MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).1
  have hmat (s : GQ l) (hs : s ∈ D.HL) :
      (conjBy h r s).mat =
        (h : Matrix (Fin 3) (Fin 3) C) * (r s).mat *
          ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    have hleft : (conjBy h r s).left = h * (r s).left * h⁻¹ := by
      show (GG.ofGL h * r s * (GG.ofGL h)⁻¹).left = _
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
      simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, SemidirectProduct.mul_right,
        hone s hs, mul_one, inv_one, map_one, MulAut.one_apply]
    unfold GG.mat
    rw [hleft, Units.val_mul, Units.val_mul]
  have hsh : ∀ s ∈ D.HL, ∀ a, D.sh (conjBy h r) a s =
      (h : Matrix (Fin 3) (Fin 3) C) * D.sh r a s * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs a
    simp only [UpperTheory.V.Loc.Dat3.sh]
    rw [hmat s hs, GlobalTheory.OrdLoc.conj_sub_scalar]
  have hHLopen : IsOpen (D.HL : Set (GQ l)) := GlobalTheory.OrdLoc.hl_isOpen' D
  have hs0 : D.s0 ∈ D.HL := by
    obtain ⟨s, ⟨hs, hi⟩, hcyc⟩ := ((cycInertia l).2 D.HL hHLopen).2
    have hex : ∃ s, D.IsInertiaInfiniteCyclotomic s := ⟨s, hs, hi, hcyc⟩
    exact (Classical.epsilon_spec hex).1
  have hex : ∃ σ, D.IsFr σ := by
    have : D.HL.Normal := GlobalTheory.OrdLoc.hl_normal' D
    obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
    have : (Iq l).Normal := hIn
    have : D.HL.FiniteIndex := GlobalTheory.OrdLoc.finiteIndex_of_open' ⟨D.HL, hHLopen⟩
    let N : Subgroup (GQ l) := D.HL ⊔ Iq l
    have : N.FiniteIndex := Subgroup.finiteIndex_of_le (show D.HL ≤ N from le_sup_left)
    have : N.Normal := Subgroup.sup_normal _ _
    let q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
    let m := orderOf q
    have hmN : σ₀ ^ m ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact pow_orderOf_eq_one q
    obtain ⟨σ, hσ, i₀, hi₀, hpow⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
    let φ := QuotientGroup.mk' (Iq l)
    have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
    have hφm : φ σ₀ ^ m = φ σ := by
      rw [← map_pow, ← hpow, map_mul, hφ.2 hi₀, mul_one]
    refine ⟨σ, ⟨hσ, ?_⟩, σ₀, m, hσ₀, orderOf_pos q, ?_⟩
    · rw [eq_top_iff]
      intro g _
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, mem_closure_iff]
      intro U hU hgU
      have hV : IsOpen (D.HL.subtype '' U) :=
        hHLopen.isOpenEmbedding_subtypeVal.isOpenMap U hU
      have hcl : (g : GQ l) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) :
          Set (GQ l)) := by
        rw [← Subgroup.topologicalClosure_coe, frobDense σ₀ hσ₀]
        trivial
      obtain ⟨x, ⟨u, huU, rfl⟩, hx⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
      obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      change i * σ₀ ^ k = (u : GQ l) at hiz
      have hkN : σ₀ ^ k ∈ N := by
        have e : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
        rw [e]
        exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
      have hdvd : (m : ℤ) ∣ k := by
        change (orderOf q : ℤ) ∣ k
        rw [orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
        exact hkN
      obtain ⟨j, rfl⟩ := hdvd
      have hφu : φ (u : GQ l) = φ σ ^ j := by
        rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
      have hy : (u : GQ l) * σ ^ (-j) ∈ Iq l := by
        rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
      refine ⟨u, huU, ?_⟩
      let y : D.HL := ⟨(u : GQ l) * σ ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hσ _)⟩
      have e : u = y * (⟨σ, hσ⟩ : D.HL) ^ j := by
        ext
        simp [y]
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
    · rw [← hpow]
      simpa using Subgroup.inv_mem _ hi₀
  have hfrSpec : D.IsFr D.fr := Classical.epsilon_spec hex
  obtain ⟨hfr, -⟩ := hfrSpec.1
  have htr : ∀ a, D.tr (conjBy h r) a = D.tr r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.tr]
    rw [hsh _ hs0, hsh _ hs0, hmat _ hfr, GlobalTheory.OrdLoc.conj_mul_three_alt, GlobalTheory.OrdLoc.trace_conj]
  have hdd : ∀ a, D.dd (conjBy h r) a = D.dd r a := by
    intro a
    simp only [UpperTheory.V.Loc.Dat3.dd, htr]
  have hprod : ∀ t : Fin 3 → GQ l, (∀ a, t a ∈ D.HL ⊓ Iq l) →
      D.sh (conjBy h r) 0 (t 0) * D.sh (conjBy h r) 1 (t 1) * D.sh (conjBy h r) 2 (t 2) =
        (h : Matrix (Fin 3) (Fin 3) C) * (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)) *
          ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro t ht
    rw [hsh _ (Subgroup.mem_inf.1 (ht 0)).1, hsh _ (Subgroup.mem_inf.1 (ht 1)).1,
      hsh _ (Subgroup.mem_inf.1 (ht 2)).1, GlobalTheory.OrdLoc.conj_mul_three_alt]
  refine ⟨?_, hdd, by simp only [UpperTheory.V.Loc.Dat3.del, hdd]⟩
  unfold UpperTheory.V.Loc.Dat3.ordIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
  · rw [Ideal.span_le]
    rintro x (⟨s, hs, i, rfl⟩ | ⟨t, ht, i, j, rfl⟩)
    · exact Ideal.subset_span
        (Or.inl ⟨s, hs, i, by rw [hmat s (Subgroup.mem_inf.1 hs).1, GlobalTheory.OrdLoc.charpoly_conj]⟩)
    · rw [GlobalTheory.OrdLoc.unconj h (D.sh r 0 (t 0) * D.sh r 1 (t 1) * D.sh r 2 (t 2)), ← hprod t ht]
      apply GlobalTheory.OrdLoc.ent_mem_mul
      intro a b
      exact Ideal.subset_span (Or.inr ⟨t, ht, a, b, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementUnramifiedTwistEqPowMulUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.NilpotentTwist

theorem isUnit_algebraMap_of_ne_zero {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Algebra O C]
    [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] {c : O} (hc : c ≠ 0) :
    IsUnit (algebraMap O C c) := by
  have hI : (Ideal.span {c}).comap (algebraMap ℤ_[l] O) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hc (Ideal.mem_span_singleton_self c) (Algebra.IsIntegral.isIntegral c)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
  obtain ⟨d, hd⟩ := hn
  have hq : algebraMap ℤ_[l] ℚ_[l] n ≠ 0 := by
    first
      | exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hn0
      | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).mpr hn0
  have hu : IsUnit (algebraMap ℤ_[l] C n) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] C]
    exact (isUnit_iff_ne_zero.mpr hq).map (algebraMap ℚ_[l] C)
  rw [IsScalarTower.algebraMap_apply ℤ_[l] O C, hd, map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem isUnit_add_nil {C : Type} [CommRing C] {a n : C} (ha : IsUnit a) (hn : IsNilpotent n) : IsUnit (a + n) := by
  first
    | exact hn.isUnit_add_left_of_commute ha (Commute.all _ _)
    | exact IsNilpotent.isUnit_add_left_of_commute hn ha (Commute.all _ _)

theorem nil_mul {C : Type} [CommRing C] {t : C} (ht : IsNilpotent t) (z : C) : IsNilpotent (t * z) := by
  first
    | exact (Commute.all _ _).isNilpotent_mul_left ht
    | exact (Commute.all _ _).isNilpotent_mul_right ht
    | exact ht.mul_right (Commute.all _ _)

theorem prod_eq {C : Type} [CommRing C] (L K0 K1 ε t w a : C) (y : Cˣ) (hy : (y : C) = a * (1 + t * w)) :
    L * (K0 * ((y : C) - ε)) * (K1 * (1 - ε * ((y⁻¹ : Cˣ) : C))) =
      (L * K0 * K1 * ((y⁻¹ : Cˣ) : C)) * ((a - ε) + t * (a * w)) ^ 2 := by
  have h := y.mul_inv
  rw [hy] at h ⊢
  linear_combination (-(L * K0 * K1 * (a * (1 + t * w) - ε))) * h

end GlobalTheory.OrdLoc.NilpotentTwist


open GlobalTheory.OrdLoc.NilpotentTwist in
theorem GlobalTheory.OrdLoc.del_unr_twist {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E]
    [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C]
    [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C]
    [IsScalarTower ℚ_[l] E C] (t : C) (ht : IsNilpotent t) :
    ∃ u : GQ l →* Cˣ, QCont l (fun g => (u g : C)) ∧ (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : C) - 1)) ∧
      ∃ (j : ℕ) (v : Cˣ), j ≤ 2 ∧
        GlobalTheory.OrdLoc.del D (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u)) = t ^ j * v := by
  obtain ⟨-, σ₀, m, hF, hm, hI⟩ := _root_.GlobalTheory.OrdLoc.fr_isFr D
  obtain ⟨-, -, -, -, hs0⟩ := _root_.GlobalTheory.OrdLoc.hl_basic D
  obtain ⟨u, hcont, huI, hunil, v, hv⟩ := GlobalTheory.unr_unip_char_frob t ht σ₀ hF
  refine ⟨u, hcont, huI, hunil, ?_⟩
  obtain ⟨b, hb⟩ := hv m
  obtain ⟨-, hcc⟩ := GlobalTheory.T.isUnit_characterDiff_at_chosenInertia D C
  have huσ : u (fr D) = u (σ₀ ^ m) := by
    calc u (fr D) = u (σ₀ ^ m * ((σ₀ ^ m)⁻¹ * fr D)) := by rw [mul_inv_cancel_left]
      _ = u (σ₀ ^ m) := by rw [map_mul, huI _ hI, mul_one]
  have hmat : ∀ g, (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) g).mat =
      Matrix.diagonal (fun i => ((((Units.map (algebraMap O C : O →* C)).comp D.Ψ g * u g) ^ wt1 i : Cˣ) : C)) :=
    fun g => rfl
  have hdiag : (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) (s0 D)).mat =
      Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D))) := by
    rw [hmat, huI _ hs0.2.1, mul_one]
    congr 1
    funext a
    rw [MonoidHom.comp_apply, ← map_zpow, Units.coe_map]
    rfl
  have h0 := GlobalTheory.T.ordinary_derivative_entry_formula D _ hdiag 0
  have h1 := GlobalTheory.T.ordinary_derivative_entry_formula D _ hdiag 1
  rw [hmat, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h0 h1
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e12 : (1 : Fin 3) + 1 = 2 := rfl
  have w0 : wt1 (0 : Fin 3) = 1 := rfl
  have w1 : wt1 (1 : Fin 3) = 0 := rfl
  have w2 : wt1 (2 : Fin 3) = -1 := rfl
  rw [e01, w0, w1, zpow_one, zpow_zero, Units.val_one, mul_one] at h0
  rw [e12, w1, w2, zpow_zero, zpow_neg_one, Units.val_one] at h1
  have hyv : (((Units.map (algebraMap O C : O →* C)).comp D.Ψ (fr D) * u (fr D) : Cˣ) : C) =
      algebraMap O C (D.Ψ (fr D) : O) * (1 + t * ((m : C) * v + t * b)) := by
    rw [Units.val_mul, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, huσ, ← hb]
    ring
  have hl : IsUnit (l : C) := by
    have : IsUnit ((l : ℚ_[l])) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    simpa using this.map (algebraMap ℚ_[l] C)
  have hmu : IsUnit (m : C) := by
    have : IsUnit ((m : ℚ_[l])) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (show m ≠ 0 by omega))
    simpa using this.map (algebraMap ℚ_[l] C)
  have hk0 : IsUnit (algebraMap O C (cc D 0 * cc D 1)) := by rw [map_mul]; exact (hcc 0).mul (hcc 1)
  have hk1 : IsUnit (algebraMap O C (cc D 1 * cc D 2)) := by rw [map_mul]; exact (hcc 1).mul (hcc 2)
  have hw : IsUnit ((m : C) * v + t * b) := isUnit_add_nil (hmu.mul (Units.isUnit v)) (nil_mul ht b)
  have ha : IsUnit (algebraMap O C (D.Ψ (fr D) : O)) := (Units.isUnit (D.Ψ (fr D))).map (algebraMap O C)
  unfold GlobalTheory.OrdLoc.del
  rw [h0, h1, prod_eq _ _ _ _ _ _ _ _ hyv, ← map_sub]
  have hQ : IsUnit ((l : C) * algebraMap O C (cc D 0 * cc D 1) * algebraMap O C (cc D 1 * cc D 2) *
      ((((Units.map (algebraMap O C : O →* C)).comp D.Ψ (fr D) * u (fr D))⁻¹ : Cˣ) : C)) :=
    ((hl.mul hk0).mul hk1).mul (Units.isUnit _)
  by_cases hc : (D.Ψ (fr D) : O) - ((cycA l l O (fr D) : Oˣ) : O) = 0
  · rw [hc, map_zero, zero_add]
    refine ⟨2, (hQ.mul ((ha.mul hw).pow 2)).unit, le_rfl, ?_⟩
    rw [IsUnit.unit_spec]
    ring
  · have hn : IsUnit (algebraMap O C ((D.Ψ (fr D) : O) - ((cycA l l O (fr D) : Oˣ) : O)) +
        t * (algebraMap O C (D.Ψ (fr D) : O) * ((m : C) * v + t * b))) :=
      isUnit_add_nil (isUnit_algebraMap_of_ne_zero (l := l) C hc) (nil_mul ht _)
    refine ⟨0, (hQ.mul (hn.pow 2)).unit, by norm_num, ?_⟩
    rw [IsUnit.unit_spec, pow_zero, one_mul]
end

