module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemFilDDiag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.GradedChart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), Continuous x → IsCr φ (chRep a) → IsCr φ (chRep b) → (IsCr φ (ext2 a b x hx) ↔ x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (a / b))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ a b ha hb x hx hc h1 h2
  have key := UpperTheory.V.Loc.crExt φ hφ (chRep a) (ext2 a b x hx) (contAction_chRep ha) (contAction_charExtension_of_continuous_cocycle ha hb hx hc)
    b (LinearMap.inl B B B) (LinearMap.snd B B B) (0, 1) x LinearMap.inl_injective Function.Exact.inl_snd rfl
    (fun g v => by simp [characterExtensionRep_apply, chRep_apply]) (fun g => by simp [characterExtensionRep_apply, mul_comm])
    ⊤ (by simp) ((crOn_top φ _).2 h1) ((crOn_top φ _).2 h2)
  have e : twist b⁻¹ (chRep a) = chRep (a / b) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, chRep_apply, chRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, smul_eq_mul]
    ring
  rwa [crOn_top, e] at key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineUpperTriangularIffMemFiniteCocycles
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → ∀ hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h, IsCr φ (ext2 (κ 0) (κ 1) x hx) → IsCr φ (chRep (κ 2)) → (IsCr φ (colRep ρ) ↔ (fun g => (z g, y g)) ∈ UpperTheory.V.Loc.finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ κ hκ x y z ρ cx cy cz hρ hx h1 h2
  have hc : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact continuous_triM (t := fun g i => κ i g) hκ cx cy cz
  let f : (B × B) →ₗ[B] (Fin 3 → B) :=
    { toFun := fun v => ![v.1, v.2, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp }
  have hf : ∀ v, f v = ![v.1, v.2, 0] := fun _ => rfl
  rw [← crOn_top]
  refine crExt φ hφ (ext2 (κ 0) (κ 1) x hx) (colRep ρ) (contAction_charExtension_of_continuous_cocycle (hκ 0) (hκ 1) hx cx)
    (contAction_colRep hc) (κ 2) f (LinearMap.proj 2) ![0, 0, 1] (fun g => (z g, y g)) ?_ ?_ ?_ ?_ ?_ ⊤
    (by simp) ((crOn_top _ _).2 h1) ((crOn_top _ _).2 h2)
  · intro v w h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · intro v
    constructor
    · intro h
      refine ⟨(v 0, v 1), ?_⟩
      have h' : v 2 = 0 := h
      ext i
      fin_cases i <;> simp [hf, h']
    · rintro ⟨w, rfl⟩
      rfl
  · rfl
  · intro g v
    rw [colRep_apply, hρ, characterExtensionRep_apply]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro g
    rw [colRep_apply, hρ]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

namespace UpperTheory.V.Loc.R0

open Topology TensorProduct

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]
  [IsTopologicalRing E]

private theorem cont_ch {G : Type} [Group G] [TopologicalSpace G] {κ : G →* Eˣ} (h : Continuous κ) :
    ContAction (chRep κ) :=
  (Units.continuous_val.comp (h.comp continuous_fst)).mul continuous_snd

private theorem cont_prod {G V V' : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module E V]
    [TopologicalSpace V] [AddCommGroup V'] [Module E V'] [TopologicalSpace V'] {ρ : Representation E G V}
    {ρ' : Representation E G V'} (h : ContAction ρ) (h' : ContAction ρ') : ContAction (ρ.prod ρ') :=
  (h.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk (h'.comp (continuous_fst.prodMk continuous_snd.snd))

private theorem isCr_char (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Eˣ) (hκ : Continuous κ)
    (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l E g ^ w) : IsCr H.subtype (chRep (κ.comp H.subtype)) :=
  crUnr H.subtype hH.isOpenEmbedding_subtypeVal _ (cont_ch (hκ.comp continuous_subtype_val)) w fun g hg x => by
    rw [Subgroup.subtype_apply, ← hw g g.2 hg]
    rfl

private theorem isCr_diag (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : Fin 3 → GQ l →* Eˣ)
    (hκ : ∀ a, Continuous (κ a)) (w : Fin 3 → ℤ) (hw : ∀ a, ∀ g ∈ H, g ∈ Iq l → κ a g = cycA l l E g ^ w a)
    (ρ : ↥H →* GL (Fin 3) E)
    (hρ : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal fun a => (κ a g : E)) :
    IsCr H.subtype (colRep ρ) := by
  have hφ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  have hc : ∀ a, ContAction (chRep ((κ a).comp H.subtype)) := fun a =>
    cont_ch ((hκ a).comp continuous_subtype_val)
  have hcr := fun a => isCr_char H hH (κ a) (hκ a) (w a) (hw a)
  have hp := fun a g x => proj_diag (κ := fun a => (κ a).comp H.subtype) hρ a g x
  have h0 : ContAction (colRep ρ) := continuous_pi fun a => by
    have := (hc a).comp (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd) :
      Continuous fun p : ↥H × (Fin 3 → E) => (p.1, p.2 a))
    exact this.congr fun p => (hp a p.1 p.2).symm
  have h1 := (isCrys_isDR_prod _ hφ _ _ (hc 0) (cont_prod (hc 1) (hc 2))).1 (hcr 0)
    ((isCrys_isDR_prod _ hφ _ _ (hc 1) (hc 2)).1 (hcr 1) (hcr 2))
  refine ((isCrys_isDR_sub_quot _ hφ _ _ h0 (cont_prod (hc 0) (cont_prod (hc 1) (hc 2)))
    ((LinearMap.proj 0).prod ((LinearMap.proj 1).prod (LinearMap.proj 2))) fun g x => ?_).1 fun x y h => ?_).1 h1
  · exact Prod.ext (hp 0 g x) (Prod.ext (hp 1 g x) (hp 2 g x))
  · funext a
    fin_cases a
    · exact congrArg Prod.fst h
    · exact congrArg (fun z => z.2.1) h
    · exact congrArg (fun z => z.2.2) h

private theorem open_GK (K : FinExt l) : IsOpen (GK K : Set (GQ l)) :=
  haveI := K.2
  IntermediateField.fixingSubgroup_isOpen K.1

private theorem fil_char (K : FinExt l) (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Eˣ)
    (hκ : Continuous κ) (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l E g ^ w) :
    IsDr (GK K).subtype (chRep (κ.comp (GK K).subtype)) ∧ ∀ i : ℤ,
      (i ≤ -w → FilD (GK K).subtype (chRep (κ.comp (GK K).subtype)) i =
        Ddr (GK K).subtype (chRep (κ.comp (GK K).subtype))) ∧
      (-w < i → FilD (GK K).subtype (chRep (κ.comp (GK K).subtype)) i = ⊥) :=
  charFil (GK K).subtype (open_GK K).isOpenEmbedding_subtypeVal _
    (Units.continuous_val.comp (hκ.comp continuous_subtype_val)) w
    ⟨H.comap (GK K).subtype, hH.preimage continuous_subtype_val, fun g hg hI => hw g hg hI⟩

private theorem cr_char {K L : FinExt l} (h : K.1 ≤ L.1) (κ τ : GQ l →* Eˣ) (hκ : Continuous κ) (hτ : Continuous τ)
    (w : ℤ) (hw : ∀ g ∈ Iq l, κ g = cycA l l E g ^ w * τ g) (hL : ∀ g ∈ GK L, τ g = 1) :
    ∃ x ∈ Dcr (GK L).subtype (chRep ((κ.comp (GK K).subtype).comp (incl h))),
      (∀ y ∈ Dcr (GK L).subtype (chRep ((κ.comp (GK K).subtype).comp (incl h))),
        ∃! c : E ⊗[ℚ_[l]] ↥(K0 L), y = smulC E L c x) ∧
      ∀ γ, actC (GK K).subtype (chRep (κ.comp (GK K).subtype)) γ x = (τ γ : E) • x := by
  obtain ⟨x, hx, hb⟩ := char_cr (κ / τ) (isCr_char _ (open_GK _) _ (hκ.div' hτ) w fun g _ hg => by
    rw [MonoidHom.div_apply, hw g hg, mul_div_cancel_right])
  have e : (κ.comp (GK K).subtype).comp (incl h) = (κ / τ).comp (GK L).subtype := by
    ext1 g
    change κ g = κ g / τ g
    rw [hL g g.2, div_one]
  rw [e]
  refine ⟨x, (mem_Dcr _ _ _).2 fun g => hx g, hb L, fun γ => ?_⟩
  conv_rhs => rw [← hx γ]
  generalize x = y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v b =>
    change ((κ γ : E) • v) ⊗ₜ _ = ((τ γ : E) • (((κ γ / τ γ : Eˣ) : E) • v)) ⊗ₜ _
    rw [smul_smul, ← Units.val_mul, mul_div_cancel]
    rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb, smul_add]

end UpperTheory.V.Loc.R0

theorem UpperTheory.V.Loc.isType_and_isLocallyCrystalline_rz :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E], D.IsType (D.rz E) ∧ D.IsLCr (D.rz E) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  let j : Oˣ →* Eˣ := Units.map (algebraMap O E : O →* E)
  let κ : Fin 3 → GQ l →* Eˣ := fun a => (zpowGroupHom (wt1 a)).comp (j.comp D.Ψ)
  let τ : Fin 3 → GQ l →* Eˣ := fun a => (zpowGroupHom (wt1 a)).comp (j.comp D.τ)
  let w : Fin 3 → ℤ := fun a => D.e * wt1 a
  have hΨ : Continuous fun g => ((j (D.Ψ g) : Eˣ) : E) :=
    (ptCont (l := l) O E (Algebra.ofId O E)).1 _ _ D.Ψ_cont
  have hΨ' : Continuous (j.comp D.Ψ) := Units.continuous_iff.2 ⟨hΨ, (hΨ.comp continuous_inv).congr fun g => by
    simp only [Function.comp_apply, map_inv, MonoidHom.comp_apply]⟩
  have hτ' : Continuous (j.comp D.τ) := continuous_of_continuousAt_one _
    (continuousAt_const.congr (Filter.eventually_of_mem (D.τ_open.mem_nhds D.τ.ker.one_mem) fun g hg => by
      change 1 = j (D.τ g)
      rw [show D.τ g = 1 from hg, map_one]))
  have hκ : ∀ a, Continuous (κ a) := fun a => hΨ'.zpow _
  have hτ : ∀ a, Continuous (τ a) := fun a => hτ'.zpow _
  have hw : ∀ a, ∀ g ∈ Iq l, κ a g = cycA l l E g ^ w a * τ a g := by
    intro a g hg
    have h1 : j (cycA l l O g) = cycA l l E g := Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O E _).symm
    change j (D.Ψ g) ^ wt1 a = _ * j (D.τ g) ^ wt1 a
    rw [D.Ψ_I g hg, map_mul, map_pow, h1, mul_zpow, ← zpow_natCast, ← zpow_mul]
  have hτ1 : ∀ a, ∀ g ∈ D.HL, τ a g = 1 := fun a g hg => by
    change j (D.τ g) ^ wt1 a = 1
    rw [show D.τ g = 1 from hg.2, map_one, one_zpow]
  have hw' : ∀ a, ∀ g ∈ D.HL, g ∈ Iq l → κ a g = cycA l l E g ^ w a := fun a g hg hI => by
    rw [hw a g hI, hτ1 a g hg, mul_one]
  have hker : D.η.ker = GK D.Kv := Subgroup.ext D.η_ker
  have hH : IsOpen (D.HL : Set (GQ l)) := by
    have := (R0.open_GK D.Kv).inter D.τ_open
    rwa [← hker] at this
  let σ : GQ l →* GL (Fin 3) E := (tor E).comp (j.comp D.Ψ)
  have hσ : ∀ g, σ g = (D.rz E g).left := fun g => Units.ext (by
    change Matrix.diagonal _ = (Matrix.diagonal _).map (algebraMap O E)
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    exact congrArg Units.val (map_zpow j _ _).symm)
  refine ⟨⟨σ.comp (GK D.Kv).subtype, fun g => hσ g, ?_, ?_⟩, σ.comp D.HL.subtype, fun g => hσ g,
    R0.isCr_diag _ hH κ hκ w hw' _ fun _ => rfl⟩
  · have he := D.e_pos
    refine R0.hodge_diag (κ := fun a => (κ a).comp (GK D.Kv).subtype) (fun _ => rfl) (fun a => -w a) ?_ _ ?_ ?_
      (fun a => (R0.fil_char D.Kv _ hH _ (hκ a) _ (hw' a)).2) fun a => ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp [w, wt1] at hab ⊢ <;> omega
    · intro a
      fin_cases a <;> simp [w, wt1, hodge0]
    · intro i hi
      have h0 := hi 0
      have h1 := hi 1
      have h2 := hi 2
      simp [w, wt1] at h0 h1 h2
      rw [hodge0, if_neg (by omega)]
    · obtain ⟨x, hx, hb⟩ := R0.char_dr (κ a) (R0.fil_char _ _ hH _ (hκ a) _ (hw' a)).1
      exact ⟨x, (R0.mem_Ddr _ _ _).2 fun g => hx g, hb D.Kv⟩
  · obtain ⟨L, -, -, -, -, hL, -, -⟩ := openField D.HL.subtype hH.isOpenEmbedding_subtypeVal
    rw [Subgroup.range_subtype] at hL
    have hle : GK L ≤ GK D.Kv := by
      rw [← hL, ← hker]
      exact inf_le_left
    have h : D.Kv.1 ≤ L.1 := by
      have : IsGalois ℚ_[l] (Om l) := inferInstance
      rw [← InfiniteGalois.fixedField_fixingSubgroup D.Kv.1, ← InfiniteGalois.fixedField_fixingSubgroup L.1]
      exact IntermediateField.fixedField_le hle
    choose x hx hb ht using fun a => R0.cr_char h (κ a) (τ a) (hκ a) (hτ a) (w a) (hw a) (hL ▸ hτ1 a)
    have hN : (GK L).Normal := by
      rw [← hL, Dat3.HL]
      infer_instance
    have hC := (isCrIff L _).1.1 (R0.isCr_diag (GK L) (R0.open_GK L) κ hκ w (hL ▸ hw') (σ.comp (GK L).subtype)
      fun _ => rfl)
    have key := R0.crys_diag (ρ := σ.comp (GK D.Kv).subtype) (κ := fun a => (κ a).comp (GK D.Kv).subtype)
      (fun _ => rfl) h inferInstance hC (fun a γ => (τ a γ : E)) x hx hb ht
    refine ⟨L, h, ?_⟩
    convert key using 2 with γ
    simp [Fin.sum_univ_three, τ, j, wt1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LiftChart
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem hasWeight_of_generators {O R X Q : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (W : WPres O X R) (h : W.HasOrigin) [AddCommGroup Q] [Module O Q] (D : R →ₗ[O] Q)
    (hD : D ∈ PtDer (W.origin h) Q) (j : X) (hz : ∀ s, W.wt s ≠ j → D (W.z s) = 0) : HasWt W.part j D := by
  classical
  let W' := WPres.free O W.wt
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  let D' : MvPowerSeries W.σ O →ₗ[O] Q := D ∘ₗ W.π.toLinearMap -
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries W.σ O →ₗ[O] O).smulRight (D (W.z s))
  have hD' : ∀ f, D' f = D (W.π f) - ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • D (W.z s) := fun f => by
    simp [D']
  have h0 := (der_extend O _ X W' h' Q).2 D' (fun f g => by
    have h1 : D (W.π f * W.π g) = W.origin h (W.π f) • D (W.π g) + W.origin h (W.π g) • D (W.π f) := hD _ _
    rw [hD', hD', hD', ho, ho, map_mul, h1, W.origin_π, W.origin_π]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
    abel) (fun (s : W.σ) => by
    show D' (MvPowerSeries.X s) = 0
    rw [hD']
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, WPres.z])
  rintro i hi _ ⟨f, hf, rfl⟩
  have h1 := hD' f
  rw [h0, LinearMap.zero_apply, eq_comm, sub_eq_zero] at h1
  refine h1.trans (Finset.sum_eq_zero fun s _ => ?_)
  by_cases hs : W.wt s = j
  · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
  · rw [hz s hs, smul_zero]

private theorem origin_eq {O R X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [AddCommGroup X] (W : WPres O X R) (x : R →ₐ[O] O)
    (hx : ∀ s, x (W.z s) = 0) : ∃ h : W.HasOrigin, W.origin h = x := by
  have key : ∀ f, x (W.π f) = MvPowerSeries.constantCoeff f := by
    let F : MvPowerSeries W.σ O →ₐ[O] O :=
      { (MvPowerSeries.constantCoeff : MvPowerSeries W.σ O →+* O) with
        commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
    have := (co_ev O O O W.σ (AlgHom.id O O) 0 (fun _ => zero_mem _)).unique (y₁ := x.comp W.π) (y₂ := F)
      ⟨fun a => (x.comp W.π).commutes a, hx⟩ ⟨fun a => F.commutes a, fun s => MvPowerSeries.constantCoeff_X s⟩
    exact fun f => DFunLike.congr_fun this f
  refine ⟨fun f hf => by rw [← key, hf, map_zero], AlgHom.ext fun a => ?_⟩
  obtain ⟨f, rfl⟩ := W.surj a
  exact (W.origin_π _ f).trans (key f).symm

private theorem qcont_lin {l : ℕ} [Fact l.Prime] {V W X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [TopologicalSpace X] {φ : X → V} (hφ : QCont l φ) (ψ : V →ₗ[ℚ_[l]] W) :
    QCont l fun g => ψ (φ g) := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap ψ).comp hφ

private theorem qcont_add {l : ℕ} [Fact l.Prime] {V X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [TopologicalSpace X] {φ ψ : X → V} (hφ : QCont l φ) (hψ : QCont l ψ) : QCont l fun g => φ g + ψ g := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hφ hψ

private theorem qcont_dual {l : ℕ} [Fact l.Prime] {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    (f : X → DualNumber E) (h1 : QCont l fun x => (f x).fst) (h2 : QCont l fun x => (f x).snd) : QCont l f := by
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  rw [e]
  exact qcont_add (qcont_lin h1 _) (qcont_lin h2 _)

theorem UpperTheory.V.Loc.liftChart :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (Q : ∀ (B : Type) [CommRing B] [Algebra O B], (Γ →* Matrix ι ι B) → Prop),
    (∀ (B B' : Type) [CommRing B] [Algebra O B] [CommRing B'] [Algebra O B'] (f : B →ₐ[O] B') (r : Γ →* Matrix ι ι B), (Q B r → Q B' (mapRep (f : B →+* B') r)) ∧ (Function.Injective f → Q B' (mapRep (f : B →+* B') r) → Q B r)) →
    Represents (fun R' _ _ _ r => Q R' r.hom) ρ → ρ.TStable w →
    ∀ ρ₀ : Lift O rbar O, Q O ρ₀.hom → (∀ g a b, w a ≠ w b → ρ₀.hom g a b = 0) →
    (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : Γ →* Matrix ι ι B', mapRep (π' : B' →+* E) r' = mapRep (algebraMap O E) ρ₀.hom → (∀ a b, QCont l fun g => r' g a b) → Q B' r' → ∃ r : Γ →* Matrix ι ι B, (∀ a b, QCont l fun g => r g a b) ∧ Q B r ∧ mapRep (p : B →+* B') r = r') →
    ∃ (x : R →ₐ[O] O) (P : Ideal R) (n : ℕ) (u : Fin n → X) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), ρ.map x = ρ₀ ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ g a b, φ (ρ.hom g a b) ∈ wtPart E u (w a - w b)) ∧
      ∀ j, ∃ S : Submodule E (Γ → Matrix ι ι E), Nat.card {i // u i = j} = finrank E ↥S ∧ ∀ s, s ∈ S ↔ (∃ r' : Γ →* Matrix ι ι (DualNumber E), (∀ g a b, r' g a b = ⟨algebraMap O E (ρ₀.hom g a b), s g a b⟩) ∧ Q (DualNumber E) r') ∧ (∀ a b, QCont l fun g => s g a b) ∧ ∀ g a b, w a - w b ≠ j → s g a b = 0 := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar X _ _ _ w E _ _ _ _ _ _ _ _ R _ _ _ ρ Q hQ hrep hst ρ₀ hQ0 hd hlift
  have hgen : ρ.Generates := fun R' _ _ _ f f' h =>
    ((hrep R').2 _ ((hrep R').1 f')).unique h rfl
  have hQρ : Q R ρ.hom := (hrep R).1 (AlgHom.id O R)
  obtain ⟨x, hx, -⟩ := (hrep O).2 ρ₀ hQ0
  have hxe : ∀ g a b, x (ρ.hom g a b) = ρ₀.hom g a b := fun g a b => by rw [← hx]; rfl
  have hpt : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
      [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : Γ →* Matrix ι ι B),
      (∀ g a b, π (r g a b) = algebraMap O E (ρ₀.hom g a b)) → (∀ a b, QCont l fun g => r g a b) → Q B r →
      ∃ f : R →ₐ[O] B, ∀ g a b, f (ρ.hom g a b) = r g a b := by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ r h1 h2 h3
    obtain ⟨C, hC, ρ', hρ'⟩ := exists_lift_factor_compact_subalgebra (l := l) rbar R ρ E B π hπ ((Algebra.ofId O E).comp x) r
      (fun g a b => by rw [h1, ← hxe]; rfl) h2
    have e : mapRep (C.val : C →+* B) ρ'.hom = r := MonoidHom.ext fun g => Matrix.ext fun a b => hρ' g a b
    obtain ⟨f, hf, -⟩ := (hrep C).2 ρ' ((hQ C B C.val ρ'.hom).2 Subtype.val_injective (e ▸ h3))
    refine ⟨C.val.comp f, fun g a b => ?_⟩
    rw [← hρ', ← hf]
    rfl
  have hc : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B) a b,
      QCont l fun g => f (ρ.hom g a b) := fun B _ _ _ _ _ _ _ f a b =>
    (ptCont (l := l) R B f).1 Γ _ (ρ.cont a b)
  obtain ⟨n, P, φ₀, hφ₀, -, ⟨y, hy, hyP⟩, -⟩ := smoothCompl (l := l) E R ⊥ x bot_le (by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc f' _ hf'
    obtain ⟨r, h1, h2, h3⟩ := hlift B π hπ B' π' hπ' p hp hpc (mapRep (f' : R →+* B') ρ.hom)
      (MonoidHom.ext fun g => Matrix.ext fun a b => (hf' _).trans (congrArg _ (hxe g a b)))
      (hc B' f') ((hQ R B' f' _).1 hQρ)
    have h4 : ∀ g a b, p (r g a b) = f' (ρ.hom g a b) := fun g a b =>
      congrFun (congrFun (DFunLike.congr_fun h3 g) a) b
    obtain ⟨f, hf⟩ := hpt B π hπ r (fun g a b => by rw [← hpc, AlgHom.comp_apply, h4, hf', hxe]) h1 h2
    have := homExt (l := l) rbar R ρ hgen B' ((p.restrictScalars O).comp f) f' fun g a b => by
      rw [← h4, ← hf]; rfl
    exact ⟨f, bot_le, fun a => DFunLike.congr_fun this a⟩)
  obtain ⟨W, hW, hWz⟩ := lift_grading O X Γ ι rbar w R ρ (fun g => ρ₀.hom g)
    (fun g a b => by rw [← ρ₀.red]; exact ((res O O).commutes _).symm) hd hgen hst
  obtain ⟨h, rfl⟩ := origin_eq W x fun s => by
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, map_sub, hxe, AlgHom.commutes]
    exact sub_self _
  obtain ⟨u, φ, hφ, hφw, hu⟩ := gradedChart (l := l) E R W h P φ₀ hφ₀ ⟨y, hy, hyP⟩
  refine ⟨_, P, n, u, φ, hx, hφ, ⟨y, hy, hyP⟩, fun g a b => hφw _ _ (hW g a b), fun j => ?_⟩
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  let ev : (R →ₗ[O] E) →ₗ[E] (Γ → Matrix ι ι E) :=
    { toFun := fun δ g => Matrix.of fun a b => δ (ρ.hom g a b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ δ g a b, ev δ g a b = δ (ρ.hom g a b) := fun _ _ _ _ => rfl
  have hder : ∀ D : R → E, (∃ D' ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, ⇑D' = D) ↔
      ∃ y : R →ₐ[O] DualNumber E, ∀ f, (y f).fst = algebraMap O E (W.origin h f) ∧ (y f).snd = D f := by
    letI : Module Oᵐᵒᵖ E := Module.compHom E (RingEquiv.toOpposite O).symm.toRingHom
    haveI : IsCentralScalar O E := ⟨fun _ _ => rfl⟩
    exact der_hom O R E E ((Algebra.ofId O E).comp (W.origin h))
  have hO : ∀ δ ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, δ ∈ PtDer (W.origin h) E := fun δ hδ f g => by
    rw [hδ f g]
    simp [Algebra.smul_def]
  have hz : ∀ δ ∈ PtDer (W.origin h) E, ∀ g a b c, δ (ρ.hom g a b - algebraMap O R c) = δ (ρ.hom g a b) := by
    intro δ hδ g a b c
    have h1 : δ (1 * 1) = W.origin h 1 • δ 1 + W.origin h 1 • δ 1 := hδ 1 1
    rw [mul_one, map_one (W.origin h), one_smul, left_eq_add] at h1
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero, sub_zero]
  refine ⟨(wtDer W.part (W.origin h) E j).map ev, (hu j).trans ?_, fun s => ⟨?_, ?_⟩⟩
  · classical
    rw [← Submodule.range_subtype (wtDer W.part (W.origin h) E j), ← LinearMap.range_comp, Submodule.range_subtype,
      LinearMap.finrank_range_of_inj]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro δ hδ
    refine Subtype.ext ((der_extend O R X W h E).2 δ.1 (hO _ δ.2.1) fun s => ?_)
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, hz _ (hO _ δ.2.1)]
    exact congrFun (congrFun (congrFun hδ g) a) b
  · rintro ⟨δ, ⟨h1, h2⟩, rfl⟩
    obtain ⟨F, hF⟩ := (hder δ).1 ⟨δ, h1, rfl⟩
    refine ⟨⟨mapRep (F : R →+* DualNumber E) ρ.hom, fun g a b => TrivSqZeroExt.ext ?_ (hF _).2,
      (hQ R _ F _).1 hQρ⟩, fun a b => ?_, fun g a b hab => h2 _ hab _ (hW g a b)⟩
    · exact (hF _).1.trans (congrArg (algebraMap O E) (hxe g a b))
    · have := qcont_lin (hc (DualNumber E) F a b) (LinearMap.snd ℚ_[l] E E)
      simp only [hev, ← (hF _).2]
      exact this
  · rintro ⟨⟨r', h1, h2⟩, h3, h4⟩
    obtain ⟨F, hF⟩ := hpt (DualNumber E) (TrivSqZeroExt.fstHom E E E)
      (fun a ha => TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.2 (by rw [show a.fst = 0 from ha]; exact IsNilpotent.zero))
      r' (fun g a b => by rw [h1]; rfl) (fun a b => qcont_dual _ (by
        simp only [h1, ← hxe]
        exact hc E ((Algebra.ofId O E).comp (W.origin h)) a b) (by
        simp only [h1]
        exact h3 a b)) h2
    have hfst := homExt (l := l) rbar R ρ hgen E (((TrivSqZeroExt.fstHom E E E).restrictScalars O).comp F)
      ((Algebra.ofId O E).comp (W.origin h)) fun g a b => by
        show (F _).fst = algebraMap O E (W.origin h _)
        rw [hF, h1, hxe]
        rfl
    obtain ⟨δ, hδ, e⟩ := (hder fun f => (F f).snd).2 ⟨F, fun f => ⟨DFunLike.congr_fun hfst f, rfl⟩⟩
    have he : ∀ g a b, δ (ρ.hom g a b) = s g a b := fun g a b => by
      rw [e]
      show (F _).snd = _
      rw [hF, h1]
      rfl
    refine ⟨δ, ⟨hδ, hasWeight_of_generators W h δ (hO _ hδ) j fun t ht => ?_⟩, funext fun g => Matrix.ext (he g)⟩
    obtain ⟨g, a, b, e1, e2⟩ := hWz t
    rw [e1, hz _ (hO _ hδ), he, h4 g a b (e2 ▸ ht)]
end

