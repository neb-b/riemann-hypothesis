module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FiltByPositiveWeightOfTwoCharacterExtensionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem exists_character_filtration_of_sub_smul_mem {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (ρ : Representation E G V) (S : Set (G →* Eˣ)) (F' F'' : Submodule E V)
    (hQ : ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i)
    (hle : F' ≤ F'') (κ : G →* Eˣ) (hκ : κ ∈ S)
    (h : ∀ y ∈ F'', ∀ g : G, (ρ g) y - ((κ g : Eˣ) : E) • y ∈ F') :
    ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F'' ∧ ∀ i < n, F i ≤ F (i + 1) ∧
      ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
  classical
  have step : ∀ W : Submodule E V, F' ≤ W →
      (∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ∧ ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i) →
      ∀ v ∈ F'', ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = W ⊔ E ∙ v ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    rintro W hW ⟨n, F, h0, hn, hs⟩ v hv
    refine ⟨n + 1, fun i => if i = n + 1 then W ⊔ E ∙ v else F i, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      by_cases hin : i < n
      · have h1 : i ≠ n + 1 := by omega
        have h2 : i + 1 ≠ n + 1 := by omega
        simp only [h1, h2, if_false]
        exact hs i hin
      · have hi' : i = n := by omega
        subst hi'
        have h1 : i ≠ i + 1 := by omega
        simp only [h1, if_true, if_false, hn]
        exact ⟨le_sup_left, κ, hκ, v, rfl, fun g => hW (h v hv g)⟩
  have key : ∀ s : Finset V, (↑s : Set V) ⊆ F'' →
      ∃ (n : ℕ) (F : ℕ → Submodule E V), F 0 = ⊥ ∧ F n = F' ⊔ Submodule.span E (↑s : Set V) ∧
        ∀ i < n, F i ≤ F (i + 1) ∧
        ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ E ∙ x ∧ ∀ g : G, (ρ g) x - ((κ g : Eˣ) : E) • x ∈ F i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hQ
    · intro a s _ ih hs
      rw [Finset.coe_insert] at hs ⊢
      have h1 := step (F' ⊔ Submodule.span E ↑s) le_sup_left
        (ih (fun z hz => hs (Set.mem_insert_of_mem a hz))) a (hs (Set.mem_insert a _))
      rw [Submodule.span_insert, sup_comm (E ∙ a), ← sup_assoc]
      exact h1
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian F'' : F''.FG)
  obtain ⟨n, F, h0, hn, hst⟩ := key s (by rw [← hs]; exact Submodule.subset_span)
  refine ⟨n, F, h0, ?_, hst⟩
  rw [hn, hs, sup_eq_right.mpr hle]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ wa wb : ℤ, 1 ≤ wa → 1 ≤ wb → (∀ g, φ g ∈ Iq l → a g = cycA l l B (φ g) ^ wa) → (∀ g, φ g ∈ Iq l → b g = cycA l l B (φ g) ^ wb) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), FiltBy (resCoef E (ext2 a b x hx)) {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ a b _ _ wa wb hwa hwb hIa hIb x hx
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  have hmemI : ∀ c : B, c - algebraMap E B (π c) ∈ RingHom.ker (π : B →+* E) := by
    intro c
    rw [RingHom.mem_ker]
    simp
  obtain ⟨M, hM⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  have hMz : ∀ c ∈ I ^ M, c = 0 := by
    intro c hc
    rw [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at hc
    exact hc
  have hstep : ∀ (c : B) (k : ℕ) (y : B), y ∈ I ^ k →
      c * y - algebraMap E B (π c) * y ∈ I ^ (k + 1) := by
    intro c k y hy
    rw [← sub_mul, pow_succ']
    exact Ideal.mul_mem_mul (hmemI c) hy
  have hcyc : ∀ σ, Units.map (π : B →* E) (cycA l l B σ) = cycA l l E σ := by
    intro σ
    ext
    simp only [cycA, Units.coe_map, MonoidHom.comp_apply, MonoidHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] E B,
      AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E _).symm
  have hwt : ∀ (c : G →* Bˣ) (w : ℤ), (∀ g, φ g ∈ Iq l → c g = cycA l l B (φ g) ^ w) →
      HasWeight φ ((Units.map (π : B →* E)).comp c) w := by
    intro c w hc
    refine ⟨⊤, by simp, fun g _ hg => ?_⟩
    rw [MonoidHom.comp_apply, hc g hg, map_zpow, hcyc]
  have hsm : ∀ (u : Bˣ) (y : B × B), ((Units.map (π : B →* E) u : Eˣ) : E) • y =
      (algebraMap E B (π u) * y.1, algebraMap E B (π u) * y.2) := by
    intro u y
    ext <;> simp [Algebra.smul_def]
  unfold FiltBy
  set S : Set (G →* Eˣ) := {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} with hS
  have hSa : (Units.map (π : B →* E)).comp a ∈ S := ⟨wa, hwa, hwt a wa hIa⟩
  have hSb : (Units.map (π : B →* E)).comp b ∈ S := ⟨wb, hwb, hwt b wb hIb⟩
  set ρ := resCoef E (ext2 a b x hx) with hρdef
  have hρ : ∀ g (y : B × B), ρ g y = ((a g : B) * y.1 + x g * (b g : B) * y.2, (b g : B) * y.2) :=
    fun g y => rfl
  set P1 : ℕ → Submodule E (B × B) := fun k => ((I ^ k).restrictScalars E).prod ⊥ with hP1
  set P2 : ℕ → Submodule E (B × B) := fun k => (⊤ : Submodule E B).prod ((I ^ k).restrictScalars E)
    with hP2
  have mP1 : ∀ k z, z ∈ P1 k ↔ z.1 ∈ I ^ k ∧ z.2 = 0 := by
    intro k z
    simp [hP1, Submodule.mem_prod]
  have mP2 : ∀ k z, z ∈ P2 k ↔ z.2 ∈ I ^ k := by
    intro k z
    simp [hP2, Submodule.mem_prod]
  have Q0 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = ⊥ ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i :=
    ⟨0, fun _ => ⊥, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hQ1 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P1 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      refine exists_character_filtration_of_sub_smul_mem ρ S ⊥ (P1 (M - 0)) Q0 bot_le _ hSa ?_
      intro y hy g
      rw [mP1, Nat.sub_zero] at hy
      have hy0 : y = 0 := Prod.ext (hMz _ hy.1) hy.2
      subst hy0
      simp
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSa ?_
        · intro z hz
          rw [mP1] at hz ⊢
          exact ⟨Ideal.pow_le_pow_right (Nat.le_succ _) hz.1, hz.2⟩
        · intro y hy g
          rw [mP1] at hy
          rw [mP1, MonoidHom.comp_apply, hsm, hρ]
          refine ⟨?_, by simp [hy.2]⟩
          simpa [hy.2] using hstep (a g : B) _ y.1 hy.1
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  have T12 : ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 M ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    have h1 := hQ1 M
    rw [Nat.sub_self] at h1
    refine exists_character_filtration_of_sub_smul_mem ρ S _ _ h1 ?_ _ hSa ?_
    · intro z hz
      rw [mP1] at hz
      rw [mP2, hz.2]
      exact zero_mem _
    · intro y hy g
      rw [mP2] at hy
      have hy2 := hMz _ hy
      rw [mP1, MonoidHom.comp_apply, hsm, hρ]
      exact ⟨by simp, by simp [hy2]⟩
  have hQ2 : ∀ j : ℕ, ∃ (n : ℕ) (F : ℕ → Submodule E (B × B)), F 0 = ⊥ ∧ F n = P2 (M - j) ∧
      ∀ i < n, F i ≤ F (i + 1) ∧ ∃ κ ∈ S, ∃ z, F (i + 1) = F i ⊔ E ∙ z ∧
        ∀ g : G, (ρ g) z - ((κ g : Eˣ) : E) • z ∈ F i := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero]
      exact T12
    | succ j ih =>
      by_cases hj : j < M
      · have e : M - j = (M - (j + 1)) + 1 := by omega
        rw [e] at ih
        refine exists_character_filtration_of_sub_smul_mem ρ S _ _ ih ?_ _ hSb ?_
        · intro z hz
          rw [mP2] at hz ⊢
          exact Ideal.pow_le_pow_right (Nat.le_succ _) hz
        · intro y hy g
          rw [mP2] at hy
          rw [mP2, MonoidHom.comp_apply, hsm, hρ]
          simpa using hstep (b g : B) _ y.2 hy
      · have e : M - (j + 1) = M - j := by omega
        rw [e]
        exact ih
  obtain ⟨n, F, h0, hn, hs⟩ := hQ2 M
  have htop : P2 (M - M) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [mP2, Nat.sub_self]
    simp
  exact ⟨n, F, h0, hn.trans htop, hs⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallineConjByInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.LCrConj

open TensorProduct

private theorem isCr_transfer {l : ℕ} [Fact l.Prime] {G A A' V V' : Type} [Group G] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [CommRing A']
    [Algebra ℚ_[l] A'] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V']
    (φ : G →* GQ l) (ρ : Representation A G V)
    (ρ' : Representation A' G V') (f : V ≃ₗ[ℚ_[l]] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsCr φ ρ ↔ IsCr φ ρ' := by
  let F : V ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hF : ∀ g x, F (actC φ (resCoef ℚ_[l] ρ) g x) = actC φ (resCoef ℚ_[l] ρ') g (F x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] ρ)).map F.toLinearMap = Dcr φ (resCoef ℚ_[l] ρ') := by
    ext x
    obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      ← hF, F.injective.eq_iff]
  unfold IsCr
  rw [← hD, LinearEquiv.finrank_map_eq, f.finrank_eq]

private theorem isCr_conjGL {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}
    (φ : G →* GQ l) (r : G →* GL (Fin n) A) (h : GL (Fin n) A) :
    IsCr φ (colRep r) ↔ IsCr φ (colRep (conjGL h r)) :=
  isCr_transfer φ (colRep r) (colRep (conjGL h r))
    ((Matrix.toLinearEquiv' (h : Matrix (Fin n) (Fin n) A) h.invertible).restrictScalars ℚ_[l]) fun g x => by
      simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]

private def glPart {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G)
    (r : G →* GG (m := m) (R := R))
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff' {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]
    (r : GQ l →* GG (m := 3) (R := B))
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glPart D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glPart D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

end GlobalTheory.LCrConj


open GlobalTheory.LCrConj in
theorem GlobalTheory.LCrConj.main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _ _ r h hm _ hc
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have hm' : HasMult D.η (conjBy h r) := fun g => (by simp [conjBy] : (conjBy h r g).right = (r g).right).trans (hm g)
  have h1' : ∀ g ∈ D.HL, (conjBy h r g).right = 1 := fun g hg => (hm' g).trans hg.1
  have he : glPart D.HL (conjBy h r) h1' = conjGL h (glPart D.HL r h1) := by
    ext g : 1
    have h2 : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by rw [map_inv]; rfl
    show (conjBy h r g).left = _
    rw [h2, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, h1 g g.2, mul_one, sgnAct_one,
      sgnAct_one]
    rfl
  rw [isLCr_iff' D r h1, isCr_conjGL _ _ h, ← he, ← isLCr_iff']
  exact hc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem push_mat_eq_mat_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : GQ l) : (push f r s).mat = (r s).mat.map f := by
  rfl
private theorem sh_push_eq_sh_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) (s : GQ l) : D.sh (push f r) a s = (D.sh r a s).map f := by
  ext i j
  simp only [Dat3.sh, Matrix.sub_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, push_mat_eq_mat_map, map_sub]
  split_ifs <;> simp
private theorem tr_push_algHom_eq_map_tr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) : D.tr (push f r) a = f (D.tr r a) := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Dat3.tr, sh_push_eq_sh_map, push_mat_eq_mat_map, h, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
private theorem map_dd_eq_dd_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (a : Fin 3) : f (D.dd r a) = D.dd (push f r) a := by
  simp only [Dat3.dd, tr_push_algHom_eq_map_tr, map_sub, map_mul, AlgHom.commutes]
private theorem map_coeff_charpoly_sub_prod_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : GQ l) (i : ℕ) : f (((r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) = (((push f r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) := by
  have h1 : (push f r s).mat.charpoly = (r s).mat.charpoly.map (f : C →+* C') := by
    rw [push_mat_eq_mat_map]
    exact Matrix.charpoly_map _ _
  have h2 : ∀ a : Fin 3, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))) = (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))).map (f : C →+* C') := by
    intro a
    simp
  rw [h1, Finset.prod_congr rfl (fun a _ => h2 a), ← Polynomial.map_prod, ← Polynomial.map_sub, Polynomial.coeff_map]
  rfl
private theorem map_sh_triple_prod_apply_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)) (s : Fin 3 → GQ l) (i j : Fin 3) : f ((D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2)) i j) = (D.sh (push f r) 0 (s 0) * D.sh (push f r) 1 (s 1) * D.sh (push f r) 2 (s 2)) i j := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  simp only [sh_push_eq_sh_map, h, Matrix.map_apply]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_map_algHom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG (m := 3) (R := C)), (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) ∧ (∀ a, f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a) ∧ f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) := by
  intro l _ O _ _ _ D C C' _ _ _ _ f r
  refine ⟨?_, fun a => map_dd_eq_dd_push D f r a, ?_⟩
  · simp only [Dat3.ordIdeal]
    rw [Ideal.map_span, Set.image_union]
    congr 2
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, rfl⟩, rfl⟩
        exact ⟨s, hs, i, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
      · rintro ⟨s, hs, i, rfl⟩
        exact ⟨_, ⟨s, hs, i, rfl⟩, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩
        exact ⟨s, hs, i, j, map_sh_triple_prod_apply_eq_push D f r s i j⟩
      · rintro ⟨s, hs, i, j, rfl⟩
        exact ⟨_, ⟨s, hs, i, j, rfl⟩, map_sh_triple_prod_apply_eq_push D f r s i j⟩
  · simp only [Dat3.del, map_mul, map_natCast, map_dd_eq_dd_push]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.PositiveScalarRepOfCharacterPositiveWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.PosModule

theorem main : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ {N : Type} [AddCommGroup N] [Module B N] [Module E N] [Module ℚ_[l] N] [IsScalarTower E B N] [IsScalarTower ℚ_[l] E N] [IsScalarTower ℚ_[l] B N] [FiniteDimensional ℚ_[l] N] [TopologicalSpace N] [IsModuleTopology ℚ_[l] N] [IsTopologicalAddGroup N] (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ContAction ρ ∧ Positive φ ρ := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI N _ _ _ _ _ _ _ _ _ _ _ ρ hρ

  let bil : B →ₗ[ℚ_[l]] N →ₗ[ℚ_[l]] N := LinearMap.mk₂ ℚ_[l] (fun b x => b • x) (fun _ _ _ => add_smul _ _ _)
    (fun c b x => smul_assoc c b x) (fun _ _ _ => smul_add _ _ _)
    (fun c b x => by rw [← algebraMap_smul B c x, ← algebraMap_smul B c (b • x), smul_smul, smul_smul, mul_comm])
  have hbil : Continuous (fun p : B × N => p.1 • p.2) := IsModuleTopology.continuous_bilinear_of_finite_left bil
  have hcont : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ]
    exact hbil.comp ((hχc.comp continuous_fst).prodMk continuous_snd)
  refine ⟨hcont, ?_⟩
  have hcs : ContinuousConstSMul E N := ⟨fun c => by
    let f : N →ₗ[ℚ_[l]] N :=
      { toFun := fun x => c • x
        map_add' := smul_add c
        map_smul' := fun r x => by
          simp only [RingHom.id_apply]
          rw [← algebraMap_smul E r x, ← algebraMap_smul E r (c • x), smul_smul, smul_smul, mul_comm] }
    exact IsModuleTopology.continuous_of_linearMap f⟩
  have hIne : ∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l E (φ g) ^ w : Eˣ) : E) • x := fun g hg x => by
    rw [hρ, hχI g hg, ← algebraMap_smul B (((cycA l l E (φ g) ^ w : Eˣ) : E)) x,
      ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    rfl
  have hcr : IsCr φ ρ := crUnr φ hφ ρ hcont w hIne
  have hdr : IsDr φ ρ := (isCrys_isDR_restrict_openSubgroup φ hφ ρ hcont).1 hcr
  refine ⟨hdr, ?_⟩

  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have : Module.Finite B N := Module.Finite.of_restrictScalars_finite ℚ_[l] B N
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := N)
  let ρB : Representation B G N :=
    { toFun := fun g => ((χ g : Bˣ) : B) • LinearMap.id
      map_one' := by ext; simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp only [map_mul, Units.val_mul, LinearMap.smul_apply, LinearMap.id_apply, Module.End.mul_apply, mul_smul] }
  let κ : G →* Eˣ := (Units.map (π : B →* E)).comp χ
  have hres : resCoef E ρB = ρ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [hρ]
    rfl
  have hκ : κ ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
    refine ⟨w, hw, ⊤, by simp, fun g _ hg => ?_⟩
    apply Units.ext
    change π ((χ g : Bˣ) : B) = _
    rw [hχI g hg, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    exact π.commutes _
  rw [← hres]
  refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ ρB _ s (fun _ => κ) hs (fun _ => hκ) fun g j => ?_
  have hm : ((χ g : B) - algebraMap E B (π (χ g : B))) • s j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B N) :=
    Submodule.smul_mem_smul (by simp) trivial
  convert hm using 1
  rw [sub_smul, algebraMap_smul]
  rfl

end GlobalTheory.PosModule
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementNotMemMinimalPrimesReducedOrdin
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

end GlobalTheory.OrdLoc
end

