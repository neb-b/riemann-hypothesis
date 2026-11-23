module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationFibreProductAmalgamationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
open UpperTheory.V.U3 (GG)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_deformation_fibre_product_amalgamation : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (πC : C →ₐ[E] E) (hπC : ∀ a, πC a = 0 → IsNilpotent a) (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T] [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T] [IsScalarTower ℚ_[l] E T] (πT : T →ₐ[E] E) (hπT : ∀ a, πT a = 0 → IsNilpotent a) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C), π.comp p₁ = πT → πC.comp p₂ = πT → (∀ b c, π b = πC c → ∃! t, p₁ t = b ∧ p₂ t = c) → ∀ (r₁ : GQ l →* GG (m := 3) (R := B)) (r₂ : GQ l →* GG (m := 3) (R := C)), D.InDcr (π : B →+* E) r₁ → D.InDcr (πC : C →+* E) r₂ → ∃ r : GQ l →* GG (m := 3) (R := T), D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ C _ _ _ _ _ _ _ _ _ _ πC hπC T _ _ _ _ _ _ _ _ _ _ πT hπT p₁ p₂ h1 h2 huniq r₁ r₂ hr₁ hr₂
  have hAmalgamate :
    ∃ r : GQ l →* GG (m := 3) (R := T),
      D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧
        (GG.map (p₂ : T →+* C)).comp r = r₂ := by
    have hpt : ∀ x, π (p₁ x) = πC (p₂ x) := fun x => by
      rw [← AlgHom.comp_apply, h1, ← AlgHom.comp_apply, h2]
    have hf : ∀ x y, (p₁ : T →+* B) x = (p₁ : T →+* B) y → (p₂ : T →+* C) x = (p₂ : T →+* C) y → x = y := by
      intro x y e1 e2
      obtain ⟨t, -, ht⟩ := huniq (p₁ x) (p₂ x) (hpt x)
      exact (ht x ⟨rfl, rfl⟩).trans (ht y ⟨e1.symm, e2.symm⟩).symm
    have hq : ∀ b c, (π : B →+* E) b = (πC : C →+* E) c → ∃ x, (p₁ : T →+* B) x = b ∧ (p₂ : T →+* C) x = c :=
      fun b c e => (huniq b c e).exists
    have hred : (GG.map (π : B →+* E)).comp r₁ = (GG.map (πC : C →+* E)).comp r₂ := hr₁.red.trans hr₂.red.symm
    have hglue : ∃ r : GQ l →* GG (m := 3) (R := T),
        (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
      have hg : ∀ g, GG.map (π : B →+* E) (r₁ g) = GG.map (πC : C →+* E) (r₂ g) :=
        fun g => DFunLike.congr_fun hred g
      choose n hn₁ hn₂ using fun g =>
        OrdinaryDeformation.glue_GL (p₁ : T →+* B) (p₂ : T →+* C) (π : B →+* E)
          (πC : C →+* E) hf hq (r₁ g).left (r₂ g).left (congrArg SemidirectProduct.left (hg g))
      let x : GQ l → GG (m := 3) (R := T) := fun g => ⟨n g, (r₁ g).right⟩
      have hx₁ (g : GQ l) : GG.map (p₁ : T →+* B) (x g) = r₁ g :=
        SemidirectProduct.ext (hn₁ g) rfl
      have hx₂ (g : GQ l) : GG.map (p₂ : T →+* C) (x g) = r₂ g := by
        refine SemidirectProduct.ext (hn₂ g) ?_
        simpa only [GG.map_right] using congrArg SemidirectProduct.right (hg g)
      have hsep {a b : GG (m := 3) (R := T)}
          (ha : GG.map (p₁ : T →+* B) a = GG.map (p₁ : T →+* B) b)
          (hb : GG.map (p₂ : T →+* C) a = GG.map (p₂ : T →+* C) b) : a = b := by
        refine SemidirectProduct.ext (Units.ext (Matrix.ext fun i j => hf _ _ ?_ ?_)) ?_
        · exact congrArg (fun u => u.mat i j) ha
        · exact congrArg (fun u => u.mat i j) hb
        · simpa only [GG.map_right] using congrArg SemidirectProduct.right ha
      refine ⟨MonoidHom.mk' x (fun g g' => hsep ?_ ?_), MonoidHom.ext hx₁, MonoidHom.ext hx₂⟩
      · rw [map_mul, hx₁, hx₁, hx₁, map_mul]
      · rw [map_mul, hx₂, hx₂, hx₂, map_mul]
    obtain ⟨r, e1, e2⟩ := hglue
    refine ⟨r, ?_, e1, e2⟩
    let f₁ := (p₁.restrictScalars ℚ_[l]).toLinearMap
    let f₂ := (p₂.restrictScalars ℚ_[l]).toLinearMap
    rw [← e1] at hr₁
    rw [← e2] at hr₂
    have hc : ∀ a b, QCont l fun g => (r g).mat a b := fun a b =>
      OrdinaryDeformation.qcont_pair f₁ f₂ hf (hr₁.cont a b) (hr₂.cont a b)
    have hm : HasMult D.η r := hr₁.mult
    have hπcomp : (π : B →+* E).comp (p₁ : T →+* B) = (πT : T →+* E) :=
      RingHom.ext fun x => by
        change π (p₁ x) = πT x
        rw [← AlgHom.comp_apply, h1]
    refine ⟨hm, ?_, hc, ?_⟩
    · rw [← hπcomp]
      exact hr₁.red
    obtain ⟨ρ₁, hρ₁, hcr₁⟩ := hr₁.cr
    obtain ⟨ρ₂, hρ₂, hcr₂⟩ := hr₂.cr
    let _ : TopologicalSpace B := moduleTopology ℚ_[l] B
    have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
    have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
    let _ : TopologicalSpace C := moduleTopology ℚ_[l] C
    have : IsModuleTopology ℚ_[l] C := ⟨rfl⟩
    have : IsTopologicalRing C := IsModuleTopology.isTopologicalRing ℚ_[l] C
    let _ : TopologicalSpace T := moduleTopology ℚ_[l] T
    have : IsModuleTopology ℚ_[l] T := ⟨rfl⟩
    have : IsTopologicalRing T := IsModuleTopology.isTopologicalRing ℚ_[l] T
    have c₁ : ContAction (resCoef ℚ_[l] (colRep ρ₁)) := OrdinaryDeformation.cont_col ρ₁ fun a b => by
      simp only [hρ₁]
      exact (hr₁.cont a b).comp (continuous_subtype_val (p := fun g => g ∈ D.HL))
    have c₂ : ContAction (resCoef ℚ_[l] (colRep ρ₂)) := OrdinaryDeformation.cont_col ρ₂ fun a b => by
      simp only [hρ₂]
      exact (hr₂.cont a b).comp (continuous_subtype_val (p := fun g => g ∈ D.HL))
    have cprod : ContAction ((resCoef ℚ_[l] (colRep ρ₁)).prod (resCoef ℚ_[l] (colRep ρ₂))) :=
      (c₁.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (c₂.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    have hHL := OrdinaryDeformation.HL_emb D
    have hprod := (isCrys_isDR_prod _ hHL _ _ c₁ c₂).1 hcr₁ hcr₂
    refine ⟨(glPart D.η r hm).comp (Subgroup.inclusion inf_le_left), fun g => rfl, ?_⟩
    refine ((isCrys_isDR_sub_quot _ hHL _ _ (OrdinaryDeformation.cont_col _ fun a b => ?_) cprod
      ((f₁.compLeft (Fin 3)).prod (f₂.compLeft (Fin 3))) fun g x => ?_).1
      (fun x y h => ?_)).1 hprod
    · exact (hc a b).comp continuous_subtype_val
    · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
      · change _ = Matrix.mulVec (ρ₁ g : Matrix (Fin 3) (Fin 3) B) _ a
        rw [hρ₁]
        exact RingHom.map_mulVec (p₁ : T →+* B) _ x a
      · change _ = Matrix.mulVec (ρ₂ g : Matrix (Fin 3) (Fin 3) C) _ a
        rw [hρ₂]
        exact RingHom.map_mulVec (p₂ : T →+* C) _ x a
    · exact funext fun a => hf _ _ (congrFun (congrArg Prod.fst h) a) (congrFun (congrArg Prod.snd h) a)
  exact hAmalgamate
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineTwistByUnramifiedCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

noncomputable section

namespace GlobalTheory.OrdTwist

theorem tor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (t : Rˣ) :
    Matrix.GeneralLinearGroup.map f (tor R t) = tor S (Units.map (f : R →* S) t) := by
  apply Units.ext
  change (Matrix.diagonal _).map f = Matrix.diagonal _
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  exact congrArg Units.val (map_zpow (Units.map (f : R →* S)) _ _)

theorem residualRep_map_ringHom {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ) (ψ : G →* Rˣ) :
    (GG.map f).comp (r0 η ψ) = r0 η ((Units.map (f : R →* S)).comp ψ) := by
  ext1 g
  refine SemidirectProduct.ext ?_ ?_
  · exact tor_map f (ψ g)
  · rfl

section Cr

variable {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
  [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A]
  [IsTopologicalRing A]

theorem cont_ch {G : Type} [Group G] [TopologicalSpace G] {κ : G →* Aˣ} (h : Continuous κ) :
    ContAction (chRep κ) :=
  (Units.continuous_val.comp (h.comp continuous_fst)).mul continuous_snd

theorem cont_prod {G V V' : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module A V]
    [TopologicalSpace V] [AddCommGroup V'] [Module A V'] [TopologicalSpace V'] {ρ : Representation A G V}
    {ρ' : Representation A G V'} (h : ContAction ρ) (h' : ContAction ρ') : ContAction (ρ.prod ρ') :=
  (h.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk (h'.comp (continuous_fst.prodMk continuous_snd.snd))

theorem isCr_char (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Aˣ) (hκ : Continuous κ)
    (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l A g ^ w) : IsCr H.subtype (chRep (κ.comp H.subtype)) :=
  crUnr H.subtype hH.isOpenEmbedding_subtypeVal _ (cont_ch (hκ.comp continuous_subtype_val)) w fun g hg x => by
    rw [Subgroup.subtype_apply, ← hw g g.2 hg]
    rfl

theorem isCr_diag (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : Fin 3 → GQ l →* Aˣ)
    (hκ : ∀ a, Continuous (κ a)) (w : Fin 3 → ℤ) (hw : ∀ a, ∀ g ∈ H, g ∈ Iq l → κ a g = cycA l l A g ^ w a)
    (ρ : ↥H →* GL (Fin 3) A)
    (hρ : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun a => (κ a g : A)) :
    IsCr H.subtype (colRep ρ) := by
  have hφ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  have hc : ∀ a, ContAction (chRep ((κ a).comp H.subtype)) := fun a =>
    cont_ch ((hκ a).comp continuous_subtype_val)
  have hcr := fun a => isCr_char H hH (κ a) (hκ a) (w a) (hw a)
  have hp := fun a g x => R0.proj_diag (κ := fun a => (κ a).comp H.subtype) hρ a g x
  have h0 : ContAction (colRep ρ) := continuous_pi fun a => by
    have := (hc a).comp (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd) :
      Continuous fun p : ↥H × (Fin 3 → A) => (p.1, p.2 a))
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

end Cr

end GlobalTheory.OrdTwist

theorem GlobalTheory.OrdTwist.twist_inDcr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (u : GQ l →* Bˣ), QCont l (fun g => (u g : B)) → (∀ g ∈ Iq l, u g = 1) → (∀ g, IsNilpotent ((u g : B) - 1)) → D.InDcr (π : B →+* E) (r0 D.η ((Units.map (algebraMap O B : O →* B)).comp D.Ψ * u)) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π _ u hc hI hu
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  let j : Oˣ →* Bˣ := Units.map (algebraMap O B : O →* B)
  let ψ : GQ l →* Bˣ := j.comp D.Ψ * u
  have hψv : ∀ g, (ψ g : B) = algebraMap O B (D.Ψ g : O) * (u g : B) := fun g => rfl
  have hu1 : ∀ g, π (u g : B) = 1 := fun g => by
    have h := (hu g).map π
    rw [map_sub, map_one] at h
    exact sub_eq_zero.1 h.eq_zero
  have hπO : ∀ x : O, π (algebraMap O B x) = algebraMap O E x := fun x => by
    rw [IsScalarTower.algebraMap_apply O E B, AlgHom.commutes]
    rfl
  have hΨ : Continuous fun g => algebraMap O B (D.Ψ g : O) :=
    (ptCont (l := l) O B (Algebra.ofId O B)).1 _ _ D.Ψ_cont
  have hψ : Continuous fun g => (ψ g : B) := by
    simp only [hψv]
    exact hΨ.mul hc
  have hψi : Continuous fun g => (((ψ g)⁻¹ : Bˣ) : B) := UpperTheory.continuous_units_inv_of_continuous_coe_finite_Qp_algebra (l := l) (fun g => ψ g) hψ
  have hψ' : Continuous ψ := Units.continuous_iff.2 ⟨hψ, hψi⟩
  refine ⟨fun g => rfl, ?_, fun a b => ?_, ?_⟩
  · show (GG.map (π : B →+* E)).comp (r0 D.η ψ) = (GG.map (algebraMap O E)).comp (r0 D.η D.Ψ)
    rw [residualRep_map_ringHom, residualRep_map_ringHom]
    congr 1
    ext g
    change π ((ψ g : Bˣ) : B) = algebraMap O E (D.Ψ g : O)
    rw [hψv, map_mul, hu1, mul_one, hπO]
  · show Continuous fun g => ((r0 D.η ψ g).left : Matrix (Fin 3) (Fin 3) B) a b
    simp only [unitaryThreeReflection_left, tor_val]
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.diagonal_apply_eq]
      fin_cases a
      · simpa [wt1] using hψ
      · simpa [wt1] using (continuous_const : Continuous fun _ : GQ l => (1 : B))
      · simpa [wt1] using hψi
    · simp only [Matrix.diagonal_apply_ne _ hab]
      exact continuous_const
  · have hker : D.η.ker = GK D.Kv := Subgroup.ext D.η_ker
    have hH : IsOpen (D.HL : Set (GQ l)) := by
      have h1 : IsOpen (GK D.Kv : Set (GQ l)) := by
        haveI := D.Kv.2
        exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
      have := h1.inter D.τ_open
      rwa [← hker] at this
    let κ : Fin 3 → GQ l →* Bˣ := fun a => (zpowGroupHom (wt1 a)).comp ψ
    have hcyc : ∀ g, j (cycA l l O g) = cycA l l B g := fun g =>
      Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O B _).symm
    refine ⟨((tor B).comp ψ).comp D.HL.subtype, fun g => rfl, ?_⟩
    refine isCr_diag D.HL hH κ (fun a => hψ'.zpow _) (fun a => (D.e : ℤ) * wt1 a) (fun a g hg hgI => ?_) _
      fun g => rfl
    have hτ : D.τ g = 1 := hg.2
    change ψ g ^ wt1 a = _
    have : ψ g = cycA l l B g ^ D.e := by
      change j (D.Ψ g) * u g = _
      rw [hI g hgI, mul_one, D.Ψ_I g hgI, hτ, mul_one, map_pow, hcyc]
    rw [this, ← zpow_natCast, ← zpow_mul]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankCocyclesEqCrysAddDualInvOfPositive
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CocycleDim

theorem sandwich {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B S Z : Submodule E M)
    (hBS : B ≤ S) (hSZ : S ≤ Z) [Module.Finite E B]
    (hQ : Module.Finite E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ)) :
    Module.Finite E S ∧
      finrank E S = finrank E ↥((S.comap Z.subtype).map (B.comap Z.subtype).mkQ) + finrank E B := by
  let f : S →ₗ[E] (Z ⧸ B.comap Z.subtype) := (B.comap Z.subtype).mkQ ∘ₗ Submodule.inclusion hSZ
  have hr : LinearMap.range f = (S.comap Z.subtype).map (B.comap Z.subtype).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]
  have hk : LinearMap.ker f = B.comap S.subtype := by
    ext x
    simp [f]
  have eB := Submodule.comapSubtypeEquivOfLe hBS
  have hkf : Module.Finite E ↥(LinearMap.ker f) := by
    rw [hk]; exact Module.Finite.equiv eB.symm
  have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
  have hS : Module.Finite E S := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
    · rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf
    · rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf
  refine ⟨hS, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]

theorem top_image {E M : Type} [Field E] [AddCommGroup M] [Module E M] (B Z : Submodule E M) :
    (Z.comap Z.subtype).map (B.comap Z.subtype).mkQ = ⊤ := by
  rw [Submodule.comap_subtype_self, Submodule.map_top, Submodule.range_mkQ]

end GlobalTheory.CocycleDim

open GlobalTheory.CocycleDim in
theorem GlobalTheory.cocycleDim_positive : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → Module.Finite E ↥(Z1 ρ) ∧ finrank E ↥(Z1 ρ) = finrank E ↥(finiteCocycles φ ρ) + finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨hH0, -, hfinf, hdimf⟩ := posBasic hP φ hφ ρ hρ hpos
  obtain ⟨hf1, -, e1, e2⟩ := tateRat hP (v := l) (l := l) φ hφ ρ hρ
  rw [if_pos rfl, hH0, finrank_bot, e2] at e1
  have hBf : Module.Finite E ↥(B1 ρ) := by
    unfold B1; infer_instance
  have hBS := (z1fMap (l := l) φ ρ ρ).1 hρ
  have hSZ : finiteCocycles φ ρ ≤ Z1 ρ := fun c h => h.1
  obtain ⟨-, hSd⟩ := sandwich _ _ _ hBS hSZ hfinf
  replace hSd : finrank E ↥(finiteCocycles φ ρ) = finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(B1 ρ) := hSd
  have hQ : Module.Finite E ↥(((Z1 ρ).comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ) := by
    rw [top_image]; exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl).symm
  obtain ⟨hZ, hZd⟩ := sandwich _ _ _ (coboundaries_le_cocycles ρ hρ) le_rfl hQ
  rw [top_image, finrank_top] at hZd
  refine ⟨hZ, ?_⟩
  change finrank E ↥(Z1 ρ) = finrank E (H1 ρ) + finrank E ↥(B1 ρ) at hZd
  rw [hZd, hSd, e1, hdimf]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallineConjByInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLCrystalline_conjBy_invariant : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  first | exact @GlobalTheory.LCrConj.main | exact GlobalTheory.LCrConj.main | (intros; apply GlobalTheory.LCrConj.main <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsUnitCharacterDiffAtChosenInertiaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_characterDiff_at_chosenInertia : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B], (∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D)) - algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b (GlobalTheory.OrdLoc.s0 D)))) ∧ ∀ a, IsUnit (algebraMap O B (GlobalTheory.OrdLoc.cc D a)) := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _
  obtain ⟨-, -, -, hΨ, hs0⟩ := _root_.GlobalTheory.OrdLoc.hl_basic D
  rw [UpperTheory.V.Loc.Dat3.IsInertiaInfiniteCyclotomic.eq_1] at hs0
  obtain ⟨hH, hI, hc⟩ := hs0
  have key : ∀ a : Fin 3, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 =
      algebraMap ℤ_[l] O ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 a) : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro a
    rw [UpperTheory.V.UnitaryThreeInertia.psi.eq_1, hΨ _ hH hI, cycA.eq_1, MonoidHom.comp_apply, ← map_pow, ← map_zpow,
      Units.coe_map, zpow_mul, zpow_natCast]
    rfl
  have unitQ : ∀ z : ℤ_[l], z ≠ 0 → IsUnit (algebraMap ℤ_[l] B z) := by
    intro z hz
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]
    apply IsUnit.map
    apply Ne.isUnit
    simpa using hz
  have expo : ∀ a b : Fin 3, a ≠ b → (D.e : ℤ) * wt1 a ≠ (D.e : ℤ) * wt1 b := by
    intro a b hab hw
    apply hab
    have he0 : (D.e : ℤ) ≠ 0 := by
      have : (1 : ℤ) ≤ D.e := by exact_mod_cast D.e_pos
      omega
    have hw' := mul_left_cancel₀ he0 hw
    rw [wt1.eq_1, wt1.eq_1] at hw'
    apply Fin.ext
    omega
  have ne : ∀ m n : ℤ, m ≠ n →
      ((cyc l l D.s0 ^ m : ℤ_[l]ˣ) : ℤ_[l]) - ((cyc l l D.s0 ^ n : ℤ_[l]ˣ) : ℤ_[l]) ≠ 0 := by
    intro m n hmn hz
    apply hc
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨m - n, sub_ne_zero.mpr hmn, ?_⟩
    have hu : cyc l l D.s0 ^ m = cyc l l D.s0 ^ n := Units.ext (sub_eq_zero.mp hz)
    rw [zpow_sub, hu, mul_inv_cancel]
  have diff : ∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) -
      algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
    intro a b hab
    rw [key a, key b, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_sub]
    exact unitQ _ (ne _ _ (expo a b hab))
  refine ⟨diff, ?_⟩
  intro a
  rw [UpperTheory.V.Loc.Dat3.cc.eq_1, map_mul, map_sub, map_sub]
  refine IsUnit.mul (diff a (a + 1) ?_) (diff a (a + 2) ?_)
  · fin_cases a <;> decide
  · fin_cases a <;> decide
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem conjBy_left {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C)
    (r : G →* UpperTheory.V.U3.GG (m := 3) (R := C)) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  show (GG.ofGL h * r g * (GG.ofGL h)⁻¹).left = _
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  simp only [SemidirectProduct.right_inl, SemidirectProduct.left_inl, SemidirectProduct.mul_right, hg, mul_one, inv_one, map_one, MulAut.one_apply]

theorem conjBy_mat {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C)
    (r : G →* UpperTheory.V.U3.GG (m := 3) (R := C)) (g : G)
    (hg : (r g).right = 1) :
    (conjBy h r g).mat = (h : Matrix (Fin 3) (Fin 3) C) * (r g).mat * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  unfold GG.mat
  rw [conjBy_left h r g hg, Units.val_mul, Units.val_mul]

section Conj

variable {C : Type} [CommRing C]

theorem ent_mem_mul {J : Ideal C} {N : Matrix (Fin 3) (Fin 3) C} (hN : ∀ i j, N i j ∈ J)
    (A B : Matrix (Fin 3) (Fin 3) C) (i j : Fin 3) : (A * N * B) i j ∈ J := by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hN m k))

theorem conj_sub_scalar (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) (c : C) :
    (h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (h : Matrix (Fin 3) (Fin 3) C) * (M - Matrix.scalar _ c) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : (h : Matrix (Fin 3) (Fin 3) C) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) (h : Matrix (Fin 3) (Fin 3) C)),
    Matrix.mul_assoc (Matrix.scalar _ c), e, Matrix.mul_one]

theorem conj_mul_three_alt (h : GL (Fin 3) C) (A B E : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * B * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * E * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) =
      (h : Matrix (Fin 3) (Fin 3) C) * (A * B * E) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul,
    ← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul]

theorem unconj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    M = ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) *
      ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) * (h : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]

theorem trace_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem charpoly_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).charpoly = M.charpoly := by
  rw [Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj h M

end Conj

end GlobalTheory.OrdLoc

namespace GlobalTheory.OrdLoc

end GlobalTheory.OrdLoc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementNotMemMinimalPrimesReducedOrdinStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturatingElement_notMem_minimalPrimes_reducedOrdinaryIdeal : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)), ∀ P ∈ (GlobalTheory.OrdLoc.Icr D U).minimalPrimes, GlobalTheory.OrdLoc.del D U.r.hom ∉ P := by
  intro l _ O _ _ _ D U P hP hdel
  have hmem : ∀ a, a ∈ D.IY U ↔ ∃ n, D.del U.r.hom ^ n * a ∈ D.ordIdeal U.r.hom := by
    intro a
    rw [UpperTheory.V.Loc.Dat3.IY.eq_1]
    rfl
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hdel
  apply hy
  rw [UpperTheory.V.Loc.Dat3.Icr.eq_1] at hxy ⊢
  obtain ⟨k, hk⟩ := hxy
  obtain ⟨n, hn⟩ := (hmem _).1 hk
  refine ⟨k, (hmem _).2 ⟨n + k, ?_⟩⟩
  have e : D.del U.r.hom ^ (n + k) * y ^ k = D.del U.r.hom ^ n * (D.del U.r.hom * y) ^ k := by
    ring
  rw [e]
  exact hn
end

