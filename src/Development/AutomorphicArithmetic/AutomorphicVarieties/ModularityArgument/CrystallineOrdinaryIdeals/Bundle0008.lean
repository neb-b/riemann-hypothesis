module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdIdealEqBotOfCrystallineDeformation

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationAmalgamateOverFibreProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.OrdLoc.dcr_amalgamate : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (πC : C →ₐ[E] E) (hπC : ∀ a, πC a = 0 → IsNilpotent a) (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T] [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T] [IsScalarTower ℚ_[l] E T] (πT : T →ₐ[E] E) (hπT : ∀ a, πT a = 0 → IsNilpotent a) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C), π.comp p₁ = πT → πC.comp p₂ = πT → (∀ b c, π b = πC c → ∃ t, p₁ t = b ∧ p₂ t = c) → ∀ (r₁ : GQ l →* GG (m := 3) (R := B)) (r₂ : GQ l →* GG (m := 3) (R := C)), D.InDcr (π : B →+* E) r₁ → D.InDcr (πC : C →+* E) r₂ → ∃ r : GQ l →* GG (m := 3) (R := T), D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ C _ _ _ _ _ _ _ _ _ _ πC hπC
    T _ _ _ _ _ _ _ _ _ _ πT hπT p₁ p₂ h₁ h₂ hs r₁ r₂ hr₁ hr₂
  let I : Ideal T := RingHom.ker p₁ ⊓ RingHom.ker p₂
  let q : T →ₐ[E] (T ⧸ I) := Ideal.Quotient.mkₐ E I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective E I
  let q₁ : (T ⧸ I) →ₐ[E] B := Ideal.Quotient.liftₐ I p₁ fun a ha => ha.1
  let q₂ : (T ⧸ I) →ₐ[E] C := Ideal.Quotient.liftₐ I p₂ fun a ha => ha.2
  have e₁ : ∀ t, q₁ (q t) = p₁ t := fun t => rfl
  have e₂ : ∀ t, q₂ (q t) = p₂ t := fun t => rfl
  have f₁ : ∀ t, π (p₁ t) = πT t := fun t => DFunLike.congr_fun h₁ t
  have f₂ : ∀ t, πC (p₂ t) = πT t := fun t => DFunLike.congr_fun h₂ t
  have hn : ∀ a, (π.comp q₁) a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨t, rfl⟩ := hq a
    exact (hπT t ((f₁ t).symm.trans ha)).map q
  have hc₂ : πC.comp q₂ = π.comp q₁ := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨t, rfl⟩ := hq a
    exact (f₂ t).trans (f₁ t).symm
  have hu : ∀ b c, π b = πC c → ∃! t, q₁ t = b ∧ q₂ t = c := by
    intro b c h
    obtain ⟨t, ht₁, ht₂⟩ := hs b c h
    refine ⟨q t, ⟨ht₁, ht₂⟩, ?_⟩
    rintro s ⟨hs₁, hs₂⟩
    obtain ⟨s, rfl⟩ := hq s
    refine Ideal.Quotient.eq.2 ⟨?_, ?_⟩
    · change p₁ (s - t) = 0
      rw [map_sub, ← e₁ s, hs₁, ht₁, sub_self]
    · change p₂ (s - t) = 0
      rw [map_sub, ← e₂ s, hs₂, ht₂, sub_self]
  have hglued : ∃ r : GQ l →* GG (m := 3) (R := T ⧸ I),
      D.InDcr (π.comp q₁ : (T ⧸ I) →+* E) r ∧
      (GG.map (q₁ : (T ⧸ I) →+* B)).comp r = r₁ ∧
      (GG.map (q₂ : (T ⧸ I) →+* C)).comp r = r₂ := by
    have hpt : ∀ x, π (q₁ x) = πC (q₂ x) :=
      fun x => (DFunLike.congr_fun hc₂ x).symm
    have hf : ∀ x y, q₁ x = q₁ y → q₂ x = q₂ y → x = y := by
      intro x y e1 e2
      obtain ⟨t, -, ht⟩ := hu (q₁ x) (q₂ x) (hpt x)
      exact (ht x ⟨rfl, rfl⟩).trans (ht y ⟨e1.symm, e2.symm⟩).symm
    have hpair : ∀ b c, π b = πC c → ∃ x, q₁ x = b ∧ q₂ x = c :=
      fun b c e => (hu b c e).exists
    have hred : (GG.map (π : B →+* E)).comp r₁ = (GG.map (πC : C →+* E)).comp r₂ :=
      hr₁.red.trans hr₂.red.symm
    have hglue : ∃ r : GQ l →* GG (m := 3) (R := T ⧸ I),
        (GG.map (q₁ : (T ⧸ I) →+* B)).comp r = r₁ ∧ (GG.map (q₂ : (T ⧸ I) →+* C)).comp r = r₂ := by
      have hg : ∀ g, GG.map (π : B →+* E) (r₁ g) = GG.map (πC : C →+* E) (r₂ g) :=
        fun g => DFunLike.congr_fun hred g
      choose n hn₁ hn₂ using fun g =>
        OrdinaryDeformation.glue_GL (q₁ : (T ⧸ I) →+* B) (q₂ : (T ⧸ I) →+* C) (π : B →+* E)
          (πC : C →+* E) hf hpair (r₁ g).left (r₂ g).left (congrArg SemidirectProduct.left (hg g))
      let x : GQ l → GG (m := 3) (R := T ⧸ I) := fun g => ⟨n g, (r₁ g).right⟩
      have hx₁ (g : GQ l) : GG.map (q₁ : (T ⧸ I) →+* B) (x g) = r₁ g :=
        SemidirectProduct.ext (hn₁ g) rfl
      have hx₂ (g : GQ l) : GG.map (q₂ : (T ⧸ I) →+* C) (x g) = r₂ g := by
        refine SemidirectProduct.ext (hn₂ g) ?_
        simpa only [GG.map_right] using congrArg SemidirectProduct.right (hg g)
      have hsep {a b : GG (m := 3) (R := T ⧸ I)}
          (ha : GG.map (q₁ : (T ⧸ I) →+* B) a = GG.map (q₁ : (T ⧸ I) →+* B) b)
          (hb : GG.map (q₂ : (T ⧸ I) →+* C) a = GG.map (q₂ : (T ⧸ I) →+* C) b) : a = b := by
        refine SemidirectProduct.ext (Units.ext (Matrix.ext fun i j => hf _ _ ?_ ?_)) ?_
        · exact congrArg (fun u => u.mat i j) ha
        · exact congrArg (fun u => u.mat i j) hb
        · simpa only [GG.map_right] using congrArg SemidirectProduct.right ha
      refine ⟨MonoidHom.mk' x (fun g g' => hsep ?_ ?_), MonoidHom.ext hx₁, MonoidHom.ext hx₂⟩
      · rw [map_mul, hx₁, hx₁, hx₁, map_mul]
      · rw [map_mul, hx₂, hx₂, hx₂, map_mul]
    obtain ⟨r, e1, e2⟩ := hglue
    refine ⟨r, ?_, e1, e2⟩
    let f₁ := (q₁.restrictScalars ℚ_[l]).toLinearMap
    let f₂ := (q₂.restrictScalars ℚ_[l]).toLinearMap
    rw [← e1] at hr₁
    rw [← e2] at hr₂
    have hc : ∀ a b, QCont l fun g => (r g).mat a b := fun a b =>
      OrdinaryDeformation.qcont_pair f₁ f₂ hf (hr₁.cont a b) (hr₂.cont a b)
    have hm : HasMult D.η r := hr₁.mult
    refine ⟨hm, hr₁.red, hc, ?_⟩
    obtain ⟨ρ₁, hρ₁, hcr₁⟩ := hr₁.cr
    obtain ⟨ρ₂, hρ₂, hcr₂⟩ := hr₂.cr
    let _ : TopologicalSpace B := moduleTopology ℚ_[l] B
    have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
    have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
    let _ : TopologicalSpace C := moduleTopology ℚ_[l] C
    have : IsModuleTopology ℚ_[l] C := ⟨rfl⟩
    have : IsTopologicalRing C := IsModuleTopology.isTopologicalRing ℚ_[l] C
    let _ : TopologicalSpace (T ⧸ I) := moduleTopology ℚ_[l] (T ⧸ I)
    have : IsModuleTopology ℚ_[l] (T ⧸ I) := ⟨rfl⟩
    have : IsTopologicalRing (T ⧸ I) := IsModuleTopology.isTopologicalRing ℚ_[l] (T ⧸ I)
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
        exact RingHom.map_mulVec (q₁ : (T ⧸ I) →+* B) _ x a
      · change _ = Matrix.mulVec (ρ₂ g : Matrix (Fin 3) (Fin 3) C) _ a
        rw [hρ₂]
        exact RingHom.map_mulVec (q₂ : (T ⧸ I) →+* C) _ x a
    · exact funext fun a => hf _ _ (congrFun (congrArg Prod.fst h) a) (congrFun (congrArg Prod.snd h) a)
  obtain ⟨r', hr', g₁, g₂⟩ := hglued
  obtain ⟨r, hr, rfl⟩ := crLift hP D E T πT hπT (T ⧸ I) (π.comp q₁) hn q hq (AlgHom.ext f₁) r' hr'
  exact ⟨r, hr, by rw [← g₁]; rfl, by rw [← g₂]; rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdIdealEqBotOfCrystallineDeformationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordIdeal_eq_bot_of_crystalline_deformation : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG (m := 3) (R := B)), D.InDcr (π : B →+* E) r → D.ordIdeal r = ⊥ := by
  first | exact @GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr | exact GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr | (intros; apply GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr <;> assumption)
end

