module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0062

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TwoApply
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Topology UpperTheory.V UpperTheory.V.Loc

namespace UpperTheory.V.Z.J.StepF

section Alg

variable {G E : Type} [Group G] [Field E]

private theorem mul_entry (t : G →* GL (Fin 3) E) (g h : G) (i j : Fin 3) :
    (t (g * h) : Matrix (Fin 3) (Fin 3) E) i j =
      (t g : Matrix (Fin 3) (Fin 3) E) i 0 * (t h : Matrix (Fin 3) (Fin 3) E) 0 j +
      (t g : Matrix (Fin 3) (Fin 3) E) i 1 * (t h : Matrix (Fin 3) (Fin 3) E) 1 j +
      (t g : Matrix (Fin 3) (Fin 3) E) i 2 * (t h : Matrix (Fin 3) (Fin 3) E) 2 j := by
  rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def diag (t : G →* GL (Fin 3) E)
    (ht : ∀ g i j, j < i → (t g : Matrix (Fin 3) (Fin 3) E) i j = 0) (j : Fin 3) : G →* Eˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => (t g : Matrix (Fin 3) (Fin 3) E) j j
      map_one' := by simp
      map_mul' := fun g h => by
        have h10 := fun g => ht g 1 0 (by decide)
        have h20 := fun g => ht g 2 0 (by decide)
        have h21 := fun g => ht g 2 1 (by decide)
        rw [mul_entry]
        fin_cases j <;> simp [h10, h20, h21] }

private def two (α κ : G →* Eˣ) (b : G → E) (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h) :
    Representation E G (E × E) where
  toFun g :=
    { toFun := fun x => (α g * x.1 + b g * x.2, κ g * x.2)
      map_add' := fun x y => by ext <;> simp <;> ring
      map_smul' := fun a x => by ext <;> simp <;> ring }
  map_one' := by
    have h1 : b 1 = 0 := by
      have := hb 1 1
      simpa using this
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    ext <;> simp [hb] <;> ring

private theorem two_apply (α κ : G →* Eˣ) (b : G → E) (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h)
    (g : G) (x : E × E) : two α κ b hb g x = (α g * x.1 + b g * x.2, κ g * x.2) := rfl

end Alg

section Cr

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E]
  [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]

private theorem crOn_map (φ : G →* GQ l) (hφ : IsOpenEmbedding φ)
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul E V]
    {V' : Type} [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] E V']
    [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V']
    [ContinuousConstSMul E V'] (ρ : Representation E G V) (ρ' : Representation E G V')
    (hρ : ReciprocityTheory.Gal.ContAction ρ) (hρ' : ReciprocityTheory.Gal.ContAction ρ') (f : V →ₗ[E] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    (Function.Injective f → CrOn φ ρ' H → CrOn φ ρ H) ∧ (Function.Surjective f → CrOn φ ρ H → CrOn φ ρ' H) := by
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have hc : Continuous fun p : H × V => ((p.1 : G), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hc' : Continuous fun p : H × V' => ((p.1 : G), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have key := isCrys_isDR_sub_quot (φ.comp H.subtype) hφH (ρ.comp H.subtype : Representation E H V)
    (ρ'.comp H.subtype : Representation E H V') (hρ.comp hc) (hρ'.comp hc') (f.restrictScalars ℚ_[l])
    (fun g x => hf g x)
  exact ⟨fun h => (key.1 h).1, fun h => (key.2 h).1⟩

omit [IsTopologicalGroup G] in
private theorem cont_two (α κ : G →* Eˣ) (b : G → E) (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h)
    (hα : Continuous fun g => (α g : E)) (hκ : Continuous fun g => (κ g : E)) (hbc : Continuous b) :
    ReciprocityTheory.Gal.ContAction (two α κ b hb) :=
  (((hα.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).add
    ((hbc.comp continuous_fst).mul (continuous_snd.comp continuous_snd))).prodMk
    ((hκ.comp continuous_fst).mul (continuous_snd.comp continuous_snd))

private theorem core (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (α κ ε : G →* Eˣ) (b : G → E)
    (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h)
    (hα : Continuous fun g => (α g : E)) (hκ : Continuous fun g => (κ g : E)) (hbc : Continuous b)
    (H : Subgroup G) [H.Normal] (hH : IsOpen (H : Set G)) (hcr : CrOn φ (two α κ b hb) H)
    (hε : ∀ g, (α g : E) = ε g * κ g) :
    (fun g => b g * (((κ g)⁻¹ : Eˣ) : E)) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep ε) := by
  have c2 := cont_two α κ b hb hα hκ hbc
  have cα : ReciprocityTheory.Gal.ContAction (chRep α) := (hα.comp continuous_fst).mul continuous_snd
  have cκ : ReciprocityTheory.Gal.ContAction (chRep κ) := (hκ.comp continuous_fst).mul continuous_snd
  have e1 : ∀ g x, LinearMap.inl E E E (chRep α g x) = two α κ b hb g (LinearMap.inl E E E x) := by
    intro g x
    simp [two_apply, chRep]
  have e2 : ∀ g x, LinearMap.snd E E E (two α κ b hb g x) = chRep κ g (LinearMap.snd E E E x) := by
    intro g x
    simp [two_apply, chRep]
  have h1 := (crOn_map φ hφ _ _ cα c2 _ e1 H hH).1 LinearMap.inl_injective hcr
  have h2 := (crOn_map φ hφ _ _ c2 cκ _ e2 H hH).2 LinearMap.snd_surjective hcr
  have key := (crExt φ hφ (chRep α) (two α κ b hb) cα c2 κ (LinearMap.inl E E E) (LinearMap.snd E E E) (0, 1)
    (fun g => b g * (((κ g)⁻¹ : Eˣ) : E)) LinearMap.inl_injective Function.Exact.inl_snd rfl e1
    (fun g => by
      ext <;> simp [two_apply]
      field_simp) H hH h1 h2).1 hcr
  have e3 : twist κ⁻¹ (chRep α) = chRep ε := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    change (((κ g)⁻¹ : Eˣ) : E) * ((α g : E) * x) = (ε g : E) * x
    rw [hε, mul_comm (ε g : E), mul_assoc, Units.inv_mul_cancel_left]
  rwa [e3] at key

end Cr

end UpperTheory.V.Z.J.StepF

open UpperTheory.V.Z.J.StepF in
theorem UpperTheory.V.Z.J.stepF :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l), IsOpenEmbedding φ → ∀ {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (t : G →* GL (Fin 3) E), Continuous (fun g => (t g : Matrix (Fin 3) (Fin 3) E)) → (∀ g i j, j < i → (t g : Matrix (Fin 3) (Fin 3) E) i j = 0) → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → CrOn φ (colRep t) H → ∀ i : Fin 2, (∀ g, (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.castSucc = (cycA l l E (φ g) : E) * (t g : Matrix (Fin 3) (Fin 3) E) i.succ i.succ) → (fun g => (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ * ((t g)⁻¹ : GL (Fin 3) E) i.succ i.succ) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep ((cycA l l E).comp φ)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ t htc ht H _ hH hcr i hi
  have h10 := fun g => ht g 1 0 (by decide)
  have h20 := fun g => ht g 2 0 (by decide)
  have h21 := fun g => ht g 2 1 (by decide)
  have ce : ∀ a b, Continuous fun g => (t g : Matrix (Fin 3) (Fin 3) E) a b :=
    fun a b => htc.matrix_elem a b
  have cc : ReciprocityTheory.Gal.ContAction (colRep t) :=
    (htc.comp continuous_fst).matrix_mulVec continuous_snd
  have hd : ∀ j g, ((diag t ht j g : Eˣ) : E) = (t g : Matrix (Fin 3) (Fin 3) E) j j := fun j g => rfl
  have hb : ∀ g h, (t (g * h) : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ =
      (diag t ht i.castSucc g : E) * (t h : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ +
      (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ * (diag t ht i.succ h : E) := by
    intro g h
    rw [mul_entry, hd, hd]
    fin_cases i <;> simp [h10, h20, h21]
  have c2 := cont_two _ _ _ hb (ce _ _) (ce _ _) (ce _ _)
  have h2 : CrOn φ (two (diag t ht i.castSucc) (diag t ht i.succ)
      (fun g => (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ) hb) H := by
    fin_cases i
    · refine (crOn_map φ hφ _ _ c2 cc
        (LinearMap.coprod (LinearMap.single E (fun _ : Fin 3 => E) 0) (LinearMap.single E (fun _ : Fin 3 => E) 1))
        (fun g x => ?_) H hH).1 (fun x y h => ?_) hcr
      · funext k
        fin_cases k <;> simp [two_apply, hd, colRep, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21]
      · exact Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1)
    · refine (crOn_map φ hφ _ _ cc c2
        (LinearMap.prod (LinearMap.proj (R := E) (φ := fun _ : Fin 3 => E) 1) (LinearMap.proj 2))
        (fun g x => ?_) H hH).2 (fun y => ⟨![0, y.1, y.2], rfl⟩) hcr
      ext <;> simp [two_apply, hd, colRep, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21]
  have key := core φ hφ _ _ ((cycA l l E).comp φ) _ hb (ce _ _) (ce _ _) (ce _ _) H hH h2 hi
  convert key using 3 with g
  rw [← map_inv, ← map_inv, hd]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnrLow
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V

section SlopeTestRemainingChoices

variable {D N : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup N]

private theorem ul_top (I : Subgroup D) (φ : D) (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (S : Subgroup D) (hS : IsClosed (S : Set D)) (hI : I ≤ S) (hφ : φ ∈ S) (s : D) : s ∈ S := by
  have := Subgroup.topologicalClosure_minimal _ (sup_le hI ((Subgroup.zpowers_le).2 hφ)) hS
  rw [h] at this
  exact this (Subgroup.mem_top s)

private theorem ul_lc (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) : IsLocallyConstant ρ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' ρ.ker, ho.preimage (by fun_prop), by simp, fun x hx => ?_⟩
  have h : ρ (g⁻¹ * x) = 1 := hx
  calc ρ x = ρ (g * (g⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = ρ g := by rw [map_mul, h, mul_one]

omit [TopologicalSpace D] [IsTopologicalGroup D] in
private theorem ul_mul (ρ : Representation ℤ D N) (s t : D) (y : N) : ρ (s * t) y = ρ s (ρ t y) := by
  rw [map_mul]; rfl

private theorem ul_zero (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) (z : D → N) (hz : z ∈ Zc ρ) (hI : ∀ s ∈ I, z s = 0)
    (hφ : z φ = 0) (s : D) : z s = 0 :=
  _root_.UpperTheory.Reformulated.B.Rb1.ul_zero ρ I φ h z hz hI hφ s

private theorem ul_ex [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [hn : I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (x : N) (hx : ∀ s ∈ I, ρ s x = x) : ∃ z ∈ Zc ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  have inv1 : ∀ s y, ρ s (ρ s⁻¹ y) = y := fun s y => by rw [← ul_mul, mul_inv_cancel, map_one]; rfl
  have inv2 : ∀ s y, ρ s⁻¹ (ρ s y) = y := fun s y => by rw [← ul_mul, inv_mul_cancel, map_one]; rfl
  have stab : ∀ s y, (∀ j ∈ I, ρ j y = y) → ∀ j ∈ I, ρ j (ρ s y) = ρ s y := fun s y hy j hj => by
    have h1 := hy _ (hn.conj_mem j hj s⁻¹)
    rw [inv_inv, ul_mul, ul_mul] at h1
    have h2 := congrArg (ρ s) h1
    rwa [inv1] at h2
  let T : Equiv.Perm N :=
    { toFun := fun y => x + ρ φ y
      invFun := fun y => ρ φ⁻¹ (y - x)
      left_inv := fun y => by simp only [add_sub_cancel_left, inv2]
      right_inv := fun y => by simp only [inv1, add_sub_cancel] }
  have hg : ∀ u : Subgroup.zpowers T, u ∈ Subgroup.zpowers (⟨T, Subgroup.mem_zpowers T⟩ : Subgroup.zpowers T) := by
    rintro ⟨_, k, rfl⟩
    exact ⟨k, rfl⟩
  obtain ⟨d, hd1, hd2, hd3⟩ := hd (Nat.card (Subgroup.zpowers T)) Nat.card_pos
  obtain ⟨τ, t1, t2, t3⟩ : ∃ τ : D →* Equiv.Perm N, IsLocallyConstant τ ∧ (∀ s ∈ I, τ s = 1) ∧ τ φ = T := by
    let e := (Subgroup.zpowers T).subtype.comp (zmodMulEquivOfGenerator hg rfl).toMonoidHom
    refine ⟨e.comp d, hd1.comp e, fun s hs => ?_, ?_⟩
    · rw [MonoidHom.comp_apply, hd2 s hs, map_one]
    · rw [MonoidHom.comp_apply, hd3]
      exact congrArg Subtype.val (zmodMulEquivOfGenerator_apply_ofAdd_one hg rfl)
  let S : Subgroup D :=
    { carrier := {s | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → τ s y = a + ρ s y}
      one_mem' := ⟨0, fun j _ => map_zero _, fun y _ => by simp⟩
      mul_mem' := fun {s t} ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩ =>
        ⟨a + ρ s b, fun j hj => by rw [map_add (f := _), ha j hj, stab s b hb j hj], fun y hy => by
          rw [map_mul, Equiv.Perm.mul_apply, hb' y hy,
            ha' _ (fun j hj => by rw [map_add (f := _), hb j hj, stab t y hy j hj]), map_add (f := _), ul_mul, add_assoc]⟩
      inv_mem' := fun {s} ⟨a, ha, ha'⟩ =>
        ⟨-ρ s⁻¹ a, fun j hj => by rw [map_neg, stab _ a ha j hj], fun y hy => by
          rw [map_inv, Equiv.Perm.inv_eq_iff_eq,
            ha' _ (fun j hj => by rw [map_add (f := _), map_neg, stab _ a ha j hj, stab _ y hy j hj]),
            map_add, map_neg, inv1, inv1, add_neg_cancel_left]⟩ }
  have hS : ∀ s, s ∈ S := by
    refine ul_top I φ h S ?_ (fun s hs => ⟨0, fun j _ => map_zero _, fun y hy => ?_⟩) ⟨x, hx, fun y _ => ?_⟩
    · exact isOpen_compl_iff.1 (t1.prodMk (ul_lc ρ ho)
        {p | ∃ a, (∀ j ∈ I, ρ j a = a) ∧ ∀ y, (∀ j ∈ I, ρ j y = y) → p.1 y = a + p.2 y}ᶜ)
    · rw [t2 s hs, hy s hs, zero_add]; rfl
    · rw [t3]; rfl
  refine ⟨fun s => τ s 0, ⟨t1.comp fun p => p 0, fun s t => ?_⟩, fun s hs => ?_, ?_⟩
  · obtain ⟨a, -, ha'⟩ := hS s
    obtain ⟨b, hb, hb'⟩ := hS t
    have h0 : ∀ j ∈ I, ρ j 0 = 0 := fun j _ => map_zero _
    show τ (s * t) 0 = τ s 0 + ρ s (τ t 0)
    rw [map_mul, Equiv.Perm.mul_apply, hb' 0 h0, map_zero, add_zero, ha' b hb, ha' 0 h0, map_zero, add_zero]
  · show τ s 0 = 0
    rw [t2 s hs]; rfl
  · show τ φ 0 = x
    rw [t3]
    show x + ρ φ 0 = x
    rw [map_zero, add_zero]

private theorem ul_abs [Finite N] (ρ : Representation ℤ D N) (ho : IsOpen (ρ.ker : Set D)) (I : Subgroup D) [I.Normal] (φ : D)
    (h : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) :
    ∃ Z : AddSubgroup (D → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧
      (∀ z ∈ Z, ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  have hsub : ∀ {a b : D → N}, a ∈ Zc ρ → b ∈ Zc ρ → a - b ∈ Zc ρ := fun {a b} ha hb =>
    ⟨ha.1.sub hb.1, fun s t => by
      simp only [Pi.sub_apply, ha.2 s t, hb.2 s t, map_sub]; abel⟩
  have h0 : (0 : D → N) ∈ Zc ρ := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  let Z : AddSubgroup (D → N) := AddSubgroup.ofSub {z | z ∈ Zc ρ ∧ ∃ Y : N, ∀ s ∈ I, z s = ρ s Y - Y}
    ⟨0, h0, 0, fun s _ => by simp⟩
    (fun a ⟨ha, Y, hY⟩ b ⟨hb, Y', hY'⟩ => by
      rw [← sub_eq_add_neg]
      refine ⟨hsub ha hb, Y - Y', fun s hs => ?_⟩
      rw [Pi.sub_apply, hY s hs, hY' s hs, map_sub]; abel)
  have hcob : ∀ Y : N, (fun s => ρ s Y - Y) ∈ Z := fun Y =>
    ⟨⟨(ul_lc ρ ho).comp fun p => p Y - Y, fun s t => by
      simp only [ul_mul, map_sub]; abel⟩, Y, fun _ _ => rfl⟩
  have hfin : Finite Z := by
    refine Finite.of_injective (fun z : Z => (z.2.2.choose, z.1 φ)) fun a b hab => Subtype.ext ?_
    obtain ⟨e1, e2⟩ := Prod.ext_iff.1 hab
    refine sub_eq_zero.1 (funext (ul_zero ρ I φ h _ (hsub a.2.1 b.2.1) (fun s hs => ?_) (sub_eq_zero.2 e2)))
    have e1' : a.2.2.choose = b.2.2.choose := e1
    rw [Pi.sub_apply, a.2.2.choose_spec s hs, b.2.2.choose_spec s hs, e1', sub_self]
  refine ⟨Z, hfin, fun z hz => hz.1, hcob, fun z hz => hz.2, ?_⟩
  let r : Z →+ (I → N) := AddMonoidHom.mk' (fun z s => z.1 s.1) fun _ _ => rfl
  let π : N →+ (I → N) := AddMonoidHom.mk' (fun Y s => ρ s.1 Y - Y) fun a b => funext fun s => by
    simp only [map_add (f := _), Pi.add_apply]; abel
  have hr : r.range = π.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨Y, hY⟩ := z.2.2
      exact ⟨Y, funext fun s => (hY s.1 s.2).symm⟩
    · rintro _ ⟨Y, rfl⟩
      exact ⟨⟨_, hcob Y⟩, rfl⟩
  have hk : Nat.card π.ker ≤ Nat.card r.ker := by
    have hex : ∀ x : π.ker, ∃ z : r.ker, z.1.1 φ = x.1 := fun x => by
      obtain ⟨z, z1, z2, z3⟩ := ul_ex ρ ho I φ h hd x.1 fun s hs => sub_eq_zero.1 (congrFun x.2 ⟨s, hs⟩)
      exact ⟨⟨⟨z, z1, 0, fun s hs => by rw [z2 s hs]; simp⟩, funext fun s => z2 s.1 s.2⟩, z3⟩
    choose f hf using hex
    exact Nat.card_le_card_of_injective f fun a b hab => Subtype.ext (by rw [← hf a, ← hf b, hab])
  rw [← π.ker.card_mul_index, ← r.ker.card_mul_index, AddSubgroup.index_ker, AddSubgroup.index_ker, hr]
  exact Nat.mul_le_mul_right _ hk

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.J.unrLow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), IsPlaceOver A v → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ (Dec (F := F) A) N), IsOpen (ρ.ker : Set (Dec (F := F) A)) → ∃ Z : AddSubgroup (Dec (F := F) A → N), Finite Z ∧ (Z : Set _) ⊆ Zc ρ ∧ (∀ Y : N, (fun s => ρ s Y - Y) ∈ Z) ∧ (∀ z ∈ Z, ∃ Y : N, ∀ s : Dec (F := F) A, s.1 ∈ Ine (F := F) A → z s = ρ s Y - Y) ∧ Nat.card N ≤ Nat.card Z := by
  intro F Ω _ _ _ _ _ A v hA N _ _ ρ ho
  obtain ⟨φ, -, h1, h2⟩ := GC.decZhat F Ω v A hA
  haveI : ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal := ⟨fun n hn g => conj_mem_Ine g.2 hn⟩
  exact ul_abs ρ ho _ φ h1 h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.WtCut
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.wtCut :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (I : Subgroup D) (d k m : ℕ) (A N : Type) [AddCommGroup A] [Finite A] [AddCommGroup N], GenI l I d → (∀ x : A, l ^ k • x = 0) → ∀ (Z : AddSubgroup (D → N)), Finite Z → ∀ p : Fin m → N →+ A, (∀ z ∈ Z, IsLocallyConstant z ∧ ∀ j s s', p j (z (s * s')) = p j (z s) + p j (z s')) → Nat.card Z ≤ {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}.ncard * Nat.card A ^ (m * d) := by
  intro l _ D _ _ I d k m A N _ _ _ hG hA Z _ p hZ
  obtain ⟨u, -, hu⟩ := hG
  let Φ : Z →+ (Fin m → Fin d → A) :=
    { toFun := fun z j a => p j (z.1 (u a))
      map_zero' := by
        funext j a
        simp
      map_add' := by
        intro x y
        funext j a
        simp }
  let S : Set (D → N) := {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}
  have hSfin : S.Finite := Set.Finite.subset (Set.toFinite (Z : Set (D → N))) (fun z hz => hz.1)
  have hker : ∀ z ∈ Φ.ker, (z : D → N) ∈ S := by
    intro z hz
    refine ⟨z.2, fun j s hs => ?_⟩
    have hz0 : ∀ a, p j (z.1 (u a)) = 0 := fun a => congrFun (congrFun hz j) a
    exact hu k A hA (fun s => p j (z.1 s)) ((hZ _ z.2).1.comp (p j))
      (fun s t => (hZ _ z.2).2 j s t) hz0 s hs
  have h1 : Nat.card Φ.ker ≤ S.ncard := by
    rw [← Nat.card_coe_set_eq]
    haveI := hSfin.to_subtype
    refine Nat.card_le_card_of_injective (fun z : Φ.ker => (⟨z.1.1, hker z.1 z.2⟩ : S)) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  have h2 : Nat.card Φ.range ≤ Nat.card A ^ (m * d) := by
    calc Nat.card Φ.range ≤ Nat.card (Fin m → Fin d → A) :=
          Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
      _ = Nat.card A ^ (m * d) := by
          simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
          rw [← pow_mul, mul_comm]
  calc Nat.card Z = Nat.card Φ.ker * Φ.ker.index := (AddSubgroup.card_mul_index _).symm
    _ = Nat.card Φ.ker * Nat.card Φ.range := by rw [AddSubgroup.index_ker]
    _ ≤ S.ncard * Nat.card A ^ (m * d) := Nat.mul_le_mul h1 h2
end

