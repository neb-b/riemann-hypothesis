module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]

theorem hl_normal' (D : Dat3 l O) : D.HL.Normal := by
  unfold Dat3.HL; infer_instance

theorem hl_isOpen' (D : Dat3 l O) : IsOpen (D.HL : Set (GQ l)) := by
  have e : (D.η.ker : Set (GQ l)) = (D.Kv.1.fixingSubgroup : Set (GQ l)) := by
    ext g; exact D.η_ker g
  have h1 : IsOpen (D.η.ker : Set (GQ l)) := by
    rw [e]; haveI := D.Kv.2; exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  exact h1.inter D.τ_open

theorem finiteIndex_of_open' (H : OpenSubgroup (GQ l)) : (H : Subgroup (GQ l)).FiniteIndex := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_isFr (D : Dat3 l O) : ∃ σ, IsFr D σ := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  haveI hHn : D.HL.Normal := hl_normal' D
  have hHo : IsOpen (D.HL : Set (GQ l)) := hl_isOpen' D
  obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
  haveI : D.HL.FiniteIndex := finiteIndex_of_open' ⟨D.HL, hHo⟩
  set N : Subgroup (GQ l) := D.HL ⊔ Iq l with hN
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  haveI : N.Normal := Subgroup.sup_normal _ _
  set q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
  set m := orderOf q with hm
  have hm1 : 1 ≤ m := orderOf_pos q
  have hmN : σ₀ ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one q
  obtain ⟨h, hh, i₀, hi₀, hhi⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
  let φ := QuotientGroup.mk' (Iq l)
  have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
  have hφm : φ σ₀ ^ m = φ h := by
    rw [← map_pow, ← hhi, map_mul, hφ.2 hi₀, mul_one]
  refine ⟨h, ⟨hh, ?_⟩, σ₀, m, hσ₀, hm1, ?_⟩
  ·
    rw [eq_top_iff]
    intro g _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    rw [mem_closure_iff]
    intro U hU hgU
    have hdense := frobDense σ₀ hσ₀
    have hV : IsOpen (D.HL.subtype '' U) := (hHo.isOpenEmbedding_subtypeVal).isOpenMap U hU
    have hcl : (D.HL.subtype g) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [← Subgroup.topologicalClosure_coe, hdense]; trivial
    obtain ⟨x, ⟨u, huU, rfl⟩, hxT⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
    obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hxT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    change i * σ₀ ^ k = (u : GQ l) at hiz
    have hkN : σ₀ ^ k ∈ N := by
      have : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
      rw [this]
      exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
    have hdvd : (m : ℤ) ∣ k := by
      rw [hm, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]; exact hkN
    obtain ⟨j, rfl⟩ := hdvd
    have hφu : φ (u : GQ l) = φ h ^ j := by
      rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
    have hy : (u : GQ l) * h ^ (-j) ∈ Iq l := by
      rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
    refine ⟨u, huU, ?_⟩
    have e : u = (⟨(u : GQ l) * h ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hh _)⟩ : ↥D.HL) * (⟨h, hh⟩ : ↥D.HL) ^ j := by
      ext; simp
    rw [SetLike.mem_coe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  · rw [← hhi]; simpa using Subgroup.inv_mem _ hi₀

theorem fr_isFr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O),
    GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  intro l _ O _ _ _ D
  exact Classical.epsilon_spec (exists_isFr D)

end GlobalTheory.OrdLoc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationFibreProductAmalgamation
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.FibreGlue

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C] [IsScalarTower ℚ_[l] E C] (πC : C →ₐ[E] E) (hπC : ∀ a, πC a = 0 → IsNilpotent a) (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T] [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T] [IsScalarTower ℚ_[l] E T] (πT : T →ₐ[E] E) (hπT : ∀ a, πT a = 0 → IsNilpotent a) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C), π.comp p₁ = πT → πC.comp p₂ = πT → (∀ b c, π b = πC c → ∃! t, p₁ t = b ∧ p₂ t = c) → ∀ (r₁ : GQ l →* GG (m := 3) (R := B)) (r₂ : GQ l →* GG (m := 3) (R := C)), D.InDcr (π : B →+* E) r₁ → D.InDcr (πC : C →+* E) r₂ → ∃ r : GQ l →* GG (m := 3) (R := T), D.InDcr (πT : T →+* E) r ∧ (GG.map (p₁ : T →+* B)).comp r = r₁ ∧ (GG.map (p₂ : T →+* C)).comp r = r₂ := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ C _ _ _ _ _ _ _ _ _ _ πC hπC T _ _ _ _ _ _ _ _ _ _ πT hπT p₁ p₂ h1 h2 huniq r₁ r₂ hr₁ hr₂
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

end GlobalTheory.FibreGlue
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsTruncatedPolynomialThickeningFibreSquareStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncated_polynomial_thickening_fibre_square : ∀ {E B : Type} [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ J : ℕ, ∃ (C : Type) (_ : CommRing C) (_ : Algebra E C) (_ : Module.Finite E C) (T : Type) (_ : CommRing T) (_ : Algebra E T) (_ : Module.Finite E T) (πC : C →ₐ[E] E) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C) (t : C), IsNilpotent t ∧ (∀ a, πC a = 0 → IsNilpotent a) ∧ (∀ a, π (p₁ a) = 0 → IsNilpotent a) ∧ π.comp p₁ = πC.comp p₂ ∧ (∀ b c, π b = πC c → ∃ s, p₁ s = b ∧ p₂ s = c) ∧ ∀ (P y : T) (j : ℕ) (v : Cˣ), j ≤ J → p₂ P = t ^ j * v → P * y = 0 → p₁ y = 0 := by
  intro E B _ _ _ _ π hπ J
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite E B
  obtain ⟨e, he⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro c hc
    exact mem_nilradical.mpr (hπ c (by simpa using hc))
  set I := RingHom.ker (π : B →+* E) with hIdef
  set N := J * e + 1 with hN
  have hN0 : N ≠ 0 := by omega
  haveI : Module.Finite E (AdjoinRoot ((X : E[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite B (AdjoinRoot ((X : B[X]) ^ N)) :=
    (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  haveI : Module.Finite E (AdjoinRoot ((X : B[X]) ^ N)) := Module.Finite.trans B _
  have hrootE : (AdjoinRoot.root ((X : E[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have hrootB : (AdjoinRoot.root ((X : B[X]) ^ N)) ^ N = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  let πC : AdjoinRoot ((X : E[X]) ^ N) →ₐ[E] E :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E E) 0 (by simp [hN0])
  let p1 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] B :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id E B) 0 (by simp [hN0])
  let p2 : AdjoinRoot ((X : B[X]) ^ N) →ₐ[E] AdjoinRoot ((X : E[X]) ^ N) :=
    AdjoinRoot.liftAlgHom _ ((Algebra.ofId E _).comp π) (AdjoinRoot.root _)
      (by rw [eval₂_X_pow]; exact hrootE)
  have hp1 : ∀ q : B[X], p1 (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [p1, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp1of : ∀ b : B, p1 (AdjoinRoot.of _ b) = b := fun b =>
    AdjoinRoot.liftAlgHom_of _ _ _ _ _
  have hπC : ∀ q : E[X], πC (AdjoinRoot.mk _ q) = q.coeff 0 := by
    intro q
    simp [πC, AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]
  have hp2 : ∀ q : B[X], p2 (AdjoinRoot.mk _ q) = AdjoinRoot.mk _ (q.map (π : B →+* E)) := by
    intro q
    rw [AdjoinRoot.liftAlgHom_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
    rfl
  have hp2root : p2 (AdjoinRoot.root _) = AdjoinRoot.root _ := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hp2map : ∀ q : E[X], p2 (AdjoinRoot.mk _ (q.map (algebraMap E B))) = AdjoinRoot.mk _ q := by
    intro q
    rw [hp2, Polynomial.map_map]
    congr 1
    conv_rhs => rw [← Polynomial.map_id (p := q)]
    congr 1
    ext r
    simp
  have hnilT : ∀ a, π (p1 a) = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hp1] at ha
    obtain ⟨r, hr⟩ : X ∣ q - C (q.coeff 0) := X_dvd_iff.mpr (by simp)
    have hq : q = C (q.coeff 0) + X * r := by rw [← hr]; ring
    rw [hq, map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact Commute.isNilpotent_add (Commute.all _ _) ((hπ _ ha).map _)
      ⟨N, by rw [mul_pow, hrootB, zero_mul]⟩
  have hnilC : ∀ a, πC a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hπC] at ha
    obtain ⟨r, rfl⟩ := X_dvd_iff.mpr ha
    exact ⟨N, by rw [map_mul, AdjoinRoot.mk_X, mul_pow, hrootE, zero_mul]⟩
  have hcomm : π.comp p1 = πC.comp p2 := by
    refine AlgHom.ext fun a => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    simp only [AlgHom.comp_apply, hp1, hp2, hπC, coeff_map]
    rfl
  have hsurj : ∀ b c, π b = πC c → ∃ s, p1 s = b ∧ p2 s = c := by
    intro b c hbc
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective c
    rw [hπC] at hbc
    refine ⟨AdjoinRoot.of _ b + AdjoinRoot.mk _ (q.map (algebraMap E B)) -
      AdjoinRoot.of _ (algebraMap E B (q.coeff 0)), ?_, ?_⟩
    · rw [map_sub, map_add (f := _), ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp1, hp1, hp1]
      simp
    · rw [map_sub, map_add (f := _), hp2map, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp2, hp2]
      simp [hbc]
  have hker : ∀ Q, p2 Q = 0 → Q ∈ I.map (AdjoinRoot.of ((X : B[X]) ^ N)) := by
    intro Q hQ
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective Q
    rw [hp2, AdjoinRoot.mk_eq_zero] at hQ
    have hmod : (q %ₘ (X ^ N)).map (π : B →+* E) = 0 := by
      rw [map_modByMonic _ (monic_X_pow N), Polynomial.map_pow, map_X]
      exact (modByMonic_eq_zero_iff_dvd (monic_X_pow N)).mpr hQ
    have hmk : AdjoinRoot.mk ((X : B[X]) ^ N) q = AdjoinRoot.mk _ (q %ₘ (X ^ N)) := by
      conv_lhs => rw [← modByMonic_add_div q (X ^ N)]
      rw [map_add (f := _), map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    have hin : q %ₘ (X ^ N) ∈ I.map (C : B →+* B[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [hIdef, RingHom.mem_ker]
      have := congrArg (fun p => p.coeff n) hmod
      simpa using this
    have := Ideal.mem_map_of_mem (AdjoinRoot.mk ((X : B[X]) ^ N)) hin
    rw [Ideal.map_map] at this
    exact this
  refine ⟨AdjoinRoot ((X : E[X]) ^ N), inferInstance, inferInstance, inferInstance,
    AdjoinRoot ((X : B[X]) ^ N), inferInstance, inferInstance, inferInstance, πC, p1, p2,
    AdjoinRoot.root _, ⟨N, hrootE⟩, hnilC, hnilT, hcomm, hsurj, ?_⟩
  intro P y j v hj hP hPy
  obtain ⟨qv, hqv⟩ := AdjoinRoot.mk_surjective (v : AdjoinRoot ((X : E[X]) ^ N))
  set V := AdjoinRoot.mk ((X : B[X]) ^ N) (qv.map (algebraMap E B)) with hVdef
  have hV : p2 V = v := by rw [hVdef, hp2map, hqv]
  have hVu : IsUnit V := by
    have hw : π (p1 V) ≠ 0 := by
      rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply, hV]
      exact (v.isUnit.map πC).ne_zero
    have h1 : IsNilpotent (V - AdjoinRoot.of _ (algebraMap E B (π (p1 V)))) := by
      apply hnilT
      rw [map_sub, map_sub, hp1of, AlgHom.commutes]
      simp
    have h2 : IsUnit (AdjoinRoot.of ((X : B[X]) ^ N) (algebraMap E B (π (p1 V)))) :=
      ((Ne.isUnit hw).map (algebraMap E B)).map _
    have := h1.isUnit_add_left_of_commute h2 (Commute.all _ _)
    simpa using this
  obtain ⟨Vi, hVi⟩ : ∃ Vi, V * Vi = 1 := hVu.exists_right_inv
  set Q := P - AdjoinRoot.root ((X : B[X]) ^ N) ^ j * V with hQdef
  have hQ2 : p2 Q = 0 := by
    rw [hQdef, map_sub, map_mul, map_pow, hV, hP, hp2root, sub_self]
  set K := I.map (AdjoinRoot.of ((X : B[X]) ^ N)) with hK
  have hQK : Q ∈ K := hker Q hQ2
  set R := -(Q * Vi) with hR
  have hRK : R ∈ K := K.neg_mem (K.mul_mem_right _ hQK)
  have hxR : AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y = R * y := by
    rw [hR]
    linear_combination (-(AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y)) * hVi + Vi * hPy +
      (Vi * y) * hQdef
  have hpow : ∀ k : ℕ, AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y = R ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsplit : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) =
          AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * AdjoinRoot.root ((X : B[X]) ^ N) ^ j := by
        rw [← pow_add]
        congr 1
      calc AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * (k + 1)) * y
          = AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) *
              (AdjoinRoot.root ((X : B[X]) ^ N) ^ j * y) := by
            rw [hsplit, mul_assoc]
        _ = R * (AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * k) * y) := by rw [hxR]; ring
        _ = R ^ (k + 1) * y := by rw [ih]; ring
  have hRe : R ^ e = 0 := by
    have h3 : R ^ e ∈ K ^ e := Ideal.pow_mem_pow hRK e
    rw [hK, ← Ideal.map_pow, he, Ideal.zero_eq_bot, Ideal.map_bot] at h3
    exact (Ideal.mem_bot).1 h3
  have hy0 : AdjoinRoot.root ((X : B[X]) ^ N) ^ (j * e) * y = 0 := by
    rw [hpow, hRe, zero_mul]
  have hlt : j * e < N := by
    have := Nat.mul_le_mul_right e hj
    omega
  obtain ⟨qy, rfl⟩ := AdjoinRoot.mk_surjective y
  rw [hp1]
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_zero] at hy0
  obtain ⟨s, hs⟩ := hy0
  have h4 := congrArg (fun p => p.coeff (j * e)) hs
  simp only [coeff_X_pow_mul'] at h4
  simpa [Nat.not_le.mpr hlt] using h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExpEqOneAddAddSq
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.UnrUnipChar

theorem exp_eq_one_add_add_sq {A : Type} [CommRing A] [Algebra ℚ A] {a : A} (ha : IsNilpotent a) :
    ∃ s, IsNilpotent.exp a = 1 + a + a ^ 2 * s := by
  obtain ⟨k, hk⟩ := ha
  have h2 : a ^ (k + 1 + 1) = 0 := pow_eq_zero_of_le (by omega) hk
  refine ⟨∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum h2, Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  have : ∀ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ (i + 1 + 1)
      = a ^ 2 * ((((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i) := fun i _ => by
    rw [mul_smul_comm]; congr 1; ring
  rw [Finset.sum_congr rfl this]
  simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one,
    pow_zero]
  ring

end GlobalTheory.UnrUnipChar


open GlobalTheory.UnrUnipChar in
theorem GlobalTheory.unr_unip_char_frob :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (t : B),
      IsNilpotent t → ∀ σ : GQ l, UpperTheory.V.Loc.IsFrob σ → ∃ u : GQ l →* Bˣ, QCont l (fun g => (u g : B)) ∧
        (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : B) - 1)) ∧
        ∃ v : Bˣ, ∀ m : ℕ, ∃ b : B, (u (σ ^ m) : B) - 1 = t * ((m : B) * v + t * b) := by
  intro l _ B _ _ _ x hx σ hσ
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B
  haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (v := l) (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ l) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1
  have hadd : ∀ g h, c (g * h) = c g + c h := fun g h => hc.2 g h
  have hcc : Continuous c := hc.1
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  have hcpow : ∀ m : ℕ, c (σ ^ m) = m := by
    intro m
    induction m with
    | zero => simp [hc1]
    | succ m ih => rw [pow_succ, hadd, ih, hcσ]; push_cast; ring
  let f : GQ l →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • x)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by
        rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := hx
    have : (f : GQ l → B) = fun g => ∑ i ∈ Finset.range k,
        ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i := by
      funext g
      change IsNilpotent.exp (c g • x) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [_root_.smul_pow, hk, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, Rat.cast_smul_eq_qsmul, _root_.smul_pow]
    rw [this]
    fun_prop
  have hfI : ∀ g ∈ Iq l, f g = 1 := fun g hg => by
    change IsNilpotent.exp (c g • x) = 1
    rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  refine ⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_, 1, fun m => ?_⟩
  · change IsNilpotent (IsNilpotent.exp (c g • x) - 1)
    obtain ⟨s, hs⟩ := exp_eq_one_add_add_sq (hx.smul (c g))
    rw [hs, show 1 + c g • x + (c g • x) ^ 2 * s - 1 = (c g • x) * (1 + (c g • x) * s) by ring]
    first
      | exact (Commute.all _ _).isNilpotent_mul_right (hx.smul (c g))
      | exact (Commute.all _ _).isNilpotent_mul_left (hx.smul (c g))
  · change ∃ b, IsNilpotent.exp (c (σ ^ m) • x) - 1 = x * ((m : B) * ((1 : Bˣ) : B) + x * b)
    rw [hcpow m]
    obtain ⟨s, hs⟩ := exp_eq_one_add_add_sq (hx.smul ((m : ℚ_[l])))
    refine ⟨(m : B) ^ 2 * s, ?_⟩
    have e : ((m : ℚ_[l]) • x) = (m : B) * x := by rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    rw [hs, e, Units.val_one]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem hl_basic : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O), D.HL.Normal ∧ IsOpen (D.HL : Set (GQ l)) ∧ IsOpenEmbedding D.HL.subtype ∧ (∀ s ∈ D.HL, s ∈ Iq l → D.Ψ s = cycA l l O s ^ D.e) ∧ GlobalTheory.OrdLoc.IsInertiaInfiniteCyclotomic D (GlobalTheory.OrdLoc.s0 D) := by
  intro l _ O _ _ _ D
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    rw [this]
    haveI := D.Kv.2
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have ho : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  have hex : ∃ s, IsInertiaInfiniteCyclotomic D s := by
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := ((cycInertia l).2 D.HL ho).2
    exact ⟨s, hs1, hs2, hs⟩
  refine ⟨inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal, ho, ho.isOpenEmbedding_subtypeVal, fun s hs hi => ?_,
    Classical.epsilon_spec hex⟩
  have ht : D.τ s = 1 := hs.2
  rw [D.Ψ_I s hi, ht, mul_one]

end GlobalTheory.OrdLoc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.NilpotentTwistStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem sh_s0_eq_diagonal_psi_sub_psi {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (b : Fin 3) : D.sh r b D.s0 = Matrix.diagonal (fun c => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ c D.s0) - algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
  rw [Dat3.sh, h, Matrix.scalar_apply, Matrix.diagonal_sub]
private theorem tr_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (a : Fin 3) : D.tr r a = algebraMap O C (D.cc a) * (r D.fr).mat a a := by
  rw [Dat3.tr, sh_s0_eq_diagonal_psi_sub_psi D r h, sh_s0_eq_diagonal_psi_sub_psi D r h, Matrix.diagonal_mul_diagonal, Matrix.trace, Fin.sum_univ_three]
  simp only [Matrix.diag, Matrix.diagonal_mul, Dat3.cc, map_mul, map_sub]
  fin_cases a <;> simp <;> ring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_derivative_entry_formula : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)), (r (GlobalTheory.OrdLoc.s0 D)).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D))) → ∀ a : Fin 3, GlobalTheory.OrdLoc.dd D r a = algebraMap O C (GlobalTheory.OrdLoc.cc D a * GlobalTheory.OrdLoc.cc D (a + 1)) * ((r (GlobalTheory.OrdLoc.fr D)).mat a a - algebraMap O C ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) * (r (GlobalTheory.OrdLoc.fr D)).mat (a + 1) (a + 1)) := by
  intro l _ O _ _ _ D C _ _ r h a
  simp only [Dat3.dd, tr_lemma_2 D r h, map_mul]
  ring
end

