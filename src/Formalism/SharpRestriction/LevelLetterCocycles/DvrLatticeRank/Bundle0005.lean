module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.DvdPf

open Formalism.BasicNotions Formalism.BasicNotions.Loc Module

private theorem finrank_cyclotomicExt_dvd_sub_one {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [CharZero Ω] [Algebra.IsIntegral F Ω] (E K : IntermediateField F Ω) (hEK : E ≤ K) (l : ℕ) (hp : l.Prime)
    (hle : K ≤ E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1}) :
    Module.finrank E (IntermediateField.extendScalars hEK) ∣ l - 1 := by
  have hl0 : 0 < l := hp.pos
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  haveI : NeZero (l : E) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : Algebra.IsIntegral E Ω := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := F) x).tower_top⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ l := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l Ω)
      (Polynomial.degree_cyclotomic_pos l Ω hl0).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  set M : IntermediateField E Ω := IntermediateField.adjoin E {ζ} with hM
  haveI hcyc : IsCyclotomicExtension {l} E M := by
    first
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension E
    | exact hζ.intermediateField_adjoin_isCyclotomicExtension
    | exact IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension E hζ
  haveI : FiniteDimensional E M := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hl0).tower_top
    | exact IsCyclotomicExtension.finiteDimensional {l} E M
  haveI : IsGalois E M := IsCyclotomicExtension.isGalois {l} E M

  have hcard : Module.finrank E M ∣ l - 1 := by
    have hμ := IsCyclotomicExtension.zeta_spec l E M
    have hinj := IsPrimitiveRoot.autToPow_injective E hμ
    have h1 : Nat.card (M ≃ₐ[E] M) ∣ Nat.card (ZMod l)ˣ := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (M ≃ₐ[E] M) = Module.finrank E M := by
      first
      | exact IsGalois.card_aut_eq_finrank E M
      | (rw [Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank E M)
    have h3 : Nat.card (ZMod l)ˣ = l - 1 := by
      haveI : Fact l.Prime := ⟨hp⟩
      first
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units])
      | (rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp])
    rw [← h2, ← h3]
    exact h1

  have hsup : E ⊔ IntermediateField.adjoin F {x : Ω | x ^ (l ^ 1) = 1} ≤ M.restrictScalars F := by
    apply sup_le
    · intro y hy
      rw [IntermediateField.mem_restrictScalars]
      exact M.algebraMap_mem ⟨y, hy⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y ^ l = 1 := by simpa using hy
      have hζM : ζ ∈ M := IntermediateField.mem_adjoin_simple_self E ζ
      show y ∈ M.restrictScalars F
      rw [IntermediateField.mem_restrictScalars]
      first
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy'
         exact pow_mem hζM i)
      | (obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy' hl0
         exact pow_mem hζM i)
  have hKM : IntermediateField.extendScalars hEK ≤ M := by
    intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    exact (IntermediateField.mem_restrictScalars F).mp (hsup (hle hx))

  have hdvd : Module.finrank E (IntermediateField.extendScalars hEK) ∣ Module.finrank E M := by
    first
    | (have h := IntermediateField.relfinrank_mul_relfinrank
          (bot_le : (⊥ : IntermediateField E Ω) ≤ IntermediateField.extendScalars hEK) hKM
       rw [IntermediateField.relfinrank_bot_left, IntermediateField.relfinrank_bot_left] at h
       exact Dvd.intro _ h)
    | exact IntermediateField.finrank_dvd_of_le_right hKM
  exact hdvd.trans hcard

theorem dvdCondition : Formalism.MainNotions.N.Ln34.DvdStep := by
  intro l _ hl K LL hG
  have hle : K.1 ≤ Ks K 1 := hG.2.2.1
  have hEK : K0 K ≤ K.1 := inf_le_left
  haveI : CharZero (Om l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Om l)).injective
  have h := finrank_cyclotomicExt_dvd_sub_one (F := ℚ_[l]) (K0 K) K.1 hEK l (Fact.out) hle
  first
  | exact h
  | (show Module.finrank (K0 K) K.1 ∣ l - 1
     convert h using 1
     exact LinearEquiv.finrank_eq
       { toFun := fun y => ⟨y.1, y.2⟩
         invFun := fun y => ⟨y.1, y.2⟩
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl })

end Formalism.MainNotions.N.Ln34.DvdPf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExistsAutPrim
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem exists_aut_prim (K : FinExt l) {z z' : Om l} (hz : IsPrimitiveRoot z l)
    (hz' : IsPrimitiveRoot z' l) : ∃ g : Om l ≃ₐ[↥(K0 K)] Om l, g z = z' := by
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  haveI : IsAlgClosure ↥(K0 K) (Om l) := ⟨inferInstance, inferInstance⟩
  have hint : IsIntegral ↥(K0 K) z := Algebra.IsIntegral.isIntegral z
  have hle : K0 K ≤ Ks K 1 := le_sup_left
  have hdeg := CyclotomicLifting.cyclotomic_degree_max_unramified K
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hdeg
  have hsub : IntermediateField.extendScalars hle ≤ IntermediateField.adjoin ↥(K0 K) {z} := by
    have h : Ks K 1 ≤ (IntermediateField.adjoin ↥(K0 K) {z}).restrictScalars ℚ_[l] := by
      refine sup_le (fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 fun x hx => ?_)
      · exact (IntermediateField.adjoin ↥(K0 K) {z}).algebraMap_mem ⟨x, hx⟩
      · have hx1 : x ^ l = 1 := by simpa using hx
        obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hx1
        exact pow_mem (IntermediateField.mem_adjoin_simple_self ↥(K0 K) z) b
    intro x hx
    exact h hx
  haveI := IntermediateField.adjoin.finiteDimensional hint
  have hd : l - 1 ≤ (minpoly ↥(K0 K) z).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, ← hdeg]
    exact IntermediateField.finrank_le_of_le_right hsub
  have hroot : ∀ {w : Om l}, IsPrimitiveRoot w l →
      Polynomial.aeval w (Polynomial.cyclotomic l ↥(K0 K)) = 0 := fun {w} hw => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hw.isRoot_cyclotomic hl.pos
  have hdvd : minpoly ↥(K0 K) z ∣ Polynomial.cyclotomic l ↥(K0 K) := minpoly.dvd _ _ (hroot hz)
  have heq : Polynomial.cyclotomic l ↥(K0 K) = minpoly ↥(K0 K) z :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic _ _) hdvd
      (by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl]; exact hd)
  have h0 : Polynomial.aeval z' (minpoly ↥(K0 K) z) = 0 := heq ▸ hroot hz'
  exact minpoly.exists_algEquiv_of_root' hint.isAlgebraic h0

theorem exists_pt (D : D7) (HW : HWOf D.loc) {K LL : FinExt l} (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hG).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hG).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := exists_aut_prim K hζ₁ hβ
  let g' : Om l →ₐ[ℚ_[l]] Om l := (g.toAlgHom).restrictScalars ℚ_[l]
  have hmem : ∀ y, ((σ.comp g').comp (Ks K 1).val) y ∈ LL.1 := hG.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp g').comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hG.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    have hgx : g (x : Om l) = x := g.commutes x
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExtPfMultVEqZero
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ExtPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem extPf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    fun x hx => PD.Fil_anti a hx
  unfold FilV
  rintro _ ⟨t, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) t, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

theorem extPf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (extPf_filV_succ_le PD (LL := LL) (V := V) a)

theorem extPf_multV_eq_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  unfold multV
  rw [not_not.1 h, sub_self]

theorem extPf_not_jump (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ)
    (h : multV PD ρ τ a = 0) : ¬ IsJumpV PD ρ τ a := by
  intro hj
  unfold IsJumpV at hj
  apply hj
  haveI : FiniteDimensional LL ↥(DdRE PD ρ τ) := hfin
  have hsub : FildR PD ρ τ a ≤ DdRE PD ρ τ := by
    unfold FildR
    exact inf_le_left
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) := Submodule.finiteDimensional_of_le hsub
  apply Submodule.eq_of_le_of_finrank_eq (extPf_fildR_succ_le PD ρ τ a)
  unfold multV at h
  omega

end Gen

theorem ext_pf : Formalism.MainNotions.N.Ln34.ExtStep := by
  intro D HW F Cm CA CB CK hA l _ _ K LL hG T h' hh' hc hj κ hκ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h8, h11, -⟩ := hA
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨h1, hz⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0 ((HW l).W K 1 LL hG)
  obtain ⟨Tp, ι, π, hcp, hext⟩ := Formalism.MainNotions.LiftingTheory.lext_HExt_D D HW F l K 1 LL hG h1 T κ hc hκ
  refine ⟨Tp, ι, π, hext, hcp, h1, fun τ a ha => ?_⟩
  by_contra hout
  obtain ⟨-, -, hadd⟩ := h11 l K LL T Tp ((HW l).W K 1 LL hG).one ι π hext.1 hcp
  have hfin := ((h8 l K LL Tp).2 τ).1
  have h0 : multV ((D.loc l).PD K) T.ρ τ a = 0 :=
    extPf_multV_eq_zero _ _ τ a fun hT => hout (hj τ a hT)
  have h2 : multV ((D.loc l).PD K) ((HW l).W K 1 LL hG).one.ρ τ a = 0 := by
    refine extPf_multV_eq_zero _ _ τ a fun hO => hout ?_
    rw [hz τ a hO]
    exact Set.mem_Icc.2 ⟨by omega, by omega⟩
  exact extPf_not_jump _ _ τ hfin a (by have := hadd τ a; omega) ha

end Formalism.MainNotions.N.Ln34.ExtPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLoc
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Coeff

variable {R : Type} [CommRing R]

theorem framepf_coeff_pow_lt (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m j : ℕ)
    (hj : j < m) : PowerSeries.coeff j (f ^ m) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem framepf_coeff_pow_self (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m : ℕ) :
    PowerSeries.coeff m (f ^ m) = PowerSeries.coeff 1 f ^ m := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end Coeff

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

theorem framepf_ιV_inj : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem framepf_levB_gam (hc : IsCrys PD T.ρ) (g : W.Gam)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - 1)) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Ct.levB T i 1 ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Ct.levB T i 1 x k :=
  Ct.levB_Γ T hc g i 1 1 0 1 (by simpa using IsPrimitiveRoot.one) (by simpa using hv) (by simp) x hx k

theorem framepf_levB_zero (hc : IsCrys PD T.ρ) (i : ZMod n)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1))
    (hχ : ∀ r : ℤ, 1 ≤ r → (algebraMap O LL (W.χΓ W.gam : O)) ^ r ≠ 1)
    (a : LetA O n) (R : ℕ) (ha : ∀ j < R, PowerSeries.coeff j (W.lev i 1 a) = 0)
    (x w : ↥(W.N T)) (hxw : W.γD T W.gam (x : W.DD T) - x = a • (w : W.DD T))
    (hw : ∀ r : ℤ, r < 0 → W.levN T i 1 w r = 0) (r : ℤ) (h1 : 1 ≤ r) (hR : r < R) :
    Ct.levB T i 1 x r = 0 := by
  have hx : W.γD T W.gam (x : W.DD T) ∈ W.N T := W.N_Γ T W.gam x x.2
  have haw : a • (w : W.DD T) ∈ W.N T := (W.N T).smul_mem a w.2
  have hsub : (⟨_, hx⟩ : ↥(W.N T)) - x = ⟨_, haw⟩ := Subtype.ext (by simp [hxw])
  have hlev := congrArg (fun y => Ct.levB T i 1 y r) hsub
  simp only [map_sub, Pi.sub_apply] at hlev
  rw [framepf_levB_gam Ct T hc W.gam hv i x hx r] at hlev
  have hzero : Ct.levB T i 1 ⟨_, haw⟩ r = 0 := by
    refine framepf_ιV_inj (PD := PD) T ?_
    rw [map_zero, ← Ct.levN_eq]
    have : (⟨_, haw⟩ : ↥(W.N T)) = a • w := rfl
    rw [this, W.levN_smul]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    by_cases hj : j < R
    · rw [ha j hj, zero_smul]
    · simp only [hw (r - (j : ℤ)) (by omega), smul_zero]
  rw [hzero] at hlev
  have h2 : ((algebraMap O LL (W.χΓ W.gam : O)) ^ r - 1) • Ct.levB T i 1 x r = 0 := by
    rw [sub_smul, one_smul]; exact hlev
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hχ r h1))

theorem framepf_levB_phi (hc : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hQ : ∀ j < m, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (i - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (i - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    Ct.levB T i ζ ⟨_, hm⟩ k =
      serC (W.lev i ζ (W.Q ^ m)) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (i - 1) 1 x 0)) k := by
  rw [Ct.levB_φ T hc i ζ hζ x m hm k, hζ1]
  unfold serC
  split_ifs with hk0
  · rw [finsum_eq_single _ k.toNat]
    · have : k - (k.toNat : ℤ) = 0 := by omega
      rw [this, zpow_zero, one_smul]
    · intro j hj
      by_cases hjm : j < m
      · rw [hQ j hjm, zero_smul]
      · by_cases hjk : (j : ℤ) < k
        · rw [hmid (k - (j : ℤ)) (by omega) (by omega), map_zero, smul_zero, smul_zero]
        · have : (j : ℤ) ≠ k := fun h => hj (by omega)
          rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]

theorem framepf_valAt (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hex : ∃ k : ℕ, W.Q ^ k • W.φD T (x : W.DD T) ∈ W.N T) :
    valAt W T c ζ (x : W.DD T) = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0)) := by
  classical
  unfold valAt
  rw [dite_eq_left hex]
  have hm := Nat.find_spec hex
  have hC := framepf_levB_phi Ct T hc c ζ hζ hζ1 x (Nat.find hex) 1 hm
    (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg
    (fun r h1 h2 => by omega) (Nat.find hex : ℤ) (by omega)
  rw [Ct.levN_eq, hC]
  unfold serC
  rw [if_pos (by omega), map_smul, map_pow, Int.toNat_natCast, framepf_coeff_pow_self _ hQ0, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hQ1), one_smul]

theorem framepf_levN_phi (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (c - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    W.levN T c ζ ⟨_, hm⟩ k = serC (W.lev c ζ (W.Q ^ m)) (valAt W T c ζ (x : W.DD T)) k := by
  rw [framepf_valAt Ct T hc c ζ hζ hζ1 hQ0 hQ1 x hneg ⟨m, hm⟩, Ct.levN_eq,
    framepf_levB_phi Ct T hc c ζ hζ hζ1 x m R hm
      (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg hmid k hk]
  unfold serC
  split_ifs
  · rw [map_smul]
  · rw [map_zero]

end Local

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OneGenPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.OneGenPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem onegen_pf : Formalism.MainNotions.N.Ln34.OneGenStep := by
  intro D HW F Cm CA CB CK _ l _ _ K LL hG
  obtain ⟨-, -, e, -, hspan, hφ, hγ⟩ := Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hG
  exact ⟨e, hspan, hφ, hγ⟩

end Formalism.MainNotions.N.Ln34.OneGenPf
end
end

