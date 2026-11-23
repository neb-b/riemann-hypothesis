module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.CongLev
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_J_of_cong (V : Lev k) {n : ℕ} (g : GL (Fin n) k)
    (h : ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ (V.c + 1)) : g ∈ V.J n := by
  have hu : uniformizer k ^ (V.c + 1) < 1 := pow_lt_one₀ zero_le' uniformizer_lt_one (Nat.succ_ne_zero _)
  have e : ∀ i, valuation k (g.val i i) = 1 := fun i => by
    have h1 : valuation k (g.val i i - 1) < 1 := by
      have := h i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      exact this.trans_lt hu
    have := Valuation.map_one_add_of_lt _ h1
    rwa [add_sub_cancel] at this
  refine (Sig.memJ k V n g).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · by_cases hij : i = j
    · subst hij
      exact (e i).le
    · have := h i j
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at this
      exact (this.trans_lt hu).le
  · have := h i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', sub_zero] at this
    rwa [GlAx.unif_spec]
  · have h0 : g.val i i ≠ 0 := fun h0 => by
      have := e i
      simp [h0] at this
    refine ⟨Units.mk0 _ h0, V.le (mem_Uc.2 ⟨e i, ?_⟩), rfl⟩
    have := h i i
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
    rwa [zpow_natCast]

private theorem proj_int {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) {Δ s : k} (hs : s * s = Δ)
    (a : Lsq k Δ) (ha : IsIntegral O a) : valuation k (proj hs a) ≤ 1 := by
  have hv : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).1 ⟨x, rfl⟩, fun x hx => (hO.range x).2 hx⟩
  have h : IsIntegral O (proj hs a) := ha.map_of_comp_eq (RingHom.id O) (proj hs) (by
    ext x
    have e : algebraMap O (Lsq k Δ) x = ⟨algebraMap O k x, 0⟩ := rfl
    simp [proj, e])
  exact hv.mem_of_integral h

end Loc

private theorem mem_KD {K O : Type} [Field K] [CommRing O] [Algebra O K] {Δ : K} (x : DX Δ) (hd : (mt x).det = 1)
    (hi : ∀ i j, IsIntegral O (mt x i j)) : x ∈ KD Δ O := by
  let X : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := fun i j => ⟨mt x i j, hi i j⟩
  have hX : X.det = 1 := Subtype.ext (by
    have h := RingHom.map_det ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) X
    refine h.trans ?_
    exact hd)
  exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mk'' X (by rw [hX]; exact isUnit_one), Units.ext (Matrix.ext fun i j => rfl)⟩

private theorem det_conj {K : Type} [Field K] {Δ : K} (a b : DX Δ) (h : (mt b).det = 1) : (mt (a⁻¹ * b * a)).det = 1 := by
  have e : mt (a⁻¹ * b * a) = mt a⁻¹ * mt b * mt a := rfl
  have e2 : mt a⁻¹ * mt a = 1 := by
    show mt (a⁻¹ * a) = 1
    rw [inv_mul_cancel]
    rfl
  rw [e, Matrix.det_mul, Matrix.det_mul, h, mul_one, ← Matrix.det_mul, e2, Matrix.det_one]

private theorem val_norm {F : Type} [Field F] [NumberField F] (v : Pl F) :
    valuation (Kv v) ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) ≤ uniformizer (Kv v) := by
  rw [le_uniformizer_iff]
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
  have h2 : (Valued.v : Valuation (Kv v) _) ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) < 1 := by
    have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v ((Ideal.absNorm v.asIdeal : ℕ) : F)
    have e2 : ((Ideal.absNorm v.asIdeal : ℕ) : Kv v) = algebraMap F (Kv v) ((Ideal.absNorm v.asIdeal : ℕ) : F) := (map_natCast _ _).symm
    rw [e2]
    refine e.trans_lt ?_
    change v.valuation F (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) < 1 at h
    rw [map_natCast] at h
    exact h
  haveI : (Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he : (valuation (Kv v)).IsEquiv (Valued.v : Valuation (Kv v) (WithZero (Multiplicative ℤ))) := isEquiv _ _
  simp only [← not_le] at h2 ⊢
  exact fun h3 => h2 (he.one_le_iff_one_le.1 h3)

private theorem eD_sub {K : Type} [Field K] {Δ s : K} (hs : s * s = Δ) (x : DX Δ) (i j : Fin 2) :
    ((eD hs x).val - 1) i j = proj hs ((mt x - 1) i j) := by
  have e : (eD hs x).val i j = proj hs (mt x i j) := rfl
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem nat_int {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (n : ℕ) : IsIntegral O (n : R) := by
  simpa using isIntegral_algebraMap (R := O) (A := R) (x := (n : O))

private def nrm {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) : ℕ :=
  ∏ v ∈ A.Sg, Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1)

private theorem mem_lvS_of_congruence {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) (hA : A.Ok) (y : DA Δ) (g : SA Δ)
    (key : ∀ (v : Pl F) (i j : Fin 2), ∃ a, IsIntegral (Ov v) a ∧ (mt ((y⁻¹ * g * y : DA Δ).1 v) - 1) i j =
      (nrm A : Lsq (Kv v) (cv v Δ)) * a) : g ∈ A.lvS y := by
  obtain ⟨-, -, hInt, -, hU2⟩ := datOk _ _ A hA
  have hg1 : ∀ v, (mt ((g : DA Δ).1 v)).det = 1 := fun v => by
    have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 g.2 v)
    exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
  have e : (MulAut.conj y⁻¹).toMonoidHom (g : DA Δ) = y⁻¹ * g * y := by simp
  rw [SD.lvS, Subgroup.mem_subgroupOf, Subgroup.mem_comap, e, hU2]
  refine ⟨fun v hv => mem_J_of_cong _ _ fun i j => ?_, fun v hv => mem_KD _ ?_ fun i j => ?_⟩
  · obtain ⟨a, ha, e1⟩ := key v i j
    obtain ⟨r, hr⟩ : Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1) ∣ nrm A :=
      Finset.dvd_prod_of_mem (fun v => Ideal.absNorm v.asIdeal ^ ((A.V v).c + 1)) hv
    rw [eD_sub, e1, map_mul, map_natCast, map_mul, hr, Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
    have h1 : valuation (Kv v) ((r : ℕ) : Kv v) ≤ 1 := natCast_mem (valuation (Kv v)).integer r
    have h2 := proj_int (hInt v hv).1 (A.hs v hv) a ha
    calc _ ≤ uniformizer (Kv v) ^ ((A.V v).c + 1) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (pow_le_pow_left' (val_norm v) _) h1) h2
      _ = _ := by simp
  · exact det_conj _ _ (hg1 v)
  · obtain ⟨a, ha, e1⟩ := key v i j
    have e2 : mt ((y⁻¹ * g * y : DA Δ).1 v) i j = (mt ((y⁻¹ * g * y : DA Δ).1 v) - 1) i j + (1 : Matrix (Fin 2) (Fin 2) _) i j := by
      simp
    rw [e2, e1]
    refine IsIntegral.add (IsIntegral.mul (nat_int _) ha) ?_
    rw [Matrix.one_apply]
    split_ifs
    exacts [isIntegral_one, isIntegral_zero]

private theorem mem_under {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (N : ℕ)
    (hN : (N : 𝓞 (Lp L)) ∈ (un w).asIdeal) : (N : 𝓞 L) ∈ w.asIdeal := by
  have h2 := Ideal.mem_comap.1 hN
  simpa using h2

private theorem norm_ne {F : Type} [Field F] [NumberField F] (v : Pl F) : Ideal.absNorm v.asIdeal ≠ 0 :=
  fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

private theorem nrm_ne {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) : nrm A ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (norm_ne v)

private theorem mem_of_dvd {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (M : ℕ)
    (h : Ideal.absNorm (un w).asIdeal ∣ M) : ((3 * M : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  obtain ⟨q, rfl⟩ := h
  refine mem_under w _ ?_
  rw [Nat.cast_mul, Nat.cast_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))

private theorem entry_mono {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (z : Kw w) (a q : ℕ)
    (h : ∃ b ∈ w.adicCompletionIntegers L, z = ((3 * (a * q) : ℕ) : Kw w) * b) :
    ∃ b ∈ w.adicCompletionIntegers L, z = (a : Kw w) * b := by
  obtain ⟨b, hb, e⟩ := h
  refine ⟨(3 * q : ℕ) * b, mul_mem (natCast_mem _ _) hb, ?_⟩
  rw [e]
  push_cast
  ring

private theorem abs_lev {α β γ υ σ : Type} (Y : Finset α) (p : α → β → Prop) (hY : ∀ y ∈ Y, {v | ¬ p y v}.Finite)
    (b : β → ℕ) (hb : ∀ v, b v ≠ 0) (un : γ → β) (mem : ℕ → γ → Prop) (hmem : ∀ w M, b (un w) ∣ M → mem (3 * M) w)
    (C : ℕ → υ → Prop) (D : υ → σ → Prop) (E : α → σ → Prop)
    (h : ∀ y, ∃ a, a ≠ 0 ∧ ∀ q U, C (3 * (a * q)) U → ∀ g, D U g → E y g) :
    ∃ m : ℕ, 3 ≤ m ∧ (∀ w, ¬ mem m w → ∀ y ∈ Y, p y (un w)) ∧ ∀ U, C m U → ∀ y ∈ Y, ∀ g, D U g → E y g := by
  classical
  choose a ha hE using h
  let P : Finset β := (Set.Finite.biUnion Y.finite_toSet hY).toFinset
  let M : ℕ := (∏ y ∈ Y, a y) * ∏ v ∈ P, b v
  have hM : 0 < M := Nat.pos_of_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun y _ => ha y)
    (Finset.prod_ne_zero_iff.2 fun v _ => hb v))
  refine ⟨3 * M, Nat.le_mul_of_pos_right 3 hM, fun w hw y hy => ?_, fun U hU y hy g hg => ?_⟩
  · by_contra hne
    have hv : un w ∈ P := (Set.Finite.mem_toFinset _).2 (Set.mem_biUnion hy hne)
    exact hw (hmem w M (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hv) _))
  · obtain ⟨q, hq⟩ : a y ∣ M := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hy) _
    rw [hq] at hU
    exact hE y q U hU g hg

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Ov DX KD RP SA Lsq

theorem UpperTheory.V.Z.Sym.So.congLev :
    UpperTheory.V.Z.Sym.So.CongLev := by
  intro L _ _ _ B hB _ _ _ A hA _ Y hY
  refine abs_lev Y _ hY (fun v => Ideal.absNorm v.asIdeal) norm_ne un _ (fun w M h => mem_of_dvd w M h) _ _ _ fun y => ?_
  exact (hB.cong y (nrm A) (nrm_ne A)).elim fun a h => ⟨a, h.1, fun q U hU g hg =>
    mem_lvS_of_congruence A hA y g fun v => h.2 g v fun w _ i j => entry_mono w _ _ _ (((hU _).1 hg).2 w i j)⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LevExt
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Gen
variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (h : s * s = Δ) (h' : s' * s' = Δ) (e : s = s') :
    Sig.eD h = Sig.eD h' := by
  subst e; rfl

private theorem mem_lvS (A : SD Δ) (y : DA Δ) (g : SA Δ) :
    g ∈ A.lvS y ↔ y⁻¹ * (g : DA Δ) * y ∈ A.dat.U2 := by
  unfold SD.lvS
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  show (MulAut.conj y⁻¹) (g : DA Δ) ∈ _ ↔ _
  rw [MulAut.conj_apply, inv_inv]

private theorem conj_at (y g : DA Δ) (v : Pl F) (h : y.1 v = 1) : (y⁻¹ * g * y).1 v = g.1 v := by
  have : (y⁻¹ * g * y).1 v = (y.1 v)⁻¹ * g.1 v * y.1 v := rfl
  rw [this, h, inv_one, one_mul, mul_one]

private theorem up (A A₀ : SD Δ) (hA : A.Ok) (hA₀ : A₀.Ok) (hE : A.Ext A₀) (x : DA Δ) (h0 : x ∈ A₀.dat.U2)
    (hn : ∀ v (h : v ∈ A.Sg), v ∉ A₀.Sg → Sig.eD (A.hs v h) (x.1 v) ∈ (Sig.Lev.iw (Kv v)).J 2) : x ∈ A.dat.U2 := by
  have d0 := ((datOk F Δ A₀ hA₀).2.2.2.2 x).1 h0
  refine ((datOk F Δ A hA).2.2.2.2 x).2 ⟨fun v hv => ?_, fun v hv => d0.2 v fun h => hv (hE.sub h)⟩
  by_cases h : v ∈ A₀.Sg
  · rw [hE.V v h, eD_congr (A.hs v hv) (A₀.hs v h) (hE.s v h)]
    exact d0.1 v h
  · rw [hE.iw v hv h]
    exact hn v hv h

end Gen

section Br
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L}

private theorem spl (hB : B.Ok) (w : Plc L) (R : B.toRingBr.Split w) (g : SA B.Δ)
    (h : cLoc w (B.bS g : UA L 2) ∈ (iw w).J 2) :
    Sig.eD R.hs ((g : DA B.Δ).1 (un w)) ∈ (Sig.Lev.iw (Kv (un w))).J 2 := by
  rw [hB.splS w R g] at h
  exact (R.J (Sig.Lev.iw _) (iw w) rfl (fun a => R.Uo a) 2 _).1 h

private theorem lev_mem {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)} {V : ∀ w : Plc L, Sig.Lev (Kw w)} {x : UA L n}
    (h : x ∈ lev U S V) : x ∈ U ∧ ∀ w ∈ S, cLoc w x ∈ (V w).J n := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
  refine ⟨h1, fun w hw => ?_⟩
  simp only [Subgroup.mem_iInf] at h2
  exact h2 w hw

end Br

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Sym.So.levExt :
    UpperTheory.V.Z.Sym.So.LevExt := by
  intro L _ _ _ B hB T S VL A hA hF A₀ hA₀ hE S₁ h1 _ U y hy hU g hg
  obtain ⟨hgU, hgJ⟩ := lev_mem hg
  refine (mem_lvS A y g).2 (up A A₀ hA hA₀ hE _ ((mem_lvS A₀ y g).1 (hU g hgU)) ?_)
  intro v hv h0
  obtain ⟨w, hwS, rfl⟩ := (hF.sg v).1 hv
  have hsp : IsSplitAt w := hF.pl.split w hwS
  rw [conj_at y (g : DA B.Δ) _ (hy _ hv), eD_congr (A.hs _ hv) (T w hsp).hs (hF.s w hwS hsp)]
  exact spl hB w (T w hsp) g (hgJ w ((h1 w hwS).resolve_right h0))

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RepsEx
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trim {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (y : DA Δ) (hy : D.Off y) :
    ∃ t w : DA Δ, w ∈ D.U2 ∧ t * w = y ∧ D.Off t ∧ {v | t.1 v ≠ 1}.Finite := by
  classical
  let P : Pl F → Prop := fun v => y.1 v ∈ KD ((cv v) Δ) (Ov v) ∧ v ∉ D.Sg
  have hfin : {v | y.1 v ∉ KD ((cv v) Δ) (Ov v)}.Finite := Filter.eventually_cofinite.mp y.2
  have hbad : {v | ¬ P v}.Finite := by
    refine (hfin.union D.Sg.finite_toSet).subset ?_
    intro v hv
    by_cases h1 : y.1 v ∈ KD ((cv v) Δ) (Ov v)
    · exact Or.inr (by_contra fun h2 => hv ⟨h1, h2⟩)
    · exact Or.inl h1
  refine ⟨⟨fun v => if P v then 1 else y.1 v, ?_⟩, ⟨fun v => if P v then y.1 v else 1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine Filter.eventually_cofinite.mpr (hbad.subset ?_)
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) ∈ KD ((cv v) Δ) (Ov v)
    rw [if_pos h]
    exact one_mem _
  · show ∀ᶠ v in Filter.cofinite, (if P v then y.1 v else 1) ∈ KD ((cv v) Δ) (Ov v)
    refine Filter.Eventually.of_forall fun v => ?_
    by_cases h : P v
    · rw [if_pos h]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · simp only [Dat.U2, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show (if P v then y.1 v else 1) ∈ D.J2v v
    by_cases h : P v
    · rw [if_pos h, Dat.J2v, if_neg h.2]
      exact h.1
    · rw [if_neg h]
      exact one_mem _
  · refine Subtype.ext (funext fun v => ?_)
    show (if P v then 1 else y.1 v) * (if P v then y.1 v else 1) = y.1 v
    split_ifs <;> simp
  · intro v hv
    show (if P v then 1 else y.1 v) = 1
    split_ifs
    · rfl
    · exact hy v hv
  · refine hbad.subset ?_
    intro v hv h
    apply hv
    show (if P v then 1 else y.1 v) = 1
    rw [if_pos h]

theorem UpperTheory.V.Z.Sym.So.repsEx :
    UpperTheory.V.Z.Sym.So.RepsEx := by
  intro F _ _ Δ A hA hCR ι hι
  classical
  obtain ⟨Y, hY, hdec⟩ := hCR F Δ A.dat (datOk F Δ A hA).1 ι hι
  let f : DA Δ → DA Δ := fun y => if h : A.dat.Off y then (trim A.dat y h).choose else y
  refine ⟨Y.image f, ?_, ?_⟩
  · intro y' hy'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    obtain ⟨w, -, -, ht, hfin⟩ := (trim A.dat y (hY y hy)).choose_spec
    simp only [f, dif_pos (hY y hy)]
    exact ⟨ht, hfin⟩
  · intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, rfl⟩ := hdec g
    obtain ⟨w, hw, hty, -, -⟩ := (trim A.dat y (hY y hy)).choose_spec
    refine ⟨γ, s, hs, f y, Finset.mem_image_of_mem f hy, w * u, mul_mem hw hu, ?_⟩
    simp only [f, dif_pos (hY y hy)]
    conv_lhs => rw [← hty]
    simp only [mul_assoc]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem rp_exists_unique {I : Type} {Gv Hv : I → Type} [∀ v, Group (Gv v)] [∀ v, Group (Hv v)]
    (K : ∀ v, Subgroup (Gv v)) (S : Finset I) (e : ∀ v, v ∈ S → (Gv v →* Hv v))
    (he : ∀ v h, Function.Bijective (e v h)) (w : ∀ v, Hv v) :
    ∃! g : RP Gv K, (∀ v (h : v ∈ S), e v h (g.1 v) = w v) ∧ ∀ v, v ∉ S → g.1 v = 1 := by
  classical
  let x : ∀ v, Gv v := fun v => if h : v ∈ S then Function.surjInv (he v h).2 (w v) else 1
  have hx : x ∈ RP Gv K := by
    show ∀ᶠ v in Filter.cofinite, x v ∈ K v
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    rw [Finset.mem_coe] at h
    exact hv (by simp [x, h, one_mem])
  refine ⟨⟨x, hx⟩, ⟨fun v h => ?_, fun v h => ?_⟩, ?_⟩
  · show e v h (x v) = w v
    simp only [x, dif_pos h]
    exact Function.surjInv_eq _ _
  · show x v = 1
    simp [x, h]
  · rintro g ⟨h1, h2⟩
    apply Subtype.ext
    funext v
    by_cases h : v ∈ S
    · apply (he v h).1
      rw [h1 v h]
      show w v = e v h (x v)
      simp only [x, dif_pos h]
      exact (Function.surjInv_eq _ _).symm
    · rw [h2 v h]
      show 1 = x v
      simp [x, h]

private theorem det_dg_inv {k : Type} [Field k] (t : kˣ) :
    ((dg ![t, t⁻¹] : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 := by
  simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

end UpperTheory.V.Z.Sym.So

private theorem mem_su_of_det_eq_one {K : Type} [Field K] {D : K} (x : DX D) (hx : (Glob.mt x).det = 1) :
    x ∈ SU D := by
  rw [SU, MonoidHom.mem_ker]
  refine Units.ext ?_
  rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact hx

theorem UpperTheory.V.Z.Sym.So.elEx :
    UpperTheory.V.Z.Sym.So.ElEx := by
  intro F _ _ Δ A hA
  have loc := fun v (h : v ∈ A.Sg) => (datOk F Δ A hA).2.2.1 v h
  have bU : ∀ v (h : v ∈ A.Sg), Function.Bijective (eU (A.hs v h)) := fun v h =>
    (eU_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  have bD : ∀ v (h : v ∈ A.Sg), Function.Bijective (eD (A.hs v h)) := fun v h =>
    (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h) (loc v h).2.2.1).1
  refine ⟨fun d => ?_, fun d => ?_, ?_, ?_, ?_⟩
  · exact rp_exists_unique (Hv := fun v => GL (Fin 3) (Kv v)) _ A.Sg (fun v h => eU (A.hs v h)) bU
      (fun v => dg (d v))
  · exact rp_exists_unique (Hv := fun v => GL (Fin 2) (Kv v)) _ A.Sg (fun v h => eD (A.hs v h)) bD
      (fun v => dg (d v))
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eU (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 3)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g g' d d' ⟨hg1, hg2⟩ ⟨hg1', hg2'⟩
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show eD (A.hs v h) (g.1 v * g'.1 v) = dg (d v * d' v)
      rw [map_mul, hg1 v h, hg1' v h]
      exact (map_mul (diagT (Kv v) (Fin 2)) _ _).symm
    · show g.1 v * g'.1 v = 1
      rw [hg2 v h, hg2' v h, mul_one]
  · rintro g t ⟨hg1, hg2⟩
    simp only [SA, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show g.1 v ∈ SU (cv v Δ)
    by_cases h : v ∈ A.Sg
    · have hfac := (eD_facts (Kv v) (Ov v) (loc v h).1 (loc v h).2.1 _ (A.s v) (A.hs v h)
        (loc v h).2.2.1).2.2.2.2.1 (g.1 v)
      have hd := hg1 v h
      have h2 : ((dg (SD.dS t v) : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)).det = 1 :=
        det_dg_inv (t v)
      refine mem_su_of_det_eq_one _ ?_
      rw [hfac.1, hd, h2, map_one]
    · exact (hg2 v h).symm ▸ one_mem _

end
end

