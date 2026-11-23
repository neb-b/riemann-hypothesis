module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExChi
section
theorem UpperTheory.V.Sd.Wc.exChi :
    UpperTheory.V.Sd.Wc.ExChi := by
  intro G Z _ _ K ζ ω hc hK
  have hcomm : ∀ (z : Z) (g : G), g * ζ z = ζ z * g := fun z g =>
    Subgroup.mem_center_iff.mp (hc z) g
  have hN : ζ.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨z, rfl⟩ g
    refine ⟨z, ?_⟩
    rw [hcomm z g, mul_assoc, mul_inv_cancel, mul_one]
  have hrep : ∀ x ∈ K ⊔ ζ.range, ∃ k ∈ K, ∃ z : Z, x = k * ζ z := by
    intro x hx
    obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    exact ⟨k, hk, z, rfl⟩
  have hwd : ∀ k ∈ K, ∀ k' ∈ K, ∀ z z' : Z, k * ζ z = k' * ζ z' → ω z = ω z' := by
    intro k hk k' hk' z z' h
    have h1 : ζ (z' * z⁻¹) = k'⁻¹ * k := by
      rw [map_mul, map_inv]
      calc ζ z' * (ζ z)⁻¹ = k'⁻¹ * (k' * ζ z') * (ζ z)⁻¹ := by group
        _ = k'⁻¹ * (k * ζ z) * (ζ z)⁻¹ := by rw [h]
        _ = k'⁻¹ * k := by group
    have h2 : ω (z' * z⁻¹) = 1 := hK _ (by rw [h1]; exact K.mul_mem (K.inv_mem hk') hk)
    rw [map_mul, map_inv] at h2
    exact (mul_inv_eq_one.mp h2).symm
  choose kf hkf zf hzf using fun h : ↥(K ⊔ ζ.range) => hrep h.1 h.2
  have hval : ∀ (h : ↥(K ⊔ ζ.range)) (k : G), k ∈ K → ∀ z : Z,
      (h : G) = k * ζ z → ω (zf h) = ω z := by
    intro h k hk z hz
    exact hwd _ (hkf h) _ hk _ _ ((hzf h).symm.trans hz)
  refine ⟨{ toFun := fun h => ω (zf h), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact (hval 1 1 K.one_mem 1 (by simp)).trans (map_one ω)
  · intro a b
    show ω (zf (a * b)) = ω (zf a) * ω (zf b)
    rw [← map_mul]
    refine hval _ (kf a * kf b) (K.mul_mem (hkf a) (hkf b)) _ ?_
    rw [Subgroup.coe_mul, hzf a, hzf b, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (ζ (zf a)), ← hcomm (zf a) (kf b), mul_assoc]
  · intro h
    exact ⟨⟨kf h, hkf h, zf h, hzf h⟩, fun k hk z hz => hval h k hk z hz⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.FinProj
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Sd.Wc

private theorem sep_of_sum {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ p : V →ₗ[ℂ] X, p x ≠ 0 ∧ ∀ g y, p (τ g y) = σ g (p y) := by
  obtain ⟨-, hirr⟩ := (isIrreducible_iff σ).1 hσ
  have key : ∀ (f : X →ₗ[ℂ] V), (∀ g v, f (σ g v) = τ g (f v)) → ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, τ g v ∈ U) →
      ¬ LinearMap.range f ≤ U → ∀ x, f x ∈ U → x = 0 := by
    intro f hf U hU hn x hx
    rcases hirr (U.comap f) (fun g v hv => by
      rw [Submodule.mem_comap, hf]; exact hU g _ hv) with e | e
    · have : x ∈ U.comap f := hx
      rwa [e, Submodule.mem_bot] at this
    · exact absurd (LinearMap.range_le_iff_comap.2 e) hn
  obtain ⟨M, ⟨hst, hxM⟩, hmax⟩ := zorn_le₀ {U : Submodule ℂ V | (∀ g, ∀ v ∈ U, τ g v ∈ U) ∧ x ∉ U}
    (fun c hc hch => by
      rcases c.eq_empty_or_nonempty with rfl | hne
      · exact ⟨⊥, ⟨fun g v hv => by simp_all, by simpa using hx⟩, by simp⟩
      refine ⟨sSup c, ⟨fun g v hv => ?_, fun hv' => ?_⟩, fun z hz => le_sSup hz⟩
      · obtain ⟨U, hU, hvU⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv
        exact le_sSup hU ((hc hU).1 g v hvU)
      · obtain ⟨U, hU, hvU⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hv'
        exact (hc hU).2 hvU)
  have hsup : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) →
      ∀ g, ∀ v ∈ M ⊔ LinearMap.range f, τ g v ∈ M ⊔ LinearMap.range f := fun f hf g v hv => by
    obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _), ← hf]
    exact Submodule.add_mem_sup (hst g a ha) ⟨_, rfl⟩
  have hmem : ∀ f : X →ₗ[ℂ] V, (∀ g v, f (σ g v) = τ g (f v)) → ¬ LinearMap.range f ≤ M →
      x ∈ M ⊔ LinearMap.range f := fun f hf hn => by
    by_contra hc
    exact hn (le_sup_right.trans (hmax ⟨hsup f hf, hc⟩ le_sup_left))
  obtain ⟨⟨f, hf⟩, hn⟩ : ∃ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, ¬ LinearMap.range f.1 ≤ M := by
    by_contra hn
    push Not at hn
    have : (⊤ : Submodule ℂ V) ≤ M := h ▸ iSup_le hn
    exact hxM (this trivial)
  have htop : (⊤ : Submodule ℂ V) ≤ M ⊔ LinearMap.range f := by
    rw [← h]
    refine iSup_le fun f' => ?_
    by_contra hc
    obtain ⟨a, ha, _, ⟨y, rfl⟩, e⟩ := Submodule.mem_sup.1 (hmem f'.1 f'.2 fun hl => hc (hl.trans le_sup_left))
    have h2 : f'.1 y ∈ M ⊔ LinearMap.range f := by
      rw [eq_sub_of_add_eq' e]
      exact Submodule.sub_mem _ (hmem f hf hn) (Submodule.mem_sup_left ha)
    have h3 := key f'.1 f'.2 _ (hsup f hf) hc y h2
    subst h3
    exact hxM (by rw [← e]; simpa using ha)
  have hbij : Function.Bijective (M.mkQ ∘ₗ f) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => key f hf M hst hn y ((Submodule.Quotient.mk_eq_zero M).1 hy), fun q => ?_⟩
    obtain ⟨v, rfl⟩ := M.mkQ_surjective q
    obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))
    refine ⟨y, ?_⟩
    rw [map_add (f := _), show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add]
    rfl
  let e := LinearEquiv.ofBijective _ hbij
  have hp : ∀ a ∈ M, ∀ y, e.symm (M.mkQ (a + f y)) = y := fun a ha y => by
    rw [map_add (f := _), show M.mkQ a = 0 from (Submodule.Quotient.mk_eq_zero M).2 ha, zero_add, LinearEquiv.symm_apply_eq]
    rfl
  refine ⟨e.symm.toLinearMap ∘ₗ M.mkQ, fun h0 => hxM ?_, fun g v => ?_⟩
  · exact (Submodule.Quotient.mk_eq_zero M).1 ((map_eq_zero_iff e.symm e.symm.injective).1 h0)
  · obtain ⟨a, ha, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := v)))
    change e.symm (M.mkQ _) = σ g (e.symm (M.mkQ _))
    rw [hp a ha, map_add (τ g), ← hf, hp _ (hst g a ha)]

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]

end UpperTheory.V.Sd.Wc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.FixGlob
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc UpperTheory.V.Af.GlobalFixedVectors Matrix

private theorem mem_Kc {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} :
    k ∈ Kc c ↔ ∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  simp [Kc, Subgroup.mem_iInf]

private theorem entry_Kc {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) (i j : Fin 2) :
    k i j ∈ UpperTheory.V.Af.Ohat F := by
  refine mem_Ohat.2 fun w => ?_
  obtain ⟨g, -, hg⟩ := mem_Kc.1 hk w
  have e := congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) hg
  change ((g i j : w.adicCompletionIntegers F) : w.adicCompletion F) = pLoc F w (k i j) at e
  rw [← e]
  exact (g i j).2

private theorem Kc_le {F : Type} [Field F] [NumberField F] {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) : k ∈ KLev F 2 1 := by
  let A : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨k i j, entry_Kc hk i j⟩
  let B : Matrix (Fin 2) (Fin 2) (UpperTheory.V.Af.Ohat F) := fun i j => ⟨(k⁻¹ : GF F) i j, entry_Kc (inv_mem hk) i j⟩
  have hA : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix A = k.val := rfl
  have hB : (UpperTheory.V.Af.Ohat F).subtype.mapMatrix B = (k⁻¹ : GF F).val := rfl
  have hinj : Function.Injective ((UpperTheory.V.Af.Ohat F).subtype.mapMatrix (m := Fin 2)) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_, ?_⟩
  · rw [map_mul, map_one, hA, hB, Units.mul_inv]
  · rw [map_mul, map_one, hA, hB, Units.inv_mul]
  · haveI : Subsingleton (UpperTheory.V.Af.Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(UpperTheory.V.Af.Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · exact Units.ext hA

theorem UpperTheory.V.Sd.Wc.fixGlob :
    UpperTheory.V.Sd.Wc.FixGlob := by
  classical
  intro F _ _ V _ _ ρ hρ c x hc
  have key : ∀ S : Finset (Pl F),
      (∀ k ∈ KAway 2 1 S, k ∈ Kc c → ρ k x = x) → (∀ k ∈ KAway 2 1 ∅, k ∈ Kc c → ρ k x = x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      intro h
      refine ih fun k hk hl => ?_
      rw [mem_Kc] at hl
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hc w _ (hl w)
      have h4 := h _ h2 (mem_Kc.2 fun v => by
        by_cases hv : v = w
        · subst hv; simp [pLoc_locGL]
        · simpa [pLoc_locGL_of_ne hv] using hl v)
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) ((hρ x).mem_nhds (by simp))
  intro k hk
  exact key S (fun k hk _ => hS hk) k (mem_KAway.2 ⟨Kc_le hk, by simp⟩) hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.GlFacts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix NNReal

namespace UpperTheory.V.Sd.Wc

section

variable {F : Type} [Field F] [NumberField F]

private theorem congruence_subgroup_one_entry_bounds (w : Pl F) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w 1) :
    (∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) ≤ 1) ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) < 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) < 1 ∧
      Valued.v (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det = 1 := by
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := hk
  change ![0, 1] ᵥ* _ = ![0, 1] at hk'
  have hm : ∀ x : w.adicCompletionIntegers F, x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 1 →
      Valued.v (x : w.adicCompletion F) < 1 := by
    intro x hx
    rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hx
    exact lt_of_le_of_ne x.2 hx
  have h0 := congrFun hk' 0
  have h1 := congrFun hk' 1
  refine ⟨fun i j => (k i j).2, hm (k 1 0) ?_, hm (k 1 1 - 1) ?_, ?_⟩
  · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using h0
  · refine Ideal.Quotient.eq.1 ?_
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using h1
  · have hu : IsUnit (k : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)).det :=
      (Matrix.GeneralLinearGroup.det k).isUnit
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
    rw [← hu]
    exact congrArg Valued.v ((w.adicCompletionIntegers F).subtype.map_det _).symm

private def low {R : Type} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem low_mem (w : Pl F) (x : w.adicCompletion F) (hx : Valued.v x < 1) : low x ∈ K1 w 1 := by
  let y : w.adicCompletionIntegers F := ⟨x, hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 1 := by
    rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne
  refine ⟨low y, ?_, ?_⟩
  · change ![0, 1] ᵥ* _ = ![0, 1]
    ext j
    fin_cases j
    · simpa [low, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Ideal.Quotient.eq_zero_iff_mem] using hy
    · simp [low, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [low, y]

private theorem loc_mem_Kc (c : Pl F → ℕ) (w : Pl F) {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w (c w)) :
    locGL F 2 w k ∈ Kc c := by
  refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 ?_
  by_cases h : u = w
  · subst h; rwa [pLoc_locGL]
  · rw [pLoc_locGL_of_ne h]; exact one_mem _

variable {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι)

private theorem gl_apply (k : GF F) (v : InfinitePlace F) :
    D.gl k v = Matrix.GeneralLinearGroup.map (D.em v) (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k) := by
  ext i j; rfl

private theorem nu_eq_one (v : InfinitePlace F) {x : (D.pl v).adicCompletion F} (hx : Valued.v x = 1) : nu ι (D.em v x) = 1 :=
  le_antisymm ((D.le v x).2 hx.le) (not_lt.1 fun h => ((D.lt v x).1 h).ne hx)

open Classical in
private theorem gl_loc (v : InfinitePlace F) (a : GL (Fin 2) ((D.pl v).adicCompletion F)) :
    D.gl (locGL F 2 (D.pl v) a) = Pi.mulSingle v (Matrix.GeneralLinearGroup.map (D.em v) a) := by
  funext u
  rw [gl_apply]
  by_cases h : u = v
  · subst h; rw [pLoc_locGL, Pi.mulSingle_eq_same]
  · rw [pLoc_locGL_of_ne (fun e => h (D.inj e)), Pi.mulSingle_eq_of_ne h, map_one]

private theorem unit_val (v : InfinitePlace F) : ∃ x : (D.pl v).adicCompletion F, Valued.v x = 1 ∧
    D.em v x = v.embedding (unif (D.pl v) : Fˣ) / (l : ℂ) := by
  have hp : Valued.v ((atFin (D.pl v) (unif (D.pl v)) : ((D.pl v).adicCompletion F)ˣ) : (D.pl v).adicCompletion F) =
    WithZero.exp (-1 : ℤ) := unif_spec _
  refine ⟨((atFin (D.pl v) (unif (D.pl v)) : ((D.pl v).adicCompletion F)ˣ) : (D.pl v).adicCompletion F) / (l : _), ?_, ?_⟩
  · rw [map_div₀, hp, D.unif, div_self WithZero.exp_ne_zero]
  · rw [map_div₀, map_natCast, ← D.em_alg]; rfl

end

private theorem val_mul_sub {ν : Valuation ℂ ℝ≥0} {x y : ℂ} (hx : ν (x - 1) < 1) (hy : ν (y - 1) < 1) : ν (x * y - 1) < 1 := by
  have e : x * y - 1 = (x - 1) * (y - 1) + ((x - 1) + (y - 1)) := by ring
  rw [e]
  refine ν.map_add_lt ?_ (ν.map_add_lt hx hy)
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hx hy.le

private theorem val_zpow_sub {ν : Valuation ℂ ℝ≥0} {x : ℂ} (h1 : ν x = 1) (hx : ν (x - 1) < 1) (m : ℤ) : ν (x ^ m - 1) < 1 := by
  have hn : ∀ y : ℂ, ν (y - 1) < 1 → ∀ n : ℕ, ν (y ^ n - 1) < 1 := by
    intro y hy n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; exact val_mul_sub ih hy
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [zpow_natCast]; exact hn x hx n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    refine hn _ ?_ n
    have e : x⁻¹ - 1 = -(x⁻¹ * (x - 1)) := by field_simp; ring
    rwa [e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.glFacts :
    UpperTheory.V.Sd.Wc.GlFacts := by
  classical
  intro F _ _ l _ ι D
  have huf : ∀ e w, nu ι (D.uf e w) = 1 := by
    intro e w
    rw [LDat.uf, map_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    split_ifs with h
    · subst h
      obtain ⟨x, hx, e⟩ := unit_val D v
      rw [← e, map_zpow₀, nu_eq_one D v hx, one_zpow]
    · exact map_one _
  refine ⟨fun c hc => ⟨fun k hk v => ?_, fun a => ?_⟩, fun w hw a => ?_, gl_loc D, fun n e z x => ?_, huf, fun e e' he w => ?_⟩
  · have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hk (D.pl v))
    rw [hc] at h1
    obtain ⟨ha, hb, hd, he⟩ := congruence_subgroup_one_entry_bounds _ h1
    have hdet : (D.gl k v : Matrix (Fin 2) (Fin 2) ℂ).det = D.em v
        (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det :=
      ((D.em v).map_det _).symm
    refine ⟨fun i j => (D.le v _).2 (ha i j), (D.lt v _).2 hb, ?_, ?_, ?_⟩
    · have := (D.lt v _).2 hd
      rwa [map_sub, map_one] at this
    · rw [hdet]; exact nu_eq_one D v he
    · rw [hdet]; exact D.res v _ he
  · have key : ∀ s : Finset (InfinitePlace F), ∃ k ∈ Kc c, ∀ v,
        D.gl k v = if v ∈ s then low ((l * a v : ℕ) : ℂ) else 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨1, one_mem _, fun v => by simp⟩
      | insert u s hu ih =>
        obtain ⟨k, hk, hv⟩ := ih
        have hl : Valued.v ((l * a u : ℕ) : (D.pl u).adicCompletion F) < 1 := by
          rw [Nat.cast_mul, map_mul, D.unif]
          have h2 : Valued.v ((a u : ℕ) : (D.pl u).adicCompletion F) ≤ 1 :=
            natCast_mem ((D.pl u).adicCompletionIntegers F) (a u)
          refine mul_lt_one_of_nonneg_of_lt_one_left zero_le ?_ h2
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
        refine ⟨locGL F 2 (D.pl u) (low ((l * a u : ℕ) : (D.pl u).adicCompletion F)) * k,
          mul_mem (loc_mem_Kc c _ (by rw [hc]; exact low_mem _ _ hl)) hk, fun v => ?_⟩
        rw [map_mul, Pi.mul_apply, gl_loc, hv]
        by_cases h : v = u
        · subst h
          rw [Pi.mulSingle_eq_same, if_neg hu, mul_one, if_pos (Finset.mem_insert_self _ _)]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [low]
        · rw [Pi.mulSingle_eq_of_ne h, one_mul]
          simp [h]
    obtain ⟨k, hk, hv⟩ := key Finset.univ
    exact ⟨k, hk, fun v => by rw [hv, if_pos (Finset.mem_univ _)]; rfl⟩
  · funext v
    rw [gl_apply, pLoc_locGL_of_ne (fun e : D.pl v = w => hw (e ▸ D.mem v)), map_one, Pi.one_apply]
  · refine Subtype.ext (MvPolynomial.funext fun y => ?_)
    have hg : ∀ v, (D.gl (zc F z) v : Matrix (Fin 2) (Fin 2) ℂ) = !![D.ea v z, 0; 0, D.ea v z] := by
      intro v
      ext i j
      change D.ea v ((zc F z : Matrix (Fin 2) (Fin 2) (Af F)) i j) = _
      fin_cases i <;> fin_cases j <;> simp [zc]
    have h0 : ∀ v, D.ea v z ≠ 0 := fun v => (z.isUnit.map (D.ea v)).ne_zero
    have ha : act (D.gl (zc F z)) y = fun p => D.ea p.1 z * y p := by
      funext p
      obtain ⟨v, i⟩ := p
      fin_cases i <;> simp [act, hg, mul_comm]
    have hd : (detE e (D.gl (zc F z)) : ℂ) = ∏ v, D.ea v z ^ (2 * e v) := by
      change ((∏ v, Matrix.GeneralLinearGroup.det (D.gl (zc F z) v) ^ e v : ℂˣ) : ℂ) = _
      rw [Units.coe_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hg, zpow_mul, zpow_two]
      simp
    change MvPolynomial.eval y (wRep n e (D.gl (zc F z)) x).1 = MvPolynomial.eval y (_ • x.1)
    rw [eval_wRep, ha, x.2 (fun v => D.ea v z) y, MvPolynomial.smul_eval, hd, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [zpow_add₀ (h0 v), zpow_natCast, mul_comm]
  · by_cases hw : ∃ v, D.pl v = w
    · obtain ⟨v, rfl⟩ := hw
      obtain ⟨x, hx, ex⟩ := unit_val D v
      have hs : ∀ e, D.uf e (D.pl v) = D.em v x ^ e v := by
        intro e
        rw [LDat.uf, Finset.prod_eq_single v (fun u _ hu => if_neg fun h => hu (D.inj h)) (by simp), if_pos rfl, ex]
      have h1 := nu_eq_one D v hx
      have h0 : D.em v x ≠ 0 := by intro h; rw [h] at h1; simp at h1
      obtain ⟨m, hm⟩ := he v
      have hl : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by
        rw [Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one]
      have e1 : D.em v x ^ e' v - D.em v x ^ e v = D.em v x ^ e v * ((D.em v x ^ (l - 1)) ^ m - 1) := by
        rw [← zpow_natCast, ← zpow_mul, hl, ← hm, mul_sub, ← zpow_add₀ h0, mul_one, add_sub_cancel]
      rw [hs, hs, e1, map_mul, map_zpow₀, h1, one_zpow, one_mul]
      exact val_zpow_sub (by rw [map_pow, h1, one_pow]) (D.res v x hx) m
    · have hs : ∀ e, D.uf e w = 1 := fun e => Finset.prod_eq_one fun v _ => if_neg fun h => hw ⟨v, h⟩
      rw [hs, hs, sub_self, map_zero]
      exact zero_lt_one
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkComm
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd.Wc

variable {F : Type} [Field F] [NumberField F]

private theorem ext_loc {g h : GL (Fin 2) (Af F)}
    (e : ∀ w, Matrix.GeneralLinearGroup.map (pLoc F w) g = Matrix.GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) (e w)

private theorem comm_of_triv {w : Pl F} (g : GL (Fin 2) (w.adicCompletion F)) {k : GL (Fin 2) (Af F)}
    (hk : Matrix.GeneralLinearGroup.map (pLoc F w) k = 1) : k * locGL F 2 w g = locGL F 2 w g * k := by
  refine ext_loc fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = w
  · subst hx; rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

private theorem fix_loc (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : x ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w)) :=
  fun k hk => hx _ ((hK F).2.2.2.2.2 c w k hk)

private theorem uop_mem (hR : HkReps) (hK : KcTop) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ)
    {x : V} (hx : x ∈ Hi.fixd ρ (Kc c)) (w : Pl F) : Uop w (ρ.comp (locGL F 2 w)) (c w) x ∈ Hi.fixd ρ (Kc c) := by
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨h1, h2⟩ := ha V _ x (fix_loc hK ρ c hx w)
  intro k hk
  have hkw : Matrix.GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := (Subgroup.mem_iInf.1 hk) w
  set kw := Matrix.GeneralLinearGroup.map (pLoc F w) k with hkwe
  have hm : k * (locGL F 2 w kw)⁻¹ ∈ Kc c := mul_mem hk (inv_mem ((hK F).2.2.2.2.2 c w kw hkw))
  have ht : Matrix.GeneralLinearGroup.map (pLoc F w) (k * (locGL F 2 w kw)⁻¹) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, ← hkwe, mul_inv_cancel]
  have e : k = k * (locGL F 2 w kw)⁻¹ * locGL F 2 w kw := by rw [inv_mul_cancel_right]
  have h3 : ρ (locGL F 2 w kw) (Uop w (ρ.comp (locGL F 2 w)) (c w) x) = Uop w (ρ.comp (locGL F 2 w)) (c w) x := h1 kw hkw
  have h4 : ρ (k * (locGL F 2 w kw)⁻¹) x = x := hx _ hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_mul, Module.End.mul_apply, h3, h2, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ρ _ (ρ (locGL F 2 w (a i)) x) = ρ (locGL F 2 w (a i)) x
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv _ ht, map_mul, Module.End.mul_apply, h4]

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.hkComm :
    UpperTheory.V.Sd.Wc.HkReps → UpperTheory.V.Sd.Wc.KcTop → UpperTheory.V.Sd.Wc.HkComm := by
  intro hR hK F _ _ V _ _ ρ c x hx w
  refine ⟨uop_mem hR hK ρ c hx w, fun w' => ?_⟩
  by_cases hw : w' = w
  · subst hw; rfl
  obtain ⟨N, a, -, ha⟩ := hR F w (c w)
  obtain ⟨N', a', -, ha'⟩ := hR F w' (c w')
  rw [(ha V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w') w)).2, (ha' V _ _ (fix_loc hK ρ c (uop_mem hR hK ρ c hx w) w')).2,
    (ha V _ _ (fix_loc hK ρ c hx w)).2, (ha' V _ _ (fix_loc hK ρ c hx w')).2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change ρ (locGL F 2 w (a i)) (ρ (locGL F 2 w' (a' j)) x) = ρ (locGL F 2 w' (a' j)) (ρ (locGL F 2 w (a i)) x)
  rw [← Module.End.mul_apply, ← map_mul, comm_of_triv (a' j) (pLoc_locGL_of_ne hw (a i)), map_mul, Module.End.mul_apply]
end
end

