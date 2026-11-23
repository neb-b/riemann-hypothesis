module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFreeSurjZmod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0245

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ApartOfNotMem
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

def CongUWG (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ Kw : Levels E a, HasLevelOff w₀ v' Kw U ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w (n := a)) ∧
      ∀ (Z W : Finset (HeightOneSpectrum (𝓞 E))),
        (∀ z ∈ Z, IsSplitAt z ∧ Apart z w₀ ∧ Apart z v' ∧ ∃ B, SatU U z B) →
        (∀ w ∈ W, IsSplitAt w ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B) →
      ∃ c : HeightOneSpectrum (𝓞 E) → ℤ → ℂ, (∀ w n, c w n ≠ 0) ∧
      ∀ (J : Type) (O : LocOps l ι Kw J) (θ : J → Qbar l), IsSysU O U θ →
        PolyApprox (Sum.elim θ (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U p.1 p.2)))
          {ϑ | ∃ U' θ', AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ (∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧
            Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Z, GenAtU Gen U' z) ∧ IsSysU O U' θ' ∧
            ϑ = Sum.elim θ' (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U' p.1 p.2))} ∧
        ((∀ j g, ∃ q : ℚ, O.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

theorem apart_of_not_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ}
    {u w : HeightOneSpectrum (𝓞 E)} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : Apart w u := by
  intro h
  have h1 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    change _ ∈ Ideal.comap _ _
    simpa using hu
  rw [← h] at h1
  apply hw
  have h2 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) w.asIdeal := h1
  simpa using h2

def CongFinG : Prop := CongUWG TyEll (GenOf DGen) WtLac

end UpperTheory.Gal.Int.Cong

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ExistsEllType
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {l : ℕ} [Fact l.Prime]

theorem exists_ellType (ha : 1 ≤ a) (w₀ : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (N : Set (GL (Fin a) (w₀.adicCompletion E))) (hN : N ∈ nhds (1 : GL (Fin a) (w₀.adicCompletion E))) (m₀ : ℕ) :
    ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m))), m₀ ≤ m ∧
      (J : Set (GL (Fin a) (w₀.adicCompletion E))) ⊆ N ∧ IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧
      Function.Surjective θ ∧ ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 →
        ∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
          (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ := by
  classical
  have hlp : l.Prime := Fact.out
  have hchar : ∀ {M : ℕ} [NeZero M] (χ : Multiplicative (ZMod M) →* ℂˣ) (z : Multiplicative (ZMod M)),
      χ z = χ (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd z).val := by
    intro M _ χ z
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · obtain rfl : a = 1 := by omega
    obtain ⟨N', hN'N, hN'o, h1N'⟩ := mem_nhds_iff.1 hN
    obtain ⟨J, θ, hJN, hJo, hJc, hJtf, hθ⟩ :=
      TypeExists.exists_congruence_surj (E := E) (l := l) (a := 1) le_rfl w₀ hl m₀ N' hN'o h1N'
    refine ⟨m₀, J, θ, le_rfl, hJN.trans hN'N, hJo, hJc, hJtf, hθ, fun χ _ σ _ _ _ => ⟨σ.smooth, fun s d e he => absurd ?_ he⟩⟩
    refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
    refine Units.ext (Matrix.ext fun i j => ?_)
    obtain rfl : i = j := Subsingleton.elim _ _
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
    have h := (GlobalTheory.SmGL.mem_unipRad.1 hu).2 b i i
    rw [Matrix.one_apply_eq] at h
    rw [h, Units.val_one, Matrix.one_apply_eq]
  · obtain ⟨m, hmm, J, lam, hJo, hJc, hJN, hJtf, hsurj, hsc⟩ :=
      TypeExists.exists_type_surj E w₀ a l hlp hl ha2 N hN m₀
    refine ⟨m, J, lam, hmm, hJN, hJo, hJc,
      fun x hx k hk hxk => hJtf x hx (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, hxk⟩), hsurj, fun χ hχ σ v hv0 hv => ?_⟩
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    refine hsc (χ (Multiplicative.ofAdd 1)) ?_ (fun h => hχ (MonoidHom.ext fun z => ?_)) σ v hv0 fun g => ?_
    · rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]
    · rw [hchar χ z, h, one_pow, MonoidHom.one_apply]
    · rw [hv g, hchar χ (lam g)]

end UpperTheory.Gal.Int.Cong

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.LacunaryBaseWeightAntitone
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {l : ℕ} [Fact l.Prime]

theorem exists_overPl (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal) :
    ∃ τ : E →+* ℂ, OverPl ι τ v' := by
  obtain ⟨σ, hσ⟩ := PlaceEmb.exists_embedding (p := l) v' hl
  refine ⟨(ι : Qbar l →+* ℂ).comp σ, fun x hx => ?_⟩
  have hx' : x ∈ PlaceEmb.smallIdeal σ := hσ ▸ hx
  simpa [PlaceEmb.mem_smallIdeal] using hx'

theorem exists_of_overPair (ι : Qbar l ≃+* ℂ) {v' : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (h : OverPair ι v' τ) :
    ∃ u : HeightOneSpectrum (𝓞 E), OverPl ι τ u ∧ ¬ Apart u v' := by
  let σ : E →+* Qbar l := ι.symm.toRingHom.comp τ
  have hne : PlaceEmb.smallIdeal σ ≠ ⊥ := fun h0 => by
    have : ((l : ℕ) : 𝓞 E) ∈ PlaceEmb.smallIdeal σ := by
      rw [PlaceEmb.mem_smallIdeal]
      simpa using PlaceEmb.norm_p_lt_one (p := l)
    rw [h0, Ideal.mem_bot] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  refine ⟨⟨PlaceEmb.smallIdeal σ, PlaceEmb.smallIdeal_isPrime σ, hne⟩, fun x hx => hx, fun hap => hap ?_⟩
  refine HeightOneSpectrum.ext ((v'.under (𝓞 (maximalRealSubfield E))).isMaximal.eq_of_le
    (HeightOneSpectrum.isPrime _).ne_top fun y hy => ?_).symm
  have hy' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y ∈ v'.asIdeal := hy
  change ‖ι.symm (τ ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E))‖ < 1
  rcases h with h | h
  · exact h _ hy'
  · have := h _ hy'
    rwa [show IsCMField.complexConj E ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) =
      ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) from
        (IsCMField.complexConj E).commutes (y : maximalRealSubfield E)] at this

def mu0 (a : ℕ) : Fin a → ℤ := fun k => -((a : ℤ) + 1) ^ (k : ℕ)

theorem lacunaryBaseWeight_antitone (a : ℕ) : Antitone (mu0 a) := fun _ _ h =>
  neg_le_neg (pow_le_pow_right₀ (by omega) h)

theorem gapJ_of_near (lam : DomWeight a) (N d : ℕ) (h : ∀ k, |lam.w k - (N : ℤ) * mu0 a k| ≤ d)
    (hN : (a + 1) * (2 * d + a) < N) (J : Multiset ℤ)
    (hJ : J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z)) : GapJ a J := by
  let f : Fin a → ℤ := fun k => (k : ℕ) - lam.w k
  have e : J = Finset.univ.val.map f := by
    refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
    rw [hJ, infOfWeight, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun k _ => ?_
    simp only [f, Function.comp]
    push_cast
    ring
  have hmono : Monotone f := fun i j hij => by
    have := lam.anti hij
    have h2 : (i : ℕ) ≤ j := hij
    simp only [f]
    omega
  have hs : J.sort (· ≤ ·) = List.ofFn f := by
    rw [e, Fin.univ_val_map, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ (List.pairwise_ofFn.2 fun i j hij => by simpa using hmono hij.le)
  intro i hi
  have g : ∀ k (hk : k < a), (List.ofFn f).getD k 0 = f ⟨k, hk⟩ := fun k hk => by
    simp [List.getD, hk]
  rw [hs, g (i + 1) hi, g 0 (by omega), g i (by omega)]
  have h0 := abs_le.1 (h ⟨0, by omega⟩)
  have h1 := abs_le.1 (h ⟨i, by omega⟩)
  have h2 := abs_le.1 (h ⟨i + 1, hi⟩)
  simp only [mu0, f, pow_zero, pow_succ] at h0 h1 h2 ⊢
  have hP : (1 : ℤ) ≤ ((a : ℤ) + 1) ^ i := one_le_pow₀ (by omega)
  generalize ((a : ℤ) + 1) ^ i = P at *
  have hN' : ((a : ℤ) + 1) * (2 * d + a) < N := by exact_mod_cast hN
  have hi' : (i : ℤ) + 1 < a := by exact_mod_cast hi
  have ha0 : (0 : ℤ) ≤ a := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  push_cast
  have k1 := mul_le_mul_of_nonneg_left h1.1 ha0
  have k0 := mul_le_mul_of_nonneg_left h0.2 ha0
  have k2 : (N : ℤ) * 1 ≤ N * P := mul_le_mul_of_nonneg_left hP hN0
  have k3 : (N : ℤ) * 1 ≤ N * a := mul_le_mul_of_nonneg_left (by omega) hN0
  have k4 : (a : ℤ) * i ≤ a * a := mul_le_mul_of_nonneg_left (by omega) ha0
  nlinarith

open MvPolynomial in
theorem dGen_ne_zero (a : ℕ) : DGen a ≠ 0 := by
  classical
  have hm : ∀ s t : Fin a →₀ ℕ, s ≠ t → (monomial s 1 - monomial t 1 : MvPolynomial (Fin a) ℤ) ≠ 0 := fun s t h h0 =>
    h (monomial_left_injective one_ne_zero (sub_eq_zero.1 h0))
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
      rw [X_pow_eq_monomial, X_pow_eq_monomial]
      refine hm _ _ fun e => ?_
      have := DFunLike.congr_fun e i
      simp [Finsupp.single_apply, Ne.symm h] at this
  · refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun k _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · push_neg at h
      rw [X_pow_eq_monomial, X, X, monomial_mul, one_mul]
      refine hm _ _ fun e => ?_
      have := DFunLike.congr_fun e j
      simp [Finsupp.single_apply, Ne.symm h.1, Ne.symm h.2] at this
  · refine Finset.prod_ne_zero_iff.2 fun m hm' => ?_
    have h1 : ∀ s : Fin a → ℕ, (∏ i, X i ^ s i : MvPolynomial (Fin a) ℤ) = monomial (Finsupp.equivFunOnFinite.symm s) 1 := fun s => by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    have h2 : (∏ i, X i : MvPolynomial (Fin a) ℤ) = ∏ i, X i ^ (fun _ => 1 : Fin a → ℕ) i := by simp
    rw [h2, h1, h1]
    refine hm _ _ fun e => (Finset.mem_filter.1 hm').2.2 (funext fun i => Fin.ext ?_)
    have := congrFun (Finsupp.equivFunOnFinite.symm.injective e) i
    have hi := i.2
    rw [this, Fin.val_one', Nat.mod_eq_of_lt (by omega)]

end UpperTheory.Gal.Int.Cong

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.OpenCompactMap
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW
open GlobalTheory.Cong.AdaptLev

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem exists_locLev {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a), (∀ w, H w ≤ intU a w) ∧
      (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) ∧ (∀ w u, ¬ Apart w u → H w = H u) ∧
      (∀ w, ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ H w, RU E a x φ = φ) ∧
      (∀ w, (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a w, RU E a x φ = φ) → H w = intU a w) ∧
      ∀ᶠ w in Filter.cofinite, H w = intU a w := by
  classical
  obtain ⟨φ₀, hφ₀U, hφ₀0⟩ := (Submodule.ne_bot_iff U).1 hU.ne_bot
  have hφ₀aut : IsAutFormU φ₀ := hU.aut φ₀ hφ₀U
  let stab : Subgroup (UA E a) :=
    { carrier := {x | RU E a x φ₀ = φ₀}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at hx hy ⊢
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        calc RU E a x⁻¹ φ₀ = RU E a x⁻¹ (RU E a x φ₀) := by rw [hx]
          _ = φ₀ := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a) := fun r =>
    if ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a r, RU E a x φ = φ then intU a r else intU a r ⊓ stab
  have hint : ∀ w, (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a w, RU E a x φ = φ) → H w = intU a w := fun w h => if_pos h
  refine ⟨H, fun r => ?_, fun r => ?_, fun w u h => ?_, fun r => ?_, hint, ?_⟩
  · simp only [H]
    split_ifs
    exacts [le_rfl, inf_le_left]
  · simp only [H]
    split_ifs
    · exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a r).2
    · have e : (((intU a r ⊓ stab).subgroupOf (locU a r)) : Set (locU a r)) =
          (((intU a r).subgroupOf (locU a r)) : Set (locU a r)) ∩
            (fun x : locU a r => (⟨x.1, ((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 x.2).1⟩ : finU (E := E) (n := a))) ⁻¹'
              {k : finU (E := E) (n := a) | RU E a k φ₀ = φ₀} := by
        ext x; exact Iff.rfl
      rw [e]
      exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a r).2.inter (hφ₀aut.level.preimage (Continuous.subtype_mk continuous_subtype_val _))
  · simp only [H, intU_congr h]
  · simp only [H]
    split_ifs with h1
    · exact h1
    · exact ⟨φ₀, hφ₀U, hφ₀0, fun x hx => (Subgroup.mem_inf.1 hx).2⟩
  · filter_upwards [GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces E a φ₀ hφ₀aut] with w hw
    exact hint w ⟨φ₀, hφ₀U, hφ₀0, hw⟩

theorem map_intU {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) : (intU a w).map (cLoc w) = GlobalTheory.LFun.KGL w (n := a) := by
  refine le_antisymm ?_ (KGL_le_map hw)
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_intU.1 hx).2 w (not_apart_self w)

theorem open_compact_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) {L : Subgroup (UA E a)} (hL : L ≤ intU a w)
    (ho : IsOpen ((L.subgroupOf (locU a w)) : Set (locU a w))) :
    IsOpen ((L.map (cLoc w) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) ∧
      IsCompact ((L.map (cLoc w) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hle := hL.trans (intU_le_locU w)
  rw [map_eq_image hle e he]
  refine ⟨e.toHomeomorph.isOpenMap _ ho, IsCompact.image ?_ e.continuous⟩
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  convert isCompact_of_le hL ho (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1 using 1
  exact coe_subgroupOf_image hle

theorem exists_level {T : Finset (HeightOneSpectrum (𝓞 E))} {U : Submodule ℂ (UA E a → ℂ)} (hU : AutOffT T U)
    {w₀ v' : HeightOneSpectrum (𝓞 E)} (hw₀ : IsSplitAt w₀) (hv' : IsSplitAt v') (hap : Apart v' w₀) :
    ∃ (K : Subgroup (UA E a)) (Kw : Levels E a) (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))),
      IsLevelAway w₀ K ∧ IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) ∧
      (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K ⊓ Kv.comap (cLoc v'), RU E a x φ = φ) ∧ Kw v' = GlobalTheory.LFun.KGL v' (n := a) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w (n := a)) ∧
      (∀ w, ¬ IsSplitAt w → w ∉ T → ∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) → x ∈ K) ∧
      ∀ w, IsSplitAt w → Apart w w₀ → ∀ x ∈ locU a w, x ∈ K ↔ cLoc w x ∈ Kw w := by
  classical
  obtain ⟨H, hleI, hopen, hfib, hfix, hint, hae⟩ := exists_locLev hU.1 w₀
  have hle : ∀ w, H w ≤ locU a w := fun w => (hleI w).trans (intU_le_locU w)
  have hcpt : ∀ w, IsCompact (H w : Set (UA E a)) := fun w => isCompact_of_le (hleI w) (hopen w) (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1
  obtain ⟨φ, hφU, hφ0, hφH⟩ := GlobalTheory.T.exists_vector_fixed_by_product_localLevels E a U hU.1 w₀ H hle hfib hcpt
    (hae.mono fun w hw x hx => by rw [hw] at hx; exact (mem_intU.1 hx).2 w (not_apart_self w)) hopen (fun w _ => hfix w)
  have hφ := GlobalTheory.T.fixed_of_fixed_by_local_levels E a w₀ H hle hfib hcpt hopen hae φ (hU.1.aut φ hφU) hφH
  let H' : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a) := fun w => if Apart w v' then H w else intU a w
  have h1 : ∀ w, Apart w v' → H' w = H w := fun w h => if_pos h
  have h2 : ∀ w, ¬ Apart w v' → H' w = intU a w := fun w h => if_neg h
  have hleI' : ∀ w, H' w ≤ intU a w := fun w => by
    by_cases h : Apart w v'
    · rw [h1 w h]; exact hleI w
    · rw [h2 w h]
  have hle' : ∀ w, H' w ≤ locU a w := fun w => (hleI' w).trans (intU_le_locU w)
  have hopen' : ∀ w, IsOpen (((H' w).subgroupOf (locU a w)) : Set (locU a w)) := fun w => by
    by_cases h : Apart w v'
    · rw [h1 w h]; exact hopen w
    · rw [h2 w h]; exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).2
  have hcpt' : ∀ w, IsCompact (H' w : Set (UA E a)) := fun w => isCompact_of_le (hleI' w) (hopen' w) (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1
  have hfib' : ∀ w u, ¬ Apart w u → H' w = H' u := fun w u h => by
    by_cases hw : Apart w v'
    · have hu : Apart u v' := by
        by_contra hu
        exact not_apart_trans h hu hw
      rw [h1 w hw, h1 u hu, hfib w u h]
    · rw [h2 w hw, h2 u (not_apart_trans (not_apart_symm h) hw), intU_congr h]
  have hint' : ∀ w, H w = intU a w → H' w = intU a w := fun w h => by
    by_cases hw : Apart w v'
    · rw [h1 w hw, h]
    · exact h2 w hw
  refine ⟨levelOf a w₀ H', fun w => (H' w).map (cLoc w), (H v').map (cLoc v'),
    GlobalTheory.T.isLevelAway_definiteUnitaryLevelFromLocalLevels E a w₀ H' hle' hfib' hcpt' hopen' (hae.mono hint'), (open_compact_map hv' (hleI v') (hopen v')).1,
    ⟨φ, hφU, hφ0, fun x hx => hφ x ?_⟩, ?_, fun w hw _ => open_compact_map hw (hleI' w) (hopen' w), ?_, ?_, ?_⟩
  · obtain ⟨hx1, y, hy, e⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨g1, g2, g3⟩ := mem_levelOf.1 hx1
    refine mem_levelOf.2 ⟨g1, g2, fun w hw => ?_⟩
    by_cases h : Apart w v'
    · rw [← h1 w h]; exact g3 w hw
    · refine ⟨y, by rw [hfib w v' h]; exact hy, ?_⟩
      have := GlobalTheory.Cong.LevelExt.one_of_cLoc hv' (y * x⁻¹) (by rw [map_mul, map_inv, e, mul_inv_cancel]) w h
      rwa [map_mul, map_inv, mul_inv_eq_one] at this
  · show (H' v').map (cLoc v') = _
    rw [h2 v' (not_apart_self v'), map_intU hv']
  · rintro w hw - ⟨B, σ, hσ, hB⟩
    obtain ⟨φ', hφ'U, hφ'0, hφ'⟩ := fix_of_fixed hw σ hσ hB.1
    show (H' w).map (cLoc w) = _
    rw [hint' w (hint w ⟨φ', hφ'U, hφ'0, fun x hx =>
      hφ' x (mem_intU.1 hx).1 ((mem_intU.1 hx).2 w (not_apart_self w))⟩), map_intU hw]
  · intro w hw hT x hx hk
    have hap : Apart w w₀ := by
      unfold Apart
      intro h
      have := eq_of_not_apart_of_not_split hw (show ¬ Apart w₀ w from fun h' => h' h.symm)
      exact hw (this ▸ hw₀)
    obtain ⟨φ', hφ'U, hφ'0, hφ'⟩ := hU.2 w hw hT
    exact (mem_levelOf_iff_of_locU hle' hfib' hap hx).2 (by
      rw [hint' w (hint w ⟨φ', hφ'U, hφ'0, fun y hy =>
        hφ' y (mem_intU.1 hy).1 ((mem_intU.1 hy).2 w (not_apart_self w))⟩)]
      exact mem_intU_of hx hk)
  · intro w hw hap x hx
    rw [mem_levelOf_iff_of_locU hle' hfib' hap hx]
    show x ∈ H' w ↔ cLoc w x ∈ (H' w).map (cLoc w)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, e⟩
      rw [← eq_of_cLoc_eq (hle' w hy) hx e]
      exact hy

theorem isLevelAway_inf {w₀ : HeightOneSpectrum (𝓞 E)} {K : Subgroup (UA E a)} (hK : IsLevelAway w₀ K)
    (v' : HeightOneSpectrum (𝓞 E)) {Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))}
    (ho : IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E)))) : IsLevelAway w₀ (K ⊓ Kv.comap (cLoc v')) := by
  have hc := GlobalTheory.BCT.GlobLev.continuous_cLoc (n := a) v'
  obtain ⟨N, hN, h1, hNK⟩ := hK.isOpen
  refine ⟨inf_le_left.trans hK.fin, fun x hx => hK.one x hx.1, hK.compact.inter_right ((Kv.isClosed_of_isOpen ho).preimage hc),
    N ∩ cLoc v' ⁻¹' Kv, hN.inter (ho.preimage hc), ⟨h1, by simp⟩, fun x hx hf h => ⟨hNK x hx.1 hf h, hx.2⟩⟩

end UpperTheory.Gal.Int.Cong

end
end

