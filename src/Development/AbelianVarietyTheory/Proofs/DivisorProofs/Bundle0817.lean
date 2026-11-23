module

public import Mathlib
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplit
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.HatLoc

variable {E : Type} [Field E] [NumberField E]

theorem finMult {R : Type} [CommRing R] [IsDedekindDomain R] {c : Ideal R} (hc : c ≠ ⊥) (v : HeightOneSpectrum R) :
    FiniteMultiplicity v.asIdeal c :=
  FiniteMultiplicity.of_prime_left v.prime hc

omit [NumberField E] in
theorem expIn_eq_zero {c : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} (h : ¬ v.asIdeal ∣ c) : expIn c v = 0 :=
  multiplicity_eq_zero_of_not_dvd h

theorem exists_global {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ v, LocIn (expIn c v) v z) :
    ∃ a : OF E, ∀ P : HeightOneSpectrum (𝓞 E),
      Valued.v (z P - iota a P) ≤ WithZero.exp (-(expIn c (P.under (OF E)) : ℤ)) := by
  classical
  choose b hb using hz
  have hfin := Ideal.finite_factors (R := OF E) hc
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset) (fun v => v.asIdeal) (expIn c)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => b v)
  refine ⟨a, fun P => ?_⟩
  have h1 : a - b (P.under (OF E)) ∈ (P.under (OF E)).asIdeal ^ expIn c (P.under (OF E)) := by
    by_cases h : (P.under (OF E)).asIdeal ∣ c
    · exact ha _ (hfin.mem_toFinset.2 h)
    · simp [expIn_eq_zero h]
  have h2 := val_iota_le_of_mem (over_under P) _ h1
  have h3 : z P - iota a P = (z P - iota (b (P.under (OF E))) P) - iota (a - b (P.under (OF E))) P := by
    rw [iota_sub, sub_coord]; ring
  rw [h3]
  exact Valuation.map_sub_le _ (hb _ P (over_under P)) h2

theorem multiplicity_map_le [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥)
    (hs : ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) (P : HeightOneSpectrum (𝓞 E)) :
    multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) ≤ expIn c (P.under (OF E)) := by
  set k := multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) with hk
  have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ k := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have h2 : (P.under (OF E)).asIdeal ∣ c :=
    Ideal.dvd_iff_le.2 (Ideal.map_le_iff_le_comap.1 (h1.trans (Ideal.pow_le_self hpos.ne')))
  refine (finMult hc _).le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 fun a ha => ?_)
  exact (((GlobalTheory.CMVal.Euler.SplitPlace.split_place E _ (hs _ h2)).2 P (over_under P)).2.1 a k).1 (h1 (Ideal.mem_map_of_mem _ ha))

theorem mem_hatO_of_locIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) →
      z ∈ hatO c := by
  intro E _ _ _ c hc hs z hz
  obtain ⟨a, ha⟩ := exists_global hc hz
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz _).val_le (over_under P))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hc' : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hc
  have hx : x - algebraMap (OF E) (𝓞 E) a ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [← Ideal.iInf_maxPowDividing_eq hc', Ideal.mem_iInf]
    intro P
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hc']
    refine Ideal.pow_le_pow_right (multiplicity_map_le hc hs P) ?_
    rw [← P.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E (x - algebraMap (OF E) (𝓞 E) a)) =
        (z - iota a) - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [map_sub, map_sub, hxy]
      change algebraMap E (Af E) (x : E) - iota a = _
      ring
    rw [h1, sub_coord, sub_coord, mul_coord]
    refine Valuation.map_sub_le _ (ha P) ?_
    rw [map_mul]
    exact (mul_le_mul' (val_iota_le_of_mem (over_under P) _
      (Ideal.le_of_dvd (pow_multiplicity_dvd _ _) (Ideal.absNorm_mem c))) (hy P)).trans_eq (mul_one _)
  rw [hxy]
  refine add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨a, _, hx, ?_⟩)) (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)
  rw [map_sub]
  change (x : E) = algebraMap (OF E) E a + ((x : E) - algebraMap (OF E) E a)
  ring

end GlobalTheory.CMVal.Euler.HatLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.OrthKer

theorem fibreDescent_transport' {X : Scheme.{0}} {m m' : X ⟶ X} (e : m = m')
    (P : (X ⟶ X) → Prop)
    (H : ∀ (V : X.Opens) (a : Γ(X, m' ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m' ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m' ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m'.app V).hom a' = a) :
    ∀ (V : X.Opens) (a : Γ(X, m ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m.app V).hom a' = a := by
  subst e; exact H


open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Chart in
theorem descends_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (hN : (N : K) ≠ 0)
    (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V))
    (ha : ∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤
      (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ
        ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V),
      ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) :
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a := by
  let A : Over (Spec (CommRingCat.of K)) := (Over.pullback f).obj G
  let ρ : ∀ (T : Over (Spec (CommRingCat.of K))) (t : T.left ⟶ S) (ht : T.hom ≫ f = t),
      (T ⟶ A) ≃* (Over.mk t ⟶ G) := fun T t ht => TorsionLift.ptsEquiv f G T t ht
  have hρ : ∀ T t ht x, (ρ T t ht x).left = x.left ≫ Limits.pullback.fst G.hom f :=
    fun T t ht x => TorsionLift.ptsEquiv_left f G T t ht x
  have hA : A.hom ≫ f = (G ⊗ Over.mk f).hom := Limits.pullback.condition.symm
  have hid : ρ A _ hA (𝟙 A) = fst G (Over.mk f) := Over.OverMorphism.ext (by
    rw [hρ]; exact Category.id_comp _)
  have ext : ∀ (u : A ⟶ A) (v : G ⊗ Over.mk f ⟶ G ⊗ Over.mk f),
      v ≫ fst _ _ = ρ A _ hA u → v ≫ snd _ _ = snd _ _ → v.left = u.left := by
    intro u v h1 h2
    apply Limits.pullback.hom_ext
    · exact (congrArg (·.left) h1).trans (hρ _ _ _ _)
    · exact (congrArg (·.left) h2).trans (Over.w u).symm
  have hm : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left = ((𝟙 A) ^ N : A ⟶ A).left := by
    refine ext _ _ ?_ (whiskerRight_snd _ _)
    rw [map_pow, hid, whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have hAb : IsAbelianScheme A := TLinPf.isAb_pullback f G hG
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, h3, h1, h2⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hAb hu
  refine fibreDescent_transport' hm (fun t => ∃ y : Over.mk f ⟶ G, y ^ N = 1 ∧
    t = (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) ?_ V a ?_
  · intro V a ha
    refine existsUnique_descend_of_torsion_invariant A N V a fun y hy => ?_
    refine ha _ ⟨ρ (𝟙_ _) f (Category.id_comp _) y, by rw [← map_pow, hy, map_one], ?_⟩
    refine (ext _ _ ?_ (lift_snd _ _)).symm
    rw [lift_fst, map_mul, hid, _root_.mul_comm]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hρ, hρ, Over.comp_left, Category.assoc]
    rfl
  · rintro _ ⟨y, hy, rfl⟩
    exact ha y hy

theorem mem_kernel_of_cubWeil_orthogonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) (p : Sp K ⟶ S) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ), (N : K) ≠ 0 → ∀ x : Over.mk p ⟶ B, x ^ N = 1 → (∀ y : Over.mk p ⟶ B, y ^ N = 1 → CubWeil c N x y 1) → Triv (translDiff B L.L x) := by
  intro K _ _ S t A _ _ hA L c n hn x hx hp
  let T : Over S := Over.mk t
  let m : A ⊗ T ⟶ A ⊗ T := ((𝟙 A) ^ n : A ⟶ A) ▷ T
  have m₁ : m ≫ fst A T = fst A T ^ n := by
    rw [whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have m₂ : m ≫ snd A T ≫ x = snd A T ≫ x := by rw [whiskerRight_snd_assoc]
  let ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left) :=
    ![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]
  obtain ⟨σ, hσ, hv⟩ := CubNondeg.exists_sigma c n (fst A T) (snd A T ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by
      funext k
      fin_cases k
      · show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left
        rw [MonObj.comp_mul, m₁, m₂]
      · exact congrArg (fun q => q.left) m₁
      · exact congrArg (fun q => q.left) m₂
      · exact congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))
  obtain ⟨u, hu⟩ := CubNondeg.descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1})
    (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by
      rw [← Over.comp_left]
      congr 1
      ext1
      · rw [Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one,
          _root_.mul_one]
      · simp [m])
    (fun V a ha => descends_fibre S A hA K t n hn V a (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ
    (fun y z J hJ => by
      have e₁ := hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ
      have e₂ := hv _ (𝟙 (A ⊗ T)) z J hJ
      rw [lift_fst, lift_snd_assoc] at e₁
      rw [Category.id_comp, Category.id_comp] at e₂
      have w := (hp y.1 y.2).comp (snd A T)
      have w' := w.2.2 z J hJ
      rw [map_one, map_one, _root_.one_mul] at w'
      exact e₁.trans ((CubNondeg.ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]
  let s : T ⊗ A ⟶ A ⊗ T := lift (snd T A) (fst T A)
  have s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left := by
    show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left
    rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]
  have s₁ : s.left ≫ ψ 1 = (snd T A).left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)
  have s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)
  have s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left :=
    congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB
    (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) *
        h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) *
        h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) =
        h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd T A).left ^ (-1 : ℤ)
      rw [s₀, s₁, s₂, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))
  exact ⟨w, hw⟩

end GlobalTheory.OrthKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffs
section
noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

variable {F : Type} [NormedField F]

namespace Red

theorem mul_mem_cell_iff {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)} {u : GL (Fin n) F}
    (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) : u * g ∈ cell z U ↔ g ∈ cell z U := by
  constructor
  · rintro ⟨v, hv, k, hk, e⟩
    refine ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, k, hk, ?_⟩
    have : g = u⁻¹ * (u * g) := by group
    rw [this, e]
    simp only [mul_assoc]
  · rintro ⟨v, hv, k, hk, rfl⟩
    exact ⟨u * v, mul_mem hu hv, k, hk, by simp only [mul_assoc]⟩

theorem cell_eq_of_mem {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (hg : g ∈ cell z (U : Set (GL (Fin n) F))) : cell g (U : Set (GL (Fin n) F)) = cell z U := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  ext x
  constructor
  · rintro ⟨u, hu, k', hk', rfl⟩
    exact ⟨u * v, mul_mem hu hv, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩
  · rintro ⟨u, hu, k', hk', rfl⟩
    refine ⟨u * v⁻¹, mul_mem hu (inv_mem hv), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
    group

theorem act_mul_left {ψ : AddChar F ℂ} {n : ℕ} (T : GL (Fin n) F →₀ ℂ) {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f)
    {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    act T f (u * g) = ψ (superDiag u) * act T f g := by
  unfold act Finsupp.sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u g k, hf u hu, mul_left_comm]

theorem indicator_cell_mul_left {ψ : AddChar F ℂ} {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f) {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    (cell z U).indicator f (u * g) = ψ (superDiag u) * (cell z U).indicator f g := by
  classical
  by_cases hg : g ∈ cell z U
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_cell_iff hu g).2 hg), hf u hu]
  · rw [Set.indicator_apply, Set.indicator_apply, if_neg hg, if_neg (fun h => hg ((mul_mem_cell_iff hu g).1 h)),
      mul_zero]

end Red

open Red

theorem cuts_mir_of_res : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  intro F _ _ _ ψ _ _ m H U hUc hUo z
  classical
  by_cases hz : ∃ h₀ : GL (Fin (m + 1)) F, cor h₀ ∈ cell z (U : Set (GL (Fin (m + 2)) F))
  swap
  · refine ⟨0, fun f _ _ p hp => ?_⟩
    rw [act_zero, Set.indicator_apply, if_neg]
    intro hpc
    obtain ⟨h, x, rfl⟩ := exists_mir hp
    rw [mir_eq, mul_mem_cell_iff (mir_mem_iff.2 (one_mem _))] at hpc
    exact hz ⟨h, hpc⟩
  obtain ⟨h₀, hh₀⟩ := hz
  have hzc : cell z (U : Set (GL (Fin (m + 2)) F)) = cell (cor h₀) U := (Red.cell_eq_of_mem hh₀).symm
  obtain ⟨B, hBc, _, hUB, hcell⟩ := GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff U hUc hUo
  let B' : Subgroup (GL (Fin (m + 1)) F) := U.comap cor
  have hB'o : IsOpen (B' : Set (GL (Fin (m + 1)) F)) := hUo.preimage continuous_cor
  have hB'B : B' ≤ B := fun b hb => hUB b hb
  have hB'c : IsCompact (B' : Set (GL (Fin (m + 1)) F)) :=
    hBc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hB'o) hB'B
  let L : Set (Fin (m + 1) → F) := {y | mir 1 y ∈ U}
  have hL : L ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    refine (hUo.preimage continuous_col).mem_nhds ?_
    show mir 1 0 ∈ U
    rw [mir_one]
    exact one_mem _
  obtain ⟨s, -, hsU, hsd⟩ := GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion B B' hBc hB'o hB'B h₀
  choose T hT using fun x : GL (Fin (m + 1)) F => H B' hB'c hB'o L hL x
  refine ⟨∑ x ∈ s, T x, fun f hf hfU => ?_⟩
  have hB'f : ∀ b ∈ B', ∀ g, f (g * cor b) = f g := fun b hb g => hfU _ hb g
  have hLf : ∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g := fun y hy g => hfU _ hy g
  have hcor : ∀ h, act (∑ x ∈ s, T x) f (cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (cor h) := by
    intro h
    rw [act_finset_sum]
    rw [Finset.sum_congr rfl fun x _ => hT x f hf hB'f hLf h]
    rw [← Finset.indicator_biUnion_apply s _ hsd, ← hsU, hzc]
    by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hcell h₀ h).2 hh)]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg hh, if_neg fun h' => hh ((hcell h₀ h).1 h')]
  intro p hp
  obtain ⟨h, x, rfl⟩ := exists_mir hp
  have hu : mir 1 x ∈ unipB F (Fin (m + 2)) := mir_mem_iff.2 (one_mem _)
  rw [mir_eq]
  show act _ f (mir 1 x * cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (mir 1 x * cor h)
  rw [act_mul_left _ hf hu, indicator_cell_mul_left hf hu, hcor]

end GlobalTheory.JSW.Cut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormDualWeylTensorEvaluationLeFibreNorm
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.TSup

theorem evalAt_intVec {n : ℕ} (la : Fin n → ℕ) (y : Matrix (Fin n) (Fin n) ℂ) (j : Idx la) :
    evalAt y (map (Int.castRingHom ℂ) (intVec la j)) =
      ∑ i, onMat la i j * evalAt y (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ) := by
  rw [← coe_basis]
  have h : basis la ℂ j = ∑ i, onMat la i j • (toSpace la).symm (onBasis la i) := by
    apply (toSpace la).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply, onMat, Matrix.of_apply]
    exact ((onBasis la).sum_repr _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, Submodule.coe_sum, map_sum]
  simp [Submodule.coe_smul, map_smul]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ}

theorem tval_eq_onb (la : ∀ t, Fin (N t) → ℕ) (z : TIdx la → ℂ) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) :
    tval la z y = ∑ J : TIdx la, ((kron fun t => onMat (la t)) *ᵥ z) J *
      ∏ t, evalAt (y t) (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) := by
  unfold tval
  simp_rw [evalAt_intVec, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul, Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  ring

theorem norm_sum_mul_le {ι : Type} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  calc ‖∑ i, a i * b i‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem mul_norm_tval_le_fibNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  intro T _ _ N la hla x X u s hs
  have h1 : tval la x (fun t => X t * (u t).1) =
      tval la ((kron fun t => rhoMat (la t) (X t)) *ᵥ x) (fun t => (u t).1) := by
    have h := _root_.GlobalTheory.DefPt.tval_translate T N la ℂ ℂ (RingHom.id ℂ) x X (fun t => (u t).1)
    simpa only [RingHom.id_apply, RingHom.coe_id, Matrix.map_id] using h
  have hk := (_root_.GlobalTheory.DefPt.kronFamily_mul_one_det T (fun t => Idx (la t)) ℂ (fun t => onMat (la t)) (fun t => rhoMat (la t) (X t))).1
  set E : TIdx la → ℂ := fun J => ∏ t, evalAt (u t).1
    (((toSpace (la t)).symm (onBasis (la t) (J t)) : nabla (la t) ℂ) : Pol (N t) ℂ) with hE
  have h2 : (s : ℂ) * tval la x (fun t => X t * (u t).1) = ∑ J, (fibY la s X *ᵥ x) J * E J := by
    rw [h1, tval_eq_onb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    have hsm : ∀ (M : Matrix (TIdx la) (TIdx la) ℂ) (v : TIdx la → ℂ), ((s : ℂ) • M) *ᵥ v = (s : ℂ) • (M *ᵥ v) := by
      intro M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [fibY, hsm, ← hk, ← Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : ∑ J, ‖E J‖ ^ 2 ≤ 1 := by
    have : ∑ J, ‖E J‖ ^ 2 = ∏ t, ∑ i, ‖evalAt (u t).1
        (((toSpace (la t)).symm (onBasis (la t) i) : nabla (la t) ℂ) : Pol (N t) ℂ)‖ ^ 2 := by
      rw [Fintype.prod_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      simp only [hE, norm_prod, Finset.prod_pow]
    rw [this]
    exact Finset.prod_le_one₀ (fun t _ => Finset.sum_nonneg fun _ _ => by positivity)
      (fun t _ => _root_.GlobalTheory.DualWeyl.EvBound.sum_sq_norm_evalAt_onBasis_le_one (N t) (la t) (hla t) (u t))
  have h4 : s * ‖tval la x (fun t => X t * (u t).1)‖ = ‖(s : ℂ) * tval la x (fun t => X t * (u t).1)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  rw [h4, h2]
  refine (norm_sum_mul_le _ _).trans ?_
  calc _ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_one]
        exact h3
    _ = _ := mul_one _

end GlobalTheory.TSup

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
section
open NumberField

noncomputable section

open scoped Classical

namespace GlobalTheory.RatPointSum

variable {F : Type} [Field F] [NumberField F]

theorem norm_mixedEmbedding_le_sum (x : F) : ‖mixedEmbedding F x‖ ≤ ∑ w : InfinitePlace F, w x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => AbsoluteValue.nonneg _ _)
    (Finset.mem_univ w)

theorem norm_mixedEmbedding_nat_mul_le {κ : Type} [Fintype κ] (M : ℕ) (ξ : κ → F) :
    ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ (M : ℝ) * ∑ i, ∑ w : InfinitePlace F, w (ξ i) := by
  have h0 : ∀ i, 0 ≤ ∑ w : InfinitePlace F, w (ξ i) := fun i => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [map_mul, map_natCast, ← nsmul_eq_mul]
  refine norm_nsmul_le.trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_mixedEmbedding_le_sum (ξ i)).trans ?_) (Nat.cast_nonneg M)
  exact Finset.single_le_sum (f := fun i => ∑ w : InfinitePlace F, w (ξ i)) (fun i _ => h0 i) (Finset.mem_univ i)

end GlobalTheory.RatPointSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneSplitQuaternionAlgebraStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_split | exact GlobalTheory.QSA.strongApprox_split | (intros; apply GlobalTheory.QSA.strongApprox_split <;> assumption)
end

