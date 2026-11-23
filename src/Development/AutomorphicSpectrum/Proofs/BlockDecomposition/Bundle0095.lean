module

public import Mathlib
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanish
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspIff

def stdRadical (K : Type) [Field K] [Fintype K] [DecidableEq K] (d a : ℕ) : Subgroup (GL (Fin d) K) :=
  have hmul : ∀ u v : GL (Fin d) K,
      (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      (∀ i j : Fin d, (v : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      ∀ i j : Fin d, ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
    intro u v hu hv i j
    by_cases hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr hij
    left
    rw [Units.val_mul, Matrix.mul_apply]
    by_cases hi : (i : ℕ) < a
    · have hk : ∀ k, (v : Matrix (Fin d) (Fin d) K) k j = if k = j then 1 else 0 :=
        fun k => (hv k j).resolve_right (by omega)
      simp only [hk]
      simpa using (hu i j).resolve_right hij
    · have hk : ∀ k, (u : Matrix (Fin d) (Fin d) K) i k = if i = k then 1 else 0 :=
        fun k => (hu i k).resolve_right (by omega)
      simp only [hk]
      simpa using (hv i j).resolve_right hij
  have hone : ∀ i j : Fin d, ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := fun i j => Or.inl (by simp [Matrix.one_apply])
  { carrier := {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ))}
    one_mem' := hone
    mul_mem' := fun {u v} hu hv => hmul u v hu hv
    inv_mem' := by
      intro u hu
      have hpow : ∀ n : ℕ, ∀ i j : Fin d, ((u ^ n : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
          (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hu
      have hinv : u⁻¹ = u ^ (orderOf u - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
      show ∀ i j : Fin d, ((u⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = _ ∨ _
      rw [hinv]
      exact hpow _ }

theorem mem_stdRadical {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} {u : GL (Fin d) K} :
    u ∈ stdRadical K d a ↔ ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := Iff.rfl

theorem pm_conj {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (g : GL ι K) : pm (K := K) σ * g * (pm (K := K) σ)⁻¹ = glEquiv K σ g := by
  have hp : ∀ i j, (pm (K := K) σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
    intro i j
    show (Equiv.toPEquiv σ⁻¹).toMatrix i j = _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    exact if_congr Equiv.Perm.inv_eq_iff_eq rfl rfl
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hg : ∀ x : GL ι K, ((glEquiv K σ x : GL ι K) : Matrix ι ι K) = (x : Matrix ι ι K).submatrix σ.symm σ.symm :=
    fun _ => rfl
  simp only [Units.val_mul, Matrix.mul_apply, hp, hg, Matrix.submatrix_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm i) (fun x _ hx => if_neg (fun h => hx (by simp [h]))) (by simp)]
  simp

theorem eq_zero_of_sum_char {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) [DecidablePred (· ∈ U)]
    (h : (∑ u : G, if u ∈ U then ρ.character u else 0) = 0) (v : V) (hv : ∀ u ∈ U, ρ u v = v) : v = 0 := by
  have hc : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have h1 := Representation.card_inv_mul_sum_char_eq_finrank (ρ.comp U.subtype : Representation ℂ U V)
  have hs : (∑ u : G, if u ∈ U then ρ.character u else 0) =
      ∑ g : U, Representation.character (ρ.comp U.subtype : Representation ℂ U V) g := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun g => ρ.character g)
  rw [hs] at h
  rw [h, mul_zero] at h1
  have h2 : Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ)]
    exact h1.symm
  have hm : v ∈ Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) := by
    rw [Representation.mem_invariants]
    exact fun u => hv u.1 u.2
  rw [h2] at hm
  simpa using hm

theorem isCuspidal_of_sum_char : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  classical
  intro K _ _ _ d τ h s b hb hs v hv
  let c0 : Fin s := ⟨0, by omega⟩
  let c1 : Fin s := ⟨1, by omega⟩
  have hc : c0 ≠ c1 := by simp [c0, c1, Fin.ext_iff]
  obtain ⟨i0, hi0⟩ := hb c0
  obtain ⟨i1, hi1⟩ := hb c1
  set a := Fintype.card {i // b i = c0} with ha
  have ha0 : 0 < a := Fintype.card_pos_iff.2 ⟨⟨i0, hi0⟩⟩
  have had : a < d := by
    have := Fintype.card_subtype_lt (p := fun i => b i = c0) (x := i1) (by rw [hi1]; exact hc.symm)
    simpa using this
  have hcard : Fintype.card {i // b i = c0} = Fintype.card {i : Fin d // (i : ℕ) < a} := by
    rw [← ha]
    exact (Fintype.card_fin a).symm.trans (Fintype.card_congr
      { toFun := fun k => ⟨⟨k, by omega⟩, k.2⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  let e := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm (Fin d) := e.extendSubtype
  have hσ : ∀ i, (σ i : ℕ) < a ↔ b i = c0 := by
    intro i
    by_cases hi : b i = c0
    · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
    · exact ⟨fun h' => absurd h' (e.extendSubtype_not_mem i hi), fun h' => absurd h' hi⟩
  have hfix : ∀ w : τ, (∀ u ∈ stdRadical K d a, τ.ρ u w = w) → w = 0 := by
    refine eq_zero_of_sum_char τ.ρ (stdRadical K d a) ?_
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (h a ha0 had)
    by_cases hu : u ∈ stdRadical K d a
    · rw [if_pos hu, if_pos (mem_stdRadical.1 hu)]; rfl
    · rw [if_neg hu, if_neg (fun h' => hu (mem_stdRadical.2 h'))]

  have hent : ∀ (x : GL (Fin d) K) (i j : Fin d),
      ((pm (K := K) σ * x * (pm (K := K) σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) (σ j) =
        (x : Matrix (Fin d) (Fin d) K) i j := by
    intro x i j
    rw [pm_conj]
    show (x : Matrix (Fin d) (Fin d) K) (σ.symm (σ i)) (σ.symm (σ j)) = _
    simp
  have key : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a → ∀ i j,
      (x : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ (b i = c0 ∧ b j ≠ c0) := by
    intro x hx i j
    have := hx (σ i) (σ j)
    rw [hent] at this
    rcases this with h1 | ⟨h1, h2⟩
    · left; simpa [σ.injective.eq_iff] using h1
    · right
      refine ⟨(hσ i).1 h1, fun h3 => ?_⟩
      have := (hσ j).2 h3
      omega
  have hut : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a →
      IsBlockUT K b (x : Matrix (Fin d) (Fin d) K) := by
    intro x hx i j hij
    rcases key x hx i j with h1 | ⟨h1, -⟩
    · have : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
      simpa [this] using h1
    · rw [h1] at hij
      exact absurd hij (by simp [c0, Fin.lt_def])
  have hun : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a → x ∈ unip K b := by
    intro x hx
    refine ⟨⟨hut x hx, hut x⁻¹ ?_⟩, ?_⟩
    · have : pm (K := K) σ * x⁻¹ * (pm (K := K) σ)⁻¹ = (pm (K := K) σ * x * (pm (K := K) σ)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
    · intro i j hij
      rcases key x hx i j with h1 | ⟨h1, h2⟩
      · exact h1
      · exact absurd (hij ▸ h1) h2
  have hw := hfix (τ.ρ (pm (K := K) σ) v) (by
    intro u hu
    have hx : (pm (K := K) σ)⁻¹ * u * pm (K := K) σ ∈ unip K b := by
      apply hun
      have : pm (K := K) σ * ((pm (K := K) σ)⁻¹ * u * pm (K := K) σ) * (pm (K := K) σ)⁻¹ = u := by group
      rw [this]
      exact hu
    have hh : u * pm (K := K) σ = pm (K := K) σ * ((pm (K := K) σ)⁻¹ * u * pm (K := K) σ) := by group
    rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, hv _ hx])
  have h3 := congrArg (τ.ρ (pm (K := K) σ)⁻¹) hw
  simpa [← Module.End.mul_apply, ← map_mul] using h3

end GlobalTheory.CompanionTheory.TyFin.CuspIff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleSurjectiveLocalSectionStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_surjective_local_section : ∀ {S : Type} [CommRing S],
    Aic (S := S) → Loc (S := S) →
    ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f →
    ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨B, i, hi, z, hz⟩ := Y.exists_Spec_apply_eq y
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S B := φ.hom.toAlgebra
  have : Algebra.Etale S B := RingHom.etale_algebraMap.1 hφe
  let Q : Ideal B := z.asIdeal
  have hQ : Q.IsPrime := z.2
  have hQm : Q.comap (algebraMap S B) = m := by
    have hx : (Spec.map φ) z = x := by rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal hx
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  let q := Q.map (algebraMap B Bg)
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hq : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : q.comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hqm : q.comap (algebraMap S Bg) = m := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap, hQm]
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := Bg)
  have hroot_of_mem (F : Polynomial S) (hF : F.Monic) (hmem : Polynomial.aeval P.x F ∈ q) :
      ∃ b : S, F.IsRoot b ∧ P.x - algebraMap S Bg b ∈ q := by
    have : Nontrivial S := nontrivial_of_ne 0 1 fun h =>
      hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))
    induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
    | ind n ih =>
      by_cases hn : n = 0
      · have h1 := Polynomial.eq_one_of_monic_natDegree_zero hF (hd.trans hn)
        rw [h1, map_one] at hmem
        exact (hq.ne_top ((Ideal.eq_top_iff_one q).2 hmem)).elim
      obtain ⟨b, hb⟩ := hA F hF (by omega)
      let G := F /ₘ (Polynomial.X - Polynomial.C b)
      have hFG : (Polynomial.X - Polynomial.C b) * G = F :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.2 hb
      have hG : G.Monic := (Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C b))
        (hFG.symm ▸ hF)
      have hdeg := (Polynomial.monic_X_sub_C b).natDegree_mul hG
      rw [hFG, Polynomial.natDegree_X_sub_C, hd] at hdeg
      rw [← hFG, map_mul] at hmem
      rcases hq.mem_or_mem hmem with hbq | hGq
      · exact ⟨b, hb, by simpa using hbq⟩
      · obtain ⟨c, hc, hcq⟩ := ih G.natDegree (by omega) G hG hGq rfl
        exact ⟨c, by rw [← hFG, Polynomial.IsRoot, Polynomial.eval_mul, hc, mul_zero], hcq⟩
  obtain ⟨b, hb, hbq⟩ := hroot_of_mem P.f P.monic_f (P.hasMap.1.symm ▸ q.zero_mem)
  let c : S := Polynomial.eval b P.g
  have hcm : c ∉ m := by
    rw [← hqm]
    intro hcq
    have hdvd : P.x - algebraMap S Bg b ∣ Polynomial.aeval P.x P.g - algebraMap S Bg c := by
      have h := Polynomial.sub_dvd_eval_sub P.x (algebraMap S Bg b) (P.g.map (algebraMap S Bg))
      rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at h
    have hgq : Polynomial.aeval P.x P.g ∈ q := by
      simpa using q.add_mem (Ideal.mem_of_dvd q hdvd hbq) (show algebraMap S Bg c ∈ q from hcq)
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q hgq P.hasMap.2)
  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hcm
  obtain ⟨e, he, hec, he1⟩ := hL (a * c)
  have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
  have he1m : 1 - e ∈ m := by
    rw [h1ac] at he1
    exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
  have hem : e ∉ m := by
    intro hem
    have h1 : (1 : S) ∈ m := by simpa using m.add_mem hem he1m
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
  have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
    have hmul : algebraMap S (Localization.Away e) e =
        algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
      rw [← map_mul, ← hr]; ring_nf
    rw [hmul] at heu
    exact isUnit_of_mul_isUnit_right heu
  have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hb.eq_zero, map_zero]
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hcu
  let ψ := ((P.P.lift _ hmap).comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom S B Bg)
  refine ⟨e, he, hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductConvergenceBound
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.SumDev

theorem sum_prod_le {ι X : Type*} (D : Finset ι) (B : Finset X) (e : ι → X → ℝ) (P : ι → X → Prop)
    (a b c : ι → ℝ) (w C' : ℝ) (hw : 0 ≤ w)
    (ha : ∀ v ∈ D, 0 ≤ a v) (hb : ∀ v ∈ D, 0 ≤ b v) (hbc : ∀ v ∈ D, b v * c v = a v)
    (he0 : ∀ v ∈ D, ∀ x ∈ B, 0 ≤ e v x)
    (he : ∀ v ∈ D, ∀ x ∈ B, e v x ≤ a v + if P v x then b v else 0)
    (hcount : ∀ t ⊆ D, w * ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) ≤ C' * ∏ v ∈ t, c v) :
    w * ∑ x ∈ B, ∏ v ∈ D, e v x ≤ C' * ∏ v ∈ D, (2 * a v) := by
  have hx : ∀ x ∈ B, ∏ v ∈ D, e v x ≤
      ∑ t ∈ D.powerset, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v := by
    intro x hxB
    calc ∏ v ∈ D, e v x ≤ ∏ v ∈ D, ((if P v x then b v else 0) + a v) := by
          refine Finset.prod_le_prod₀ (fun v hv => he0 v hv x hxB) (fun v hv => ?_)
          rw [add_comm]
          exact he v hv x hxB
      _ = ∑ t ∈ D.powerset, (∏ v ∈ t, (if P v x then b v else 0)) * ∏ v ∈ D \ t, a v :=
          Finset.prod_add _ _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.prod_ite_zero]
  have ht : ∀ t ∈ D.powerset,
      w * ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v ≤ C' * ∏ v ∈ D, a v := by
    intro t htD
    rw [Finset.mem_powerset] at htD
    have hA : 0 ≤ ∏ v ∈ D \ t, a v := Finset.prod_nonneg fun v hv => ha v (Finset.sdiff_subset hv)
    have hB : 0 ≤ ∏ v ∈ t, b v := Finset.prod_nonneg fun v hv => hb v (htD hv)
    have hsum : ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v
        = ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    have hprod : (∏ v ∈ t, b v) * ∏ v ∈ t, c v = ∏ v ∈ t, a v := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v hv => hbc v (htD hv)
    rw [hsum]
    calc w * (((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v))
        = (w * ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ)) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) := by
          ring
      _ ≤ (C' * ∏ v ∈ t, c v) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) :=
          mul_le_mul_of_nonneg_right (hcount t htD) (mul_nonneg hB hA)
      _ = C' * ((∏ v ∈ D \ t, a v) * ((∏ v ∈ t, b v) * ∏ v ∈ t, c v)) := by ring
      _ = C' * ∏ v ∈ D, a v := by rw [hprod, Finset.prod_sdiff htD]
  calc w * ∑ x ∈ B, ∏ v ∈ D, e v x
      ≤ w * ∑ x ∈ B, ∑ t ∈ D.powerset, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx) hw
    _ = ∑ t ∈ D.powerset, w * ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ t ∈ D.powerset, C' * ∏ v ∈ D, a v := Finset.sum_le_sum ht
    _ = C' * ∏ v ∈ D, (2 * a v) := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.prod_mul_distrib, Finset.prod_const, nsmul_eq_mul]
        push_cast
        ring

variable {F : Type} [Field F] [NumberField F]

theorem mem_asIdeal (v : HeightOneSpectrum (𝓞 F)) {x : F}
    (hxi : algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F)
    (h1 : Valued.v (algebraMap F (Fv F v) x) ≠ 1) {N : ℕ} {y : 𝓞 F} (hy : (y : F) = (N : F) * x) :
    y ∈ v.asIdeal := by
  have hval : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hle : v.valuation F x ≤ 1 := by
    rw [← hval]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hxi
  have hlt : v.valuation F x < 1 := lt_of_le_of_ne hle (by rw [← hval]; exact h1)
  refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v y).mp ?_
  have hN : v.valuation F (N : F) ≤ 1 := by
    have h := HeightOneSpectrum.valuation_le_one (K := F) v (N : 𝓞 F)
    exact_mod_cast h
  have hNx : v.valuation F ((N : F) * x) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hN) hlt
  convert hNx using 2

theorem mem_prod_asIdeal (t : Finset (HeightOneSpectrum (𝓞 F))) {y : 𝓞 F} (h : ∀ v ∈ t, y ∈ v.asIdeal) :
    y ∈ ∏ v ∈ t, v.asIdeal := by
  revert h
  refine Finset.induction_on t (fun _ => by simp) ?_
  intro v t hv ih h
  rw [Finset.prod_insert hv]
  have hcop : IsCoprime v.asIdeal (∏ w ∈ t, w.asIdeal) := by
    refine IsCoprime.prod_right fun w hw => ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal fun hvw => hv ?_
    rw [HeightOneSpectrum.ext hvw]
    exact hw
  rw [Ideal.mul_eq_inf_of_isCoprime hcop]
  exact Ideal.mem_inf.mpr ⟨h v (Finset.mem_insert_self v t), ih fun w hw => h w (Finset.mem_insert_of_mem hw)⟩

theorem sum_bounded_prod : CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (K : Set (Ainf F)), IsCompact K → ∀ N : ℕ, 0 < N → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), 0 ≤ C → (∀ v, v ∉ S → (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧ ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ δ : ℝ, 0 < δ → ∀ D : Finset (HeightOneSpectrum (𝓞 F)), Disjoint D S → ∀ B : Finset F, (∀ x ∈ B, x ≠ 0 ∧ x ∈ IntOut S ∧ (∃ y : 𝓞 F, (y : F) = (N : F) * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K) → δ ^ Module.finrank ℚ F * ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| ≤ C' * ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
  intro hCB F _ _ hF θ hθ K hK N hN
  obtain ⟨C0, hC0⟩ := hCB F hF θ hθ K hK N hN
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro S C g hC hg δ hδ D hDS B hB
  have hnorm : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := fun v =>
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have hcnt : ∀ t ⊆ D, δ ^ Module.finrank ℚ F *
      ((B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1).card : ℝ) ≤
        max C0 0 * ∏ v ∈ t, (1 / (Ideal.absNorm v.asIdeal : ℝ)) := by
    intro t ht
    have hI0 : (∏ v ∈ t, v.asIdeal) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
      intro v _
      rw [Ideal.zero_eq_bot]
      exact v.ne_bot
    obtain ⟨hfin, hle⟩ := hC0 δ hδ (∏ v ∈ t, v.asIdeal) hI0
    have hsub : (↑(B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1) : Set F) ⊆
        {x | x ≠ 0 ∧ (∃ y ∈ ∏ v ∈ t, v.asIdeal, (y : F) = (N : F) * x) ∧
          θ δ * algebraMap F (Ainf F) x ∈ K} := by
      intro x hx
      rw [Finset.coe_filter] at hx
      obtain ⟨hxB, hxP⟩ := hx
      obtain ⟨hx0, hxS, ⟨y, hy⟩, hxK⟩ := hB x hxB
      refine ⟨hx0, ⟨y, mem_prod_asIdeal t fun v hv => ?_, hy⟩, hxK⟩
      have hvS : v ∉ S := Finset.disjoint_left.mp hDS (ht hv)
      exact mem_asIdeal v (hxS v hvS) (hxP v hv) hy
    have hcard : ((B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1).card : ℝ) ≤
        ({x | x ≠ 0 ∧ (∃ y ∈ ∏ v ∈ t, v.asIdeal, (y : F) = (N : F) * x) ∧
          θ δ * algebraMap F (Ainf F) x ∈ K}.ncard : ℝ) := by
      rw [← Set.ncard_coe_finset]
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    have hnormI : (Ideal.absNorm (∏ v ∈ t, v.asIdeal) : ℝ) = ∏ v ∈ t, (Ideal.absNorm v.asIdeal : ℝ) := by
      rw [map_prod, Nat.cast_prod]
    calc δ ^ Module.finrank ℚ F *
          ((B.filter fun x => ∀ v ∈ t, Valued.v (algebraMap F (Fv F v) x) ≠ 1).card : ℝ)
        ≤ δ ^ Module.finrank ℚ F * ({x | x ≠ 0 ∧ (∃ y ∈ ∏ v ∈ t, v.asIdeal, (y : F) = (N : F) * x) ∧
          θ δ * algebraMap F (Ainf F) x ∈ K}.ncard : ℝ) :=
          mul_le_mul_of_nonneg_left hcard (pow_nonneg hδ.le _)
      _ ≤ C0 / (Ideal.absNorm (∏ v ∈ t, v.asIdeal) : ℝ) := hle
      _ ≤ max C0 0 / (Ideal.absNorm (∏ v ∈ t, v.asIdeal) : ℝ) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      _ = max C0 0 * ∏ v ∈ t, (1 / (Ideal.absNorm v.asIdeal : ℝ)) := by
          rw [hnormI, Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div]
  have key := sum_prod_le D B (fun v x => |g v (algebraMap F (Fv F v) x) - 1|)
    (fun v x => Valued.v (algebraMap F (Fv F v) x) ≠ 1)
    (fun v => C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) (fun v => C / (Ideal.absNorm v.asIdeal : ℝ))
    (fun v => 1 / (Ideal.absNorm v.asIdeal : ℝ)) (δ ^ Module.finrank ℚ F) (max C0 0)
    (pow_nonneg hδ.le _)
    (fun v _ => div_nonneg hC (pow_nonneg (hnorm v).le _))
    (fun v _ => div_nonneg hC (hnorm v).le)
    (fun v _ => by ring)
    (fun v _ x _ => abs_nonneg _)
    (fun v hv x hx => by
      have hvS : v ∉ S := Finset.disjoint_left.mp hDS hv
      obtain ⟨hx0, hxS, -, -⟩ := hB x hx
      have hint : algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := hxS v hvS
      have h2 : 0 ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := div_nonneg hC (pow_nonneg (hnorm v).le _)
      split_ifs with hP
      · have h1 := (hg v hvS).1 _ hint ((map_ne_zero _).mpr hx0)
        linarith
      · rw [add_zero]
        exact (hg v hvS).2 _ (not_not.mp hP))
    (fun t ht => by
      convert hcnt t ht)
  refine le_of_le_of_eq key ?_
  refine congrArg _ (Finset.prod_congr rfl fun v _ => ?_)
  exact (mul_div_assoc _ _ _).symm

end GlobalTheory.CompanionTheory.Mass.SumDev

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProductDifferenceBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem abs_prod_sub_prod_le_sum_powerset (V : Type) (a : V → ℝ) (A U : Finset V) (hAU : A ⊆ U) :
    |∏ v ∈ U, a v - ∏ v ∈ A, a v| ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by
  have hexp : ∀ S : Finset V, ∏ v ∈ S, a v = ∑ D ∈ S.powerset, ∏ v ∈ D, (a v - 1) := by
    intro S
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hfilt : U.powerset.filter (fun D => D ⊆ A) = A.powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hAU, h⟩⟩
  rw [hexp U, hexp A, ← Finset.sum_filter_add_sum_filter_not U.powerset (fun D => D ⊆ A), hfilt,
    add_sub_cancel_left]
  calc |∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, (a v - 1)|
      ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, |∏ v ∈ D, (a v - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by simp_rw [Finset.abs_prod]

end GlobalTheory.CompanionTheory.Mass.MeanV
end

