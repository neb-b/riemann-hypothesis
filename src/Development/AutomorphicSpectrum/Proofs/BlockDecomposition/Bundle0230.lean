module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtNil

theorem isNilpotent_of_fg_of_le {B : Type} [CommRing B] {J J' : Ideal B}
    (hJ : ∀ x ∈ J, IsNilpotent x) (hfg : J'.FG) (hle : J' ≤ J) : IsNilpotent J' :=
  (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 fun x hx => mem_nilradical.2 (hJ x (hle hx))

theorem exists_lift {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallySmooth P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (g : E →ₐ[P] B ⧸ J) :
    ∃ h : E →ₐ[P] B, (Ideal.Quotient.mkₐ P J).comp h = g := by
  obtain ⟨n, π, hπ, hK⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  choose b hb using fun i => Ideal.Quotient.mk_surjective (g (π (MvPolynomial.X i)))
  let φ : MvPolynomial (Fin n) P →ₐ[P] B := MvPolynomial.aeval b
  have hφ : (Ideal.Quotient.mkₐ P J).comp φ = g.comp π :=
    MvPolynomial.algHom_ext fun i => by simp [φ, hb]
  have hφ' : ∀ p, Ideal.Quotient.mk J (φ p) = g (π p) := fun p => DFunLike.congr_fun hφ p
  let J' : Ideal B := (RingHom.ker π.toRingHom).map φ.toRingHom
  have hle : J' ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun p hp => ?_
    have hp0 : π p = 0 := hp
    refine Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    change Ideal.Quotient.mk J (φ p) = 0
    rw [hφ', hp0, map_zero]
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ (hK.map _) hle
  have hkill : ∀ a ∈ RingHom.ker π, ((Ideal.Quotient.mkₐ P J').comp φ) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem φ.toRingHom ha)
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let g' : E →ₐ[P] B ⧸ J' :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill).comp
      e.symm.toAlgHom
  have hg' : ∀ p, g' (π p) = Ideal.Quotient.mk J' (φ p) := fun p => by
    have : e.symm (π p) = Ideal.Quotient.mk (RingHom.ker π) p := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hπ p).symm
    change Ideal.Quotient.liftₐ (RingHom.ker π) ((Ideal.Quotient.mkₐ P J').comp φ) hkill
      (e.symm (π p)) = _
    rw [this]
    rfl
  refine ⟨Algebra.FormallySmooth.lift J' hnil g', AlgHom.ext fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hπ x
  have h1 := Algebra.FormallySmooth.mk_lift J' hnil g' (π p)
  rw [hg', Ideal.Quotient.eq] at h1
  change Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J' hnil g' (π p)) = g (π p)
  rw [← hφ', Ideal.Quotient.eq]
  exact hle h1

theorem lift_unique {P E B : Type} [CommRing P] [CommRing E] [CommRing B] [Algebra P E]
    [Algebra P B] [Algebra.FormallyUnramified P E] [Algebra.FinitePresentation P E] (J : Ideal B)
    (hJ : ∀ x ∈ J, IsNilpotent x) (h₁ h₂ : E →ₐ[P] B)
    (H : ∀ x, Ideal.Quotient.mk J (h₁ x) = Ideal.Quotient.mk J (h₂ x)) : h₁ = h₂ := by
  obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := P) (A := E)
  let d : Fin n → B := fun i => h₁ (π (MvPolynomial.X i)) - h₂ (π (MvPolynomial.X i))
  let J' : Ideal B := Ideal.span (Set.range d)
  have hfg : J'.FG := Submodule.fg_span (Set.finite_range d)
  have hle : J' ≤ J := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.Quotient.eq.1 (H _)
  have hnil : IsNilpotent J' := isNilpotent_of_fg_of_le hJ hfg hle
  have hc : (Ideal.Quotient.mkₐ P J').comp (h₁.comp π) =
      (Ideal.Quotient.mkₐ P J').comp (h₂.comp π) :=
    MvPolynomial.algHom_ext fun i =>
      Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
  refine Algebra.FormallyUnramified.ext J' hnil fun x => ?_
  obtain ⟨p, rfl⟩ := hπ x
  exact DFunLike.congr_fun hc p

end GlobalTheory.CompanionTheory.EtNil

theorem GlobalTheory.CompanionTheory.EtNil.etLift_of_nil : ∀ {B : Type} [CommRing B] (J : Ideal B),
    (∀ x ∈ J, IsNilpotent x) → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g hg
  letI := ψ.toAlgebra
  letI := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let gA : E →ₐ[P] B ⧸ J :=
    { g with commutes' := fun p => DFunLike.congr_fun hg p }
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.EtNil.exists_lift J hJ gA
  have hh' : ∀ x, Ideal.Quotient.mk J (h x) = g x := fun x => DFunLike.congr_fun hh x
  refine ⟨h.toRingHom, ⟨RingHom.ext fun p => h.commutes p, RingHom.ext hh'⟩, ?_⟩
  rintro h' ⟨h1, h2⟩
  let hA : E →ₐ[P] B := { h' with commutes' := fun p => DFunLike.congr_fun h1 p }
  have : hA = h := GlobalTheory.CompanionTheory.EtNil.lift_unique J hJ hA h fun x => by
    change Ideal.Quotient.mk J (h' x) = _
    rw [hh']
    exact DFunLike.congr_fun h2 x
  exact RingHom.ext fun x => DFunLike.congr_fun this x
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueLiftOfNilpotent
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

theorem existsUnique_lift_of_nilpotent {P E C D : Type} [CommRing P] [CommRing E] [CommRing C] [CommRing D]
    (ψ : P →+* E) (hψ : ψ.Etale) (u : C →+* D) (hu : Function.Surjective u)
    (hn : IsNilpotent (RingHom.ker u)) (f : P →+* C) (g : E →+* D) (h : g.comp ψ = u.comp f) :
    ∃! l : E →+* C, l.comp ψ = f ∧ u.comp l = g := by
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P C := f.toAlgebra
  letI : Algebra P D := (u.comp f).toAlgebra
  haveI : Algebra.Etale P E := hψ
  let uA : C →ₐ[P] D := { u with commutes' := fun _ => rfl }
  let gA : E →ₐ[P] D := { g with commutes' := fun r => congrArg (fun t : P →+* D => t r) h }
  have hn₁ : IsNilpotent (RingHom.ker (uA : C →+* D)) := hn
  have hn₂ : IsNilpotent (RingHom.ker uA) := hn
  let lA : E →ₐ[P] C := Algebra.FormallySmooth.liftOfSurjective gA uA hu hn₁
  have hl : ∀ x, u (lA x) = g x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply gA uA hu hn₂ x
  refine ⟨(lA : E →+* C), ⟨RingHom.ext fun r => lA.commutes r, RingHom.ext hl⟩, ?_⟩
  rintro l' ⟨h1, h2⟩
  let lA' : E →ₐ[P] C := { l' with commutes' := fun r => congrArg (fun t : P →+* C => t r) h1 }
  have : lA' = lA := Algebra.FormallyUnramified.ext' u hn lA' lA fun x => by
    rw [hl]; exact congrArg (fun t : E →+* D => t x) h2
  exact congrArg (fun t : E →ₐ[P] C => (t : E →+* C)) this

variable {B : Type} [CommRing B] (J : Ideal B)

abbrev toBase (n : ℕ) : B ⧸ J ^ (n + 1) →+* B ⧸ J :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero n))

theorem isNilpotent_ker_toBase (n : ℕ) : IsNilpotent (RingHom.ker (toBase J n)) := by
  refine ⟨n + 1, ?_⟩
  have hk : RingHom.ker (toBase J n) = J.map (Ideal.Quotient.mk (J ^ (n + 1))) := by
    rw [Ideal.Quotient.factor_ker]
  rw [hk, ← Ideal.map_pow]
  simp

theorem existsUnique_level {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E) (hψ : ψ.Etale)
    (f : P →+* B) (g : E →+* B ⧸ J) (h : g.comp ψ = (Ideal.Quotient.mk J).comp f) (n : ℕ) :
    ∃! l : E →+* B ⧸ J ^ (n + 1), l.comp ψ = (Ideal.Quotient.mk _).comp f ∧ (toBase J n).comp l = g :=
  existsUnique_lift_of_nilpotent ψ hψ (toBase J n) (Ideal.Quotient.factor_surjective _)
    (isNilpotent_ker_toBase J n) _ g h

theorem iInf_pow_eq_bot (hJ : IsAdicComplete J B) : ⨅ i : ℕ, J ^ i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  refine (Ideal.mem_bot).2 (IsHausdorff.haus hJ.toIsHausdorff x fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact (Ideal.mem_iInf.1 hx) n

end GlobalTheory.CompanionTheory.EtaleLift


open GlobalTheory.CompanionTheory.EtaleLift in
theorem GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete :
    ∀ {B : Type} [CommRing B] (J : Ideal B), IsAdicComplete J B → EtLift J := by
  intro B _ J hJ P E _ _ ψ hψ f g h
  haveI := hJ
  choose l hl hu using existsUnique_level J ψ hψ f g h
  have hcomp : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J (Nat.succ_le_succ hle)).comp (l n) = l m := by
    intro m n hle
    refine (hu m _ ⟨?_, ?_⟩).symm ▸ rfl
    · rw [RingHom.comp_assoc, (hl n).1]
      rfl
    · rw [← (hl n).2, ← RingHom.comp_assoc]
      congr 1
      exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let F : (n : ℕ) → E →+* B ⧸ J ^ n := fun n => (Ideal.Quotient.factorPow J (Nat.le_succ n)).comp (l n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (F n) = F m := by
    intro m n hle
    simp only [F]
    rw [← hcomp hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  let H : E →+* B := IsAdicComplete.liftRingHom J F hF
  have hH : ∀ n x, Ideal.Quotient.mk (J ^ n) (H x) = F n x := fun n x =>
    IsAdicComplete.mk_liftRingHom J F hF n x
  have h1 : H.comp ψ = f := by
    ext p
    rw [← sub_eq_zero]
    refine IsHausdorff.haus hJ.toIsHausdorff _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      RingHom.comp_apply, hH, sub_eq_zero]
    have := congrArg (fun t : P →+* B ⧸ J ^ (n + 1) => Ideal.Quotient.factorPow J (Nat.le_succ n) (t p)) (hl n).1
    exact this
  have h2 : (Ideal.Quotient.mk J).comp H = g := by
    ext x
    have e1 : (toBase J 0).comp (Ideal.Quotient.factorPow J (Nat.le_succ 1)) = toBase J 1 :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    have e2 : Ideal.Quotient.mk J (H x) = toBase J 0 (F 1 x) := by
      rw [← hH 1 x]
      rfl
    rw [RingHom.comp_apply, e2, ← (hl 1).2, ← e1]
    rfl
  refine ⟨H, ⟨h1, h2⟩, ?_⟩
  rintro H' ⟨h1', h2'⟩
  letI : Algebra P E := ψ.toAlgebra
  letI : Algebra P B := f.toAlgebra
  haveI : Algebra.Etale P E := hψ
  let A : E →ₐ[P] B := { H with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1 }
  let A' : E →ₐ[P] B := { H' with commutes' := fun r => congrArg (fun t : P →+* B => t r) h1' }
  have : A' = A := Algebra.FormallyUnramified.ext_of_iInf J (iInf_pow_eq_bot J hJ) fun x => by
    exact (congrArg (fun t : E →+* B ⧸ J => t x) h2').trans (congrArg (fun t : E →+* B ⧸ J => t x) h2).symm
  exact congrArg (fun t : E →ₐ[P] B => (t : E →+* B)) this
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendedDividedPowers
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDMap

variable {B : Type} [CommRing B] {J : Ideal B}

theorem fil_anti (δ : DividedPowers J) {m n : ℕ} (h : m ≤ n) : fil δ n ≤ fil δ m := by
  refine Ideal.span_mono ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact ⟨l, h1, h.trans h2, rfl⟩

theorem fil_zero_top (δ : DividedPowers J) : fil δ 0 = ⊤ := by
  refine (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], ?_, ?_, ?_⟩) <;> simp

theorem dpow_mem_fil (δ : DividedPowers J) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ fil δ n := by
  refine Ideal.subset_span ⟨[(n, x)], ?_, ?_, ?_⟩ <;> simp [hx]

theorem fil_mul_le (δ : DividedPowers J) (m n : ℕ) : fil δ m * fil δ n ≤ fil δ (m + n) := by
  rw [fil, fil, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ⟨l, h1, h2, rfl⟩, b, ⟨l', h1', h2', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h1 p hp
    · exact h1' p hp
  · simpa using Nat.add_le_add h2 h2'
  · simp

theorem map_fil_le' {C : Type} [CommRing C] {J' : Ideal C} (δ : DividedPowers J) (δ' : DividedPowers J')
    (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) : (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

theorem fil_le_map {C : Type} [CommRing C] (δ : DividedPowers J) (f : B →+* C)
    (δ' : DividedPowers (J.map f)) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    fil δ' N ≤ (fil δ N).map f := by
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (fil_mul_le δ m n)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (dpow_mem_fil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (fil_anti δ h2) (hprod l h1)

theorem extended_dividedPowers : ∀ {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} (δ : DividedPowers J) (φ : B →+* B') (δ' : DividedPowers (J.map φ)), IsDPMorphism δ δ' φ → (∀ r, fil δ' r = (fil δ r).map φ) ∧ ∀ {B'' : Type} [CommRing B''] {J'' : Ideal B''} (δ'' : DividedPowers J'') (ψ : B' →+* B''), IsDPMorphism δ δ'' (ψ.comp φ) → IsDPMorphism δ' δ'' ψ := by
  intro B B' _ _ J δ φ δ' hφ
  refine ⟨fun r ↦ le_antisymm (fil_le_map δ φ δ' hφ r) (map_fil_le' δ δ' φ hφ r), ?_⟩
  intro B'' _ J'' δ'' ψ hψ
  refine IsDPMorphism.on_span δ' δ'' (S := φ '' (J : Set B)) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hψ.ideal_comp (Ideal.mem_map_of_mem (ψ.comp φ) ha)
  · rintro n _ ⟨a, ha, rfl⟩
    have h1 := hφ.dpow_comp (n := n) a ha
    have h2 := hψ.dpow_comp (n := n) a ha
    rw [h1]
    exact h2.symm

end GlobalTheory.CompanionTheory.PDMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowEqZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PerfectWittMaps

theorem isAdicComplete_of_pow_eq_zero (p : ℕ) {B : Type} [CommRing B] {n : ℕ} (hn : (p : B) ^ n = 0) :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  have hI : (Ideal.span {(p : B)}) ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, hn]; simp
  have hz0 : ∀ x y : B, x ≡ y [SMOD ((Ideal.span {(p : B)}) ^ n • ⊤ : Submodule B B)] → x = y := by
    intro x y h
    rw [hI] at h
    simpa [SModEq.bot] using h
  refine { haus' := fun x h => hz0 _ _ (h n), prec' := fun f h => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hmn
  · exact h hmn
  · rw [hz0 _ _ (h hmn)]

theorem exists_pow_pow_eq (p : ℕ) {A : Type} [CommRing A] (h : Function.Bijective fun x : A => x ^ p)
    (k : ℕ) (a : A) : ∃ b : A, b ^ p ^ k = a := by
  induction k generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := h.2 a
    obtain ⟨b, hb⟩ := ih c
    refine ⟨b, ?_⟩
    rw [pow_succ, pow_mul, hb]
    exact hc

theorem exists_lift (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] [IsAdicComplete (Ideal.span {(p : B)}) B] (J : Ideal B)
    (hpJ : (p : B) ∈ J) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) (g : A →+* B ⧸ J) :
    ∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a := by
  let φ : B ⧸ J →+* ModP B p := Ideal.Quotient.lift J
    ((frobenius (ModP B p) p).comp (Ideal.Quotient.mk _)) (by
      intro x hx
      rw [RingHom.comp_apply, frobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hJ x hx)
  let σ : A →+* A := ((frobeniusEquiv A p).symm : A ≃+* A)
  let g₁ : A →+* ModP B p := φ.comp (g.comp σ)
  let G : A →+* PreTilt B p := Perfection.lift p A (ModP B p) g₁
  have hle : Ideal.span {(p : B)} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hpJ
  let res : ModP B p →+* B ⧸ J := Ideal.Quotient.factor hle
  have hres : ∀ u : B, Ideal.Quotient.mk J u = res (Ideal.Quotient.mk _ u) := fun u => rfl
  have hφ : ∀ y : B ⧸ J, res (φ y) = y ^ p := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : φ (Ideal.Quotient.mk J b) = Ideal.Quotient.mk _ (b ^ p) := by
      simp [φ, frobenius_def]
    rw [this, ← hres, map_pow]
  refine ⟨(WittVector.fontaineTheta B p).comp (WittVector.map G), fun a => ?_⟩
  have h1 : (WittVector.fontaineTheta B p).comp (WittVector.map G) (WittVector.teichmuller p a)
      = (G a).untilt := by
    rw [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]
  have h3 : PreTilt.coeff 0 (G a) = g₁ a := rfl
  rw [h1, hres, PreTilt.mk_untilt_eq_coeff_zero, h3]
  change res (φ (g (σ a))) = g a
  rw [hφ, ← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p A p a

theorem lift_unique (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] [CharP A p]
    [PerfectRing A p] [Fact ¬IsUnit (p : B)] (J : Ideal B) (n : ℕ) (hbij : Function.Bijective fun x : A => x ^ p)
    (hn : (p : B) ^ n = 0) (hJ : ∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)})
    (f f' : WittVector p A →+* B)
    (h : ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) =
      Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) : f = f' := by
  refine WittVector.eq_of_apply_teichmuller_eq f f' ⟨n, hn⟩ fun a => ?_
  obtain ⟨b, rfl⟩ := exists_pow_pow_eq p hbij (n + 1) a
  rw [map_pow, map_pow, map_pow]
  set u := f (WittVector.teichmuller p b)
  set v := f' (WittVector.teichmuller p b)
  have huv : u - v ∈ J := Ideal.Quotient.eq.1 (h b)
  have h1 : (p : B) ∣ u ^ p - v ^ p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow,
      ← sub_pow_char, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ _ huv
  have h2 := dvd_sub_pow_of_dvd_sub h1 n
  have h0 : (p : B) ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [h0, zero_dvd_iff, sub_eq_zero, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
  exact h2

theorem wittVector_lift : ∀ (p : ℕ) [Fact p.Prime] {A B : Type} [CommRing A] [CommRing B] (J : Ideal B) (n : ℕ), D.Pf p A → (p : B) ^ n = 0 → (p : B) ∈ J → (∀ x ∈ J, x ^ p ∈ Ideal.span {(p : B)}) → ∀ g : A →+* B ⧸ J, (∃ f : WittVector p A →+* B, ∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = g a) ∧ ∀ f f' : WittVector p A →+* B, (∀ a, Ideal.Quotient.mk J (f (WittVector.teichmuller p a)) = Ideal.Quotient.mk J (f' (WittVector.teichmuller p a))) → f = f' := by
  intro p _ A B _ _ J n hA hn hpJ hJ g
  by_cases hB : Subsingleton B
  · have hQ : Subsingleton (B ⧸ J) := (Ideal.Quotient.mk_surjective (I := J)).subsingleton
    refine ⟨⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
               map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun a => Subsingleton.elim _ _⟩,
      fun f f' _ => RingHom.ext fun x => Subsingleton.elim _ _⟩
  · rw [not_subsingleton_iff_nontrivial] at hB
    have hu : ¬IsUnit (p : B) := IsNilpotent.not_isUnit ⟨n, hn⟩
    haveI : Fact ¬IsUnit (p : B) := ⟨hu⟩
    haveI := isAdicComplete_of_pow_eq_zero p hn
    have hAn : Nontrivial A := by
      by_contra hA'
      rw [not_nontrivial_iff_subsingleton] at hA'
      have h1 : (1 : B) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_one, ← map_one g, Subsingleton.elim (1 : A) 0, map_zero]
      have h2 := hJ 1 h1
      rw [one_pow, Ideal.mem_span_singleton] at h2
      exact hu (isUnit_of_dvd_one h2)
    haveI : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hA.char
    haveI : PerfectRing A p := ⟨hA.bij⟩
    exact ⟨exists_lift p J hpJ hJ g, fun f f' h => lift_unique p J n hA.bij hn hJ f f' h⟩

end GlobalTheory.CompanionTheory.PerfectWittMaps
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubThickOnto
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickSub

theorem subThick_onto {O : Type} [CommRing O] {F : Fn O} (V : F.Sub) (b : Base) (ht : b.t = 1)
    (κ : O →+* b.R ⧸ b.I) : Onto (subThick V b ht κ) fun T => V.In T.y.1.2 := by
  refine ⟨⟨fun {T T'} f => ⟨{
      φ := f.φ, u := f.u, comm := f.comm, dp := f.dp, hle := f.hle,
      pt := Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) f.pt)
        (Subtype.ext (congrArg (fun z => z.1.2) f.pt))),
      hx := fun j => j.elim, hs := f.hs, hv := fun j => j.elim }, rfl⟩⟩,
    ⟨fun {T T'} f g h => Thick.Hom.ext (congrArg (fun m => m.φ) h) (funext fun j => j.elim)⟩,
    fun T => T.y.1.2.2, fun T h => ?_⟩
  refine ⟨{ B := T.B, i := T.i, J := T.J, δ := T.δ, adm := T.adm, compat := T.compat, α := (),
            y := ⟨(T.y.1.1, ⟨T.y.1.2, h⟩), T.y.2⟩, inα := trivial, w := T.w, x := T.x, v := T.v, s := T.s,
            hx := fun j => j.elim, hs := T.hs, hv := T.hv }, ⟨eqToIso rfl⟩⟩

end GlobalTheory.CompanionTheory.ThickSub
end

