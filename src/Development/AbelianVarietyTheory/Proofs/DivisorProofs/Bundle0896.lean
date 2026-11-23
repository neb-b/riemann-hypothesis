module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwist
section
open Polynomial

namespace GlobalTheory.FrobOrbit

theorem card_le_of_pow_eq_self {k : Type} [Field k] {n : ℕ} (hn : 1 < n) (Z : Finset k)
    (hZ : ∀ x ∈ Z, x ^ n = x) : Z.card ≤ n := by
  have hd := Polynomial.natDegree_X_pow_sub_X (R := k) hn
  have hne : (X ^ n - X : k[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hd
    omega
  have := card_le_degree_of_subset_roots (p := (X ^ n - X : k[X])) (Z := Z) (by
    intro x hx
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hZ x hx, sub_self])
  rwa [hd] at this

theorem field_case (K k : Type) [Field K] [Fintype K] [Field k] (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] (f : K →+* k) (h : ℕ) (hh : 0 < h) (hc : Fintype.card K = p ^ h) :
    (∀ a, f a ^ p ^ h = f a) ∧ (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
    (∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t) ∧
    ∀ g : K →+* k, ∃ s : ℕ, s < h ∧ ∀ a, g a = f a ^ p ^ s := by
  classical
  have h1 : 1 < p := hp.out.one_lt
  have hfix : ∀ a, f a ^ p ^ h = f a := fun a => by
    rw [← map_pow, ← hc, FiniteField.pow_card]
  have himg : (Finset.univ.image f).card = p ^ h := by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, hc]
  have hlt : ∀ s t : ℕ, s < t → t < h → ¬ ∀ a, f a ^ p ^ s = f a ^ p ^ t := by
    intro s t hst hth H
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hst
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ (d + 1))
      (Nat.one_lt_pow (Nat.succ_ne_zero d) h1) (Finset.univ.image f) (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        apply (iterateFrobenius k p s).injective
        rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, H a]
        congr 2
        omega)
    rw [himg] at hle
    have := (Nat.pow_le_pow_iff_right h1).1 hle
    omega
  have hinj : ∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t := by
    intro s t hs ht H
    rcases lt_trichotomy s t with hst | hst | hst
    · exact absurd H (hlt s t hst ht)
    · exact hst
    · exact absurd (fun a => (H a).symm) (hlt t s hst hs)
  refine ⟨hfix, ?_, hinj, ?_⟩
  · intro x hx
    by_contra hne
    have hx' : x ∉ Finset.univ.image f := by
      intro hm
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hm
      exact hne ⟨a, ha⟩
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ h)
      (Nat.one_lt_pow hh.ne' h1) (insert x (Finset.univ.image f)) (by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hx
        · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
          exact hfix a)
    rw [Finset.card_insert_of_notMem hx', himg] at hle
    omega
  · intro g
    haveI : CharP K p := RingHom.charP f f.injective p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    let toAlg : (K →+* k) → (K →ₐ[ZMod p] k) := fun φ =>
      { φ with
        commutes' := fun r =>
          congrArg (fun ψ : ZMod p →+* k => ψ r)
            (Subsingleton.elim (φ.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) k)) }
    have toAlg_apply : ∀ φ a, toAlg φ a = φ a := fun _ _ => rfl
    have hrank : Module.finrank (ZMod p) K = h := by
      have := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
      rw [ZMod.card, hc] at this
      exact (Nat.pow_right_injective h1 this).symm
    let F : Fin h → (K →ₐ[ZMod p] k) := fun s => toAlg ((iterateFrobenius k p s.val).comp f)
    have hF : ∀ s a, F s a = f a ^ p ^ s.val := fun s a => rfl
    have hFinj : Function.Injective F := by
      intro s t hst
      apply Fin.ext
      apply hinj _ _ s.2 t.2
      intro a
      rw [← hF, ← hF, hst]
    have hbij := hFinj.bijective_of_nat_card_le (by
      have := card_algHom_le_finrank (ZMod p) K k
      rw [hrank] at this
      simpa using this)
    obtain ⟨s, hs⟩ := hbij.2 (toAlg g)
    exact ⟨s.val, s.2, fun a => by rw [← hF, hs, toAlg_apply]⟩

theorem ringHom_ker_eq_iff_frobenius_twist :
    ∀ (R k : Type) [CommRing R] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : R →+* k) (h : ℕ),
      0 < h → Nat.card (R ⧸ RingHom.ker f) = p ^ h →
      (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
      ∃ F : ZMod h → (R →+* k), (∀ s a, F s a = f a ^ p ^ s.val) ∧
        (∀ s a, F (s + 1) a = F s a ^ p) ∧ Function.Injective F ∧
        ∀ g : R →+* k, RingHom.ker g = RingHom.ker f ↔ ∃ s, F s = g := by
  intro R k _ _ p hp _ f h hh hc
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI : Finite (R ⧸ RingHom.ker f) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : (RingHom.ker f).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isDomain_to_isField _)
  letI : Field (R ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Fintype (R ⧸ RingHom.ker f) := Fintype.ofFinite _
  obtain ⟨hfix, hsurj, hinj, hall⟩ := field_case (R ⧸ RingHom.ker f) k p (RingHom.kerLift f) h hh
    (by rw [← Nat.card_eq_fintype_card, hc])
  have hmk : ∀ a, RingHom.kerLift f (Ideal.Quotient.mk _ a) = f a := RingHom.kerLift_mk f
  have hfix' : ∀ a, f a ^ p ^ h = f a := fun a => by
    have := hfix (Ideal.Quotient.mk _ a)
    exact this
  have hmod : ∀ (a : R) (n : ℕ), f a ^ p ^ (n % h) = f a ^ p ^ n := by
    intro a n
    have hm : ∀ m : ℕ, f a ^ p ^ (h * m) = f a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfix']
    conv_rhs => rw [← Nat.div_add_mod n h, pow_add, pow_mul, hm]
  refine ⟨fun x hx => ?_, fun s => (iterateFrobenius k p s.val).comp f, fun s a => rfl,
    fun s a => ?_, fun s t hst => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := hsurj x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, ha⟩
  · change f a ^ p ^ (s + 1).val = (f a ^ p ^ s.val) ^ p
    have hv : (s + 1).val = (s.val + 1) % h := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rw [hv, hmod, pow_succ, pow_mul]
  · apply ZMod.val_injective h
    apply hinj _ _ (ZMod.val_lt s) (ZMod.val_lt t)
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact congrArg (fun φ : R →+* k => φ b) hst
  · obtain ⟨s, hs, hgs⟩ := hall (Ideal.Quotient.lift (RingHom.ker f) g
      (fun a ha => by rw [← hg] at ha; exact ha))
    refine ⟨(s : ZMod h), RingHom.ext fun a => ?_⟩
    change f a ^ p ^ ((s : ZMod h)).val = g a
    rw [ZMod.val_cast_of_lt hs]
    exact (hgs (Ideal.Quotient.mk _ a)).symm
  · rintro ⟨s, rfl⟩
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change f a ^ p ^ s.val = 0 ↔ f a = 0
    exact pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)

end GlobalTheory.FrobOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

theorem rosati_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → ∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left) := by
  intro p _ D R _ b M S s o A' _ _ act' ψ G hA' hψ hG hact m P' hP' hIso r₁ r₂ c
  haveI := act'.hom c
  haveI := act'.hom (D.star c).unop
  have e₁ : sq2 ψ ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left ≫ sq2 ψ := by
    simp only [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have e₂ : sq2 ψ ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left ≫ sq2 ψ := by
    simp only [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have u₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      𝟙 _ ≫ (lift (1 : A' ⟶ A') (𝟙 A')).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have u₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ (lift (fst A' A' ≫ act'.act c) (snd A' A')).left =
      (act'.act c).left ≫ (lift (𝟙 A') (1 : A' ⟶ A')).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      (act'.act (D.star c).unop).left ≫ (lift (1 : A' ⟶ A') (𝟙 A')).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left =
      𝟙 _ ≫ (lift (𝟙 A') (1 : A' ⟶ A')).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp

  have hL := o.isLB
  have hX₁ : ((P'.pull (lift (fst A' A' ≫ act'.act c) (snd A' A')).left).pull (sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hP' _) _
  have hX₂ : ((P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left).pull (sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hP' _) _
  have hL₁ : (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have hL₂ : (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have I₁ : LBIso (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m)
      ((P'.pull (lift (fst A' A' ≫ act'.act c) (snd A' A')).left).pull (sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin m) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => sq2 ψ) (fun _ => sq2 ψ) (fun _ => 1) _ (fun _ => e₁)) hIso
  have I₂ : LBIso (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m)
      ((P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c).unop)).left).pull (sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin m) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => sq2 ψ) (fun _ => sq2 ψ) (fun _ => 1) _ (fun _ => e₂)) hIso
  have Rm : LBIso (lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left) m)
      (lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left) m) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (o.rosati c) _ _
  have hsq := LBIso.trans hX₁ hL₁ hX₂ I₁.symm (LBIso.trans hL₁ hL₂ hX₂ Rm I₂)
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  exact _root_.GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt S o.A A' G ψ o.ab hA' hψ hG _ _ (pull_isLB hP' _) (pull_isLB hP' _)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₁)) t₁ ht₁)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₂)) t₂ ht₂)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₁)) t₁ ht₁)
    (gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₂)) t₂ ht₂)
    hsq

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem finiteQ (G : HTGroup p) : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

theorem norm_sim (P : Pair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  haveI := finiteQ G
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G), P'.γ = P.γ → P'.c = P.c ∨ P'.c = -P.c := by
  intro p _ G P P' hγ
  haveI := finiteQ G
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

end GlobalTheory.LKMid.Pair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

open GlobalTheory.LFun GlobalTheory.PRep

theorem satEig_map_mul (q m : ℕ) (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    satEig q m (B.map (· * z)) j = (z : ℂ) ^ j * satEig q m B j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [satEig, Multiset.map_map, Function.comp_def, Units.val_mul]
  rw [mul_left_comm, h]
  simp only [mul_comm]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m : ℕ}

theorem isUnitAt_det_of_mem {k : GL (Fin m) (w.adicCompletion E)} (hk : k ∈ KGL w (n := m)) :
    Formalism.L2.Host.IsUnitAt w (Matrix.GeneralLinearGroup.det k) := by
  obtain ⟨k, rfl⟩ := hk
  have e : ((Matrix.GeneralLinearGroup.det (bc (Ov E w).subtype k) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((Matrix.GeneralLinearGroup.det k : (Ov E w)ˣ) : Ov E w) :=
    ((Ov E w).subtype.map_det k.val).symm
  change Valued.v _ = 1
  rw [e]
  generalize Matrix.GeneralLinearGroup.det k = u
  have h1 : Valued.v ((u : Ov E w) : w.adicCompletion E) ≤ 1 := (u : Ov E w).2
  have h2 : Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) ≤ 1 := ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2
  have h3 : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  exact le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)

theorem det_diagJ {L : Type} [Field L] (ϖ : L) {j : ℕ} (hj : j ≤ m) : (diagJ m ϖ j).det = ϖ ^ j := by
  rw [diagJ, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Fin.card_filter_val_lt, min_eq_right hj]

theorem loc_det_of_Tj {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ)
    {j : ℕ} (hj : j ≤ m) {g : GL (Fin m) (w.adicCompletion E)} (hg : Tj ℂ m (Ov E w) ϖ j g ≠ 0) :
    χ.loc w (Matrix.GeneralLinearGroup.det g) = χ.val w ^ j := by
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hg
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ h0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change g.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, det_diagJ ϖ hj]
    simp
  rw [e2, map_mul, map_mul, hχ _ (isUnitAt_det_of_mem ha), hχ _ (isUnitAt_det_of_mem hb), map_pow,
    χ.val_eq hχ (Units.mk0 ϖ h0) hϖ, one_mul, mul_one]

theorem hasSatGL_of_twist {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V}
    {ρ' : Representation ℂ (GL (Fin m) (w.adicCompletion E)) W} {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w)
    (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g x, ρ' g (T x) = ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (ρ g x))
    {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' (B.map (· * χ.val w)) := by
  have hf : ∀ x, T x ∈ fixed ρ' (KGL w (n := m)) ↔ x ∈ fixed ρ (KGL w (n := m)) := fun x => by
    simp only [GlobalTheory.LGrp.mem_fixed]
    refine forall₂_congr fun k hk => ?_
    rw [hT, hχ _ (isUnitAt_det_of_mem hk), Units.val_one, one_smul, T.injective.eq_iff]
  constructor
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h.1
    exact (Submodule.ne_bot_iff _).2 ⟨T x, (hf x).2 hx, (map_ne_zero_iff T T.injective).2 h0⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx := h.2 x ((hf x).1 hy) ((map_ne_zero_iff T T.injective).1 h0)
    refine ⟨h0, hy, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
    rw [satEig_map_mul, mul_smul, ← map_smul T, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
    have e := T.toAddEquiv.map_finsum
      (fun c : _ ⧸ KGL w (n := m) => Tj ℂ m (Ov E w) ϖ j c.out • ρ c.out x)
    rw [show T _ = _ from e, smul_finsum]
    refine finsum_congr fun c => ?_
    by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
    · simp [hc]
    · rw [hT, loc_det_of_Tj hχ hϖ hj hc, smul_comm]
      simp

theorem hasSatGL_twist (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E m)
    (χ : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (hχ : χ.UnrAt w)
    (h : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) :
    GlobalTheory.LFun.HasSatGL w ((π.twist χ).locRep w) (B.map (· * χ.val w)) := by
  refine hasSatGL_of_twist hχ (π.toTwist χ) (fun g x => ?_) h
  rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
  rfl

end GlobalTheory.SphGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.CoeffCont

open MvPowerSeries

theorem coe_le_add {a b : WithTop ℝ} {x y : ℝ} (ha : (x : WithTop ℝ) ≤ a) (hb : (y : WithTop ℝ) ≤ b) :
    ((x + y : ℝ) : WithTop ℝ) ≤ a + b := by
  rw [WithTop.coe_add]; exact add_le_add ha hb

theorem poly_bound {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {κ : Type} (Q : MvPolynomial κ C) :
    ∃ K : ℝ, ∀ (N : ℝ) (s s' : κ → C), (∀ k, (0 : WithTop ℝ) ≤ v (s k)) → (∀ k, (0 : WithTop ℝ) ≤ v (s' k)) →
      (∀ k, ((N : ℝ) : WithTop ℝ) ≤ v (s k - s' k)) →
      ((N - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q - MvPolynomial.eval s' Q) ∧
      ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q) := by
  induction Q using MvPolynomial.induction_on
  · rename_i c
    by_cases ht : v c = ⊤
    · refine ⟨0, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ht, le_top, and_self]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
      refine ⟨-r, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ← hr, le_top, neg_neg, le_refl, and_self]
  · rename_i p q hp hq
    obtain ⟨K₁, h₁⟩ := hp
    obtain ⟨K₂, h₂⟩ := hq
    refine ⟨max K₁ K₂, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a₁, b₁⟩ := h₁ N s s' hs hs' hss
    obtain ⟨a₂, b₂⟩ := h₂ N s s' hs hs' hss
    rw [map_add (MvPolynomial.eval s), map_add (MvPolynomial.eval s')]
    constructor
    · have e : MvPolynomial.eval s p + MvPolynomial.eval s q - (MvPolynomial.eval s' p + MvPolynomial.eval s' q) =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) + (MvPolynomial.eval s q - MvPolynomial.eval s' q) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) a₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) a₂
    · refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) b₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) b₂
  · rename_i p k hp
    obtain ⟨K, h⟩ := hp
    refine ⟨K, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a, b⟩ := h N s s' hs hs' hss
    rw [map_mul (MvPolynomial.eval s), map_mul (MvPolynomial.eval s'), MvPolynomial.eval_X, MvPolynomial.eval_X]
    constructor
    · have e : MvPolynomial.eval s p * s k - MvPolynomial.eval s' p * s' k =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) * s k + MvPolynomial.eval s' p * (s k - s' k) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · rw [v.map_mul]
        have := coe_le_add (y := 0) a (hs k)
        rwa [add_zero] at this
      · rw [v.map_mul]
        have := coe_le_add (h N s' s' hs' hs' (fun k => by rw [sub_self, v.map_zero]; exact le_top)).2 (hss k)
        have e2 : (-K + N : ℝ) = N - K := by ring
        rw [e2] at this
        exact this
    · rw [v.map_mul]
      have := coe_le_add (y := 0) b (hs k)
      rwa [add_zero] at this

theorem coeff_subst_eq_eval {C : Type} [Field C] {τ σ ι : Type} [Fintype τ] [Fintype ι]
    (W : MvPowerSeries τ C) (g : ι → MvPowerSeries σ C) (hg : ∀ i, constantCoeff (g i) = 0) (α : σ →₀ ℕ) :
    ∃ Q : MvPolynomial (τ × ι) C, ∀ s : τ → ι → C,
      coeff α (subst (fun q => ∑ i, s q i • g i) W : MvPowerSeries σ C) =
        MvPolynomial.eval (fun x => s x.1 x.2) Q := by
  classical
  let G : ι → MvPowerSeries σ (MvPolynomial (τ × ι) C) := fun i => (g i).map MvPolynomial.C
  let a : τ → MvPowerSeries σ (MvPolynomial (τ × ι) C) :=
    fun q => ∑ i, (MvPolynomial.X (q, i) : MvPolynomial (τ × ι) C) • G i
  have hG : ∀ i, constantCoeff (G i) = 0 := fun i => by simp [G, hg]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun q => by simp [a, hG])
  refine ⟨coeff α (subst a (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)) :
    MvPowerSeries σ (MvPolynomial (τ × ι) C)), fun s => ?_⟩
  have h1 := congrArg (coeff α) (map_subst ha (h := MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))
    (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)))
  rw [coeff_map] at h1
  have hW : (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)).map
      (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2)) = W := by
    ext n; simp [coeff_map]
  have hA : (fun q => (a q).map (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))) =
      fun q => ∑ i, s q i • g i := by
    funext q; ext n; simp [a, G, coeff_map, map_sum]
  rw [h1, hW, hA]

end GlobalTheory.IsoTriv.CoeffCont

namespace GlobalTheory.IsoTriv

open MvPowerSeries

theorem contSt_holds : ContSt := by
  intro C _ v τ σ ι _ _ _ W g hg α
  obtain ⟨Q, hQ⟩ := CoeffCont.coeff_subst_eq_eval W g hg α
  obtain ⟨K, hK⟩ := CoeffCont.poly_bound v Q
  refine ⟨⌈K⌉₊, fun s s' hs hs' hss => ?_⟩
  rw [hQ, hQ]
  have h := (hK (⌈K⌉₊ : ℝ) (fun x => s x.1 x.2) (fun x => s' x.1 x.2) (fun x => hs _ _) (fun x => hs' _ _)
    (fun x => hss _ _)).1
  show (0 : WithTop ℝ) ≤ _
  refine le_trans ?_ h
  rw [← WithTop.coe_zero, WithTop.coe_le_coe]
  linarith [Nat.le_ceil K]

end GlobalTheory.IsoTriv
end
end

