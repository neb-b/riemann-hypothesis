module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSameOr
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

private theorem conj_alt_bis {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) : IsCMField.complexConj E x = -x :=
  _root_.UpperTheory.Reformulated.B.CMConjNegOfSqEqNegPos.conj_alt_bis hd hx

private theorem adjoin_form {E : Type} [Field E] [NumberField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (y : E) (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ s t : ℚ, y = (s : E) + (t : E) * x :=
  _root_.UpperTheory.Reformulated.B.AdjoinForm.adjoin_form hd hx y hy

private theorem two_cases {R : Type} [CommRing R] (T : R → Prop) (hT : ∀ a b, T a → T b → T (a + b))
    (I J : Ideal R) (h : ∀ y, T y → y ∈ I ∨ y ∈ J) : (∀ y, T y → y ∈ I) ∨ (∀ y, T y → y ∈ J) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨a, ha, haI⟩, b, hb, hbJ⟩ := hcon
  have haJ : a ∈ J := (h a ha).resolve_left haI
  have hbI : b ∈ I := (h b hb).resolve_right hbJ
  rcases h (a + b) (hT a b ha hb) with h1 | h1
  · exact haI ((Submodule.add_mem_iff_left I hbI).mp h1)
  · exact hbJ ((Submodule.add_mem_iff_right J haJ).mp h1)

private theorem core {R : Type} [CommRing R] (c : R ≃+* R) (hcc : ∀ y, c (c y) = y) (K : R → Prop)
    (hKa : ∀ a b, K a → K b → K (a + b)) (hKc : ∀ y, K y → K (c y)) (W W' : Ideal R)
    (h1 : ∀ y, K y → y ∈ W → y ∈ W' ∨ c y ∈ W') (h2 : ∀ y, K y → y ∈ W' → y ∈ W ∨ c y ∈ W) :
    (∀ y, K y → (y ∈ W ↔ y ∈ W')) ∨ (∀ y, K y → (c y ∈ W ↔ y ∈ W')) := by
  have A := two_cases (fun y => K y ∧ y ∈ W') (fun a b ha hb => ⟨hKa a b ha.1 hb.1, W'.add_mem ha.2 hb.2⟩)
    W (W.comap (c : R →+* R)) (fun y hy => by simpa [Ideal.mem_comap] using h2 y hy.1 hy.2)
  have B := two_cases (fun y => K y ∧ y ∈ W) (fun a b ha hb => ⟨hKa a b ha.1 hb.1, W.add_mem ha.2 hb.2⟩)
    W' (W'.comap (c : R →+* R)) (fun y hy => by simpa [Ideal.mem_comap] using h1 y hy.1 hy.2)
  simp only [Ideal.mem_comap, RingHom.coe_coe] at A B
  rcases A with A | A <;> rcases B with B | B
  · exact Or.inl fun y hy => ⟨fun h => B y ⟨hy, h⟩, fun h => A y ⟨hy, h⟩⟩
  · refine Or.inl fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := A (c y) ⟨hKc y hy, B y ⟨hy, h⟩⟩
    have h4 := B (c y) ⟨hKc y hy, h3⟩
    rwa [hcc] at h4
  · refine Or.inr fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := B (c y) ⟨hKc y hy, h⟩
    have h4 := A (c y) ⟨hKc y hy, h3⟩
    rw [hcc] at h4
    exact B y ⟨hy, h4⟩
  · refine Or.inr fun y hy => ⟨fun h => ?_, fun h => A y ⟨hy, h⟩⟩
    have h3 := B (c y) ⟨hKc y hy, h⟩
    rwa [hcc] at h3

private theorem int_mem {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) {u u' : Ideal R} (hu : u ≠ ⊤)
    (hlu : (l : R) ∈ u) (hlu' : (l : R) ∈ u') {n : ℤ} (hn : (n : R) ∈ u) : (n : R) ∈ u' := by
  by_cases hd : (l : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hd
    push_cast
    exact u'.mul_mem_right _ hlu'
  · have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) n := (Prime.coprime_iff_not_dvd hp).mpr hd
    exfalso
    apply hu
    rw [Ideal.eq_top_iff_one]
    have : ((a * l + b * n : ℤ) : R) = 1 := by rw [hab]; simp
    rw [← this]
    push_cast
    exact u.add_mem (u.mul_mem_left _ hlu) (u.mul_mem_left _ hn)

private theorem norm_int {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (y y' : 𝓞 E) (hy : (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (hy' : (y' : E) = IsCMField.complexConj E (y : E)) : ∃ n : ℤ, y * y' = (n : 𝓞 E) := by
  obtain ⟨s, t, hst⟩ := adjoin_form hd hx _ hy
  have hc := conj_alt_bis hd hx
  have hq : ((y * y' : 𝓞 E) : E) = algebraMap ℚ E (s ^ 2 + d * t ^ 2) := by
    have h1 : (y' : E) = (s : E) - t * x := by
      rw [hy', hst, map_add (f := _), map_mul, hc]
      simp [sub_eq_add_neg]
    change (y : E) * (y' : E) = _
    rw [h1, hst, eq_ratCast]
    push_cast
    linear_combination (-(t : E) ^ 2) * hx
  have hI : IsIntegral ℤ (algebraMap ℚ E (s ^ 2 + d * t ^ 2)) := hq ▸ RingOfIntegers.isIntegral_coe _
  have hI' : IsIntegral ℤ (s ^ 2 + d * t ^ 2 : ℚ) := (isIntegral_algebraMap_iff ).mp hI
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI'
  refine ⟨n, RingOfIntegers.ext ?_⟩
  rw [hq, ← hn]
  simp

private theorem two_places {E : Type} [Field E] [NumberField E] [IsCMField E] {l d : ℕ} (hl : l.Prime) (hd : 0 < d) {x : E}
    (hx : x ^ 2 = -(d : E)) (u u' : HeightOneSpectrum (𝓞 E)) (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hu' : ((l : ℕ) : 𝓞 E) ∈ u'.asIdeal) (y y' : 𝓞 E) (hy : (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (hy' : (y' : E) = IsCMField.complexConj E (y : E)) (hm : y ∈ u.asIdeal) : y ∈ u'.asIdeal ∨ y' ∈ u'.asIdeal := by
  obtain ⟨n, hn⟩ := norm_int hd hx y y' hy hy'
  have h1 : (n : 𝓞 E) ∈ u.asIdeal := hn ▸ u.asIdeal.mul_mem_right _ hm
  have h2 := int_mem hl u.isPrime.ne_top hu hu' h1
  rw [← hn] at h2
  exact u'.isPrime.mem_or_mem h2

theorem UpperTheory.Gal.Int.Div.sameOr_of :
    CplMem → SameOr := by
  intro hC E _ _ _ l d hl hd x hx w w' hw hw'
  let c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
  have hcE : ∀ y : 𝓞 E, ((c y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := fun y => rfl
  have hcc : ∀ y, c (c y) = y := fun y => RingOfIntegers.ext (by
    rw [hcE, hcE, IsCMField.complexConj_apply_apply])
  have hKc : ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {x} → ((c y : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {x} := by
    intro y hy
    obtain ⟨s, t, hst⟩ := adjoin_form hd hx _ hy
    have hxK : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
    have h1 : ((c y : 𝓞 E) : E) = (s : E) + ((-t : ℚ) : E) * x := by
      rw [hcE, hst, map_add (f := _), map_mul, conj_alt_bis hd hx]
      simp
    rw [h1]
    exact add_mem (SubfieldClass.ratCast_mem _ s) (mul_mem (SubfieldClass.ratCast_mem _ _) hxK)
  have key := core c hcc (fun y : 𝓞 E => (y : E) ∈ IntermediateField.adjoin ℚ {x})
    (fun a b ha hb => by simpa using add_mem ha hb) hKc w.asIdeal w'.asIdeal
    (fun y hy hm => two_places hl hd hx w w' hw hw' y (c y) hy (hcE y) hm)
    (fun y hy hm => two_places hl hd hx w' w hw' hw y (c y) hy (hcE y) hm)
  rcases key with h | h
  · exact Or.inl fun y hy => h y hy
  · exact Or.inr fun y hy => (hC E w y (c y) (hcE y)).trans (h y hy)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatCent
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div


open GlobalTheory.LFun Formalism.UG Matrix in
private theorem scalar_unit_mem {E : Type} [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    GeneralLinearGroup.scalar (Fin a) u ∈ KGL w a := by
  have hv : Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have m1 : (u : w.adicCompletion E) ∈ Ov E w := le_of_eq hu
  have m2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Ov E w := le_of_eq hv
  have hinj : Function.Injective fun M : Matrix (Fin a) (Fin a) (Ov E w) => M.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.scalar (Fin a) (⟨u, m1⟩ : Ov E w), Matrix.scalar (Fin a) (⟨_, m2⟩ : Ov E w), hinj ?_, hinj ?_⟩,
    Units.ext ?_⟩
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · ext i j
    by_cases h : i = j
    · subst h; simp [bc]
    · simp [bc, h]


open GlobalTheory.LFun Formalism.UG Matrix in
private theorem satEig_self (q n : ℕ) (B : Multiset ℂˣ) (hB : B.card = n) :
    satEig q n B n = ((B.prod : ℂˣ) : ℂ) := by
  subst hB
  have hc : (B.map fun b : ℂˣ => (b : ℂ)).card = B.card := Multiset.card_map _ _
  rw [satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
  conv_lhs => rw [← hc]
  rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
  exact (map_multiset_prod (Units.coeHom ℂ) B).symm


open GlobalTheory.LFun Formalism.UG Matrix in
private theorem scalar_unif_act {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V] {a : ℕ}
    {w : HeightOneSpectrum (𝓞 E)} {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {x : V}
    {B : Multiset ℂˣ} (hx : IsSatVecGL w ρ x B) (u : (w.adicCompletion E)ˣ)
    (hu : IsUnifV E w (u : w.adicCompletion E)) :
    ρ (GeneralLinearGroup.scalar (Fin a) u) x = ((B.prod : ℂˣ) : ℂ) • x := by
  have h0 : (u : w.adicCompletion E) ≠ 0 := u.ne_zero
  set z : GL (Fin a) (w.adicCompletion E) := GlobalTheory.WeylGL.tor h0 fun _ => 1 with hz
  have hzs : z = GeneralLinearGroup.scalar (Fin a) u := by
    ext i j
    simp [hz, GlobalTheory.WeylGL.tor_val, Matrix.diagonal_apply]
  have hcomm : ∀ g, z * g = g * z := GlobalTheory.WeylGL.tor_const_comm h0 1
  have hT : Tj ℂ a (Ov E w) (u : w.adicCompletion E) a = dosetInd ℂ (KGL w a) z := by
    rw [GlobalTheory.WeylGL.Tj_eq h0]; simp [hz]
  have h1 := hx.2.2.2 _ hu a le_rfl
  rw [hT, heckeVec_dosetInd (R := {z}) hx.2.1, Finset.sum_singleton, satEig_self _ _ _ hx.2.2.1, hzs] at h1
  · exact h1
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro g hg
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← hcomm c, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hc hd

theorem UpperTheory.Gal.Int.Div.satCent_of :
    SatCent := by
  intro E _ _ a w σ B hB
  obtain ⟨x, hx⟩ := hB.exists_vec
  exact ⟨x, hx.1, fun u hu => GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ (scalar_unit_mem a w u hu),
    fun u hu => scalar_unif_act hx u hu⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSchurU
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.schurU_of :
    SchurU := by
  intro E _ _ _ a U hU z hz
  classical
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  have hcomm : ∀ (x : UA E a) (ψ : UA E a → ℂ), RU E a z (RU E a x ψ) = RU E a x (RU E a z ψ) := fun x ψ => by
    rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.RU_RU, hz]
  let S : Submodule ℂ (UA E a → ℂ) := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)
  haveI hSfd : FiniteDimensional ℂ S := (hU.aut φ hφU).kfin
  have hSU : S ≤ U := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact hU.stable _ _ hφU)
  have hφS : φ ∈ S := Submodule.subset_span ⟨1, by simp⟩
  have hSst : ∀ x : infU E a, ∀ v ∈ S, RU E a x v ∈ S := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      exact Submodule.subset_span ⟨x * k, by simp only [Subgroup.coe_mul, GlobalTheory.DefU.RU_RU]⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add p q _ _ hp hq => rw [map_add (f := _)]; exact S.add_mem hp hq
    | smul c p _ hp => rw [map_smul]; exact S.smul_mem c hp
  let ρ : infU E a → Module.End ℂ S := fun x => (RU E a x).restrict (hSst x)
  let K : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by
        change RU E a ((1 : finU (E := E) (n := a)) : UA E a) φ = φ
        simp
      mul_mem' := fun {p q} hp hq => by
        have hp' : RU E a p φ = φ := hp
        have hq' : RU E a q φ = φ := hq
        change RU E a ((p * q : finU (E := E) (n := a)) : UA E a) φ = φ
        rw [Subgroup.coe_mul, ← GlobalTheory.DefU.RU_RU, hq', hp']
      inv_mem' := fun {p} hp => by
        have hp' : RU E a p φ = φ := hp
        change RU E a ((p⁻¹ : finU (E := E) (n := a)) : UA E a) φ = φ
        conv_lhs => rw [← hp']
        rw [GlobalTheory.DefU.RU_RU, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hKo : IsOpen (K : Set (finU (E := E) (n := a))) := (hU.aut φ hφU).level
  have hKS : ∀ k ∈ K, ∀ v ∈ S, RU E a (k : finU (E := E) (n := a)) v = v := by
    intro k hk v hv
    have hk' : RU E a k φ = φ := hk
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      change RU E a k (RU E a x φ) = RU E a x φ
      rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf k.2 x.2, ← GlobalTheory.DefU.RU_RU, hk']
    | zero => rw [map_zero]
    | add p q _ _ hp hq => rw [map_add (f := _), hp, hq]
    | smul c p _ hp => rw [map_smul, hp]
  let M : Submodule ℂ (S →ₗ[ℂ] (UA E a → ℂ)) :=
    { carrier := {f | (∀ v, f v ∈ U) ∧ (∀ (x : infU E a) v, f (ρ x v) = RU E a x (f v)) ∧
        ∀ k ∈ K, ∀ v, RU E a (k : finU (E := E) (n := a)) (f v) = f v}
      add_mem' := fun {f g} hf hg => ⟨fun v => U.add_mem (hf.1 v) (hg.1 v),
        fun x v => by rw [LinearMap.add_apply, LinearMap.add_apply, hf.2.1, hg.2.1, map_add (f := _)],
        fun k hk v => by rw [LinearMap.add_apply, map_add (f := _), hf.2.2 k hk, hg.2.2 k hk]⟩
      zero_mem' := ⟨fun _ => U.zero_mem, fun x v => by simp, fun k _ v => by simp⟩
      smul_mem' := fun c f hf => ⟨fun v => U.smul_mem c (hf.1 v),
        fun x v => by rw [LinearMap.smul_apply, LinearMap.smul_apply, hf.2.1, map_smul],
        fun k hk v => by rw [LinearMap.smul_apply, map_smul, hf.2.2 k hk]⟩ }
  haveI hMfd : FiniteDimensional ℂ M := UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level E a S ρ K hKo M fun f hf =>
    ⟨fun v γ hγ g => (hU.aut _ (hf.1 v)).left γ hγ g, hf.2.1, hf.2.2⟩
  have hsub : S.subtype ∈ M :=
    ⟨fun v => hSU v.2, fun _ _ => rfl, fun k hk v => hKS k hk v.1 v.2⟩
  haveI : Nontrivial M := ⟨⟨⟨S.subtype, hsub⟩, 0, fun h => hφ0 (by
    have h1 := LinearMap.congr_fun (congrArg Subtype.val h) (⟨φ, hφS⟩ : S)
    exact h1)⟩⟩
  let T : Module.End ℂ M :=
    { toFun := fun f => ⟨(RU E a z).comp f.1, fun v => hU.stable z _ (f.2.1 v),
        fun x v => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, f.2.2.1, hcomm],
        fun k hk v => by
          rw [LinearMap.comp_apply, ← hcomm, f.2.2.2 k hk]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.ext fun v => map_add (RU E a z) _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.ext fun v => map_smul (RU E a z) c _) }
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨f, hf⟩ := hc.exists_hasEigenvector
  have hTf : ∀ v, RU E a z (f.1 v) = c • f.1 v := fun v =>
    LinearMap.congr_fun (congrArg Subtype.val hf.apply_eq_smul) v
  have hfne : ∃ v, f.1 v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf.2 (Subtype.ext (LinearMap.ext h))
  obtain ⟨v, hv⟩ := hfne
  let W : Submodule ℂ (UA E a → ℂ) :=
    { carrier := {ψ | ψ ∈ U ∧ RU E a z ψ = c • ψ}
      add_mem' := fun {p q} hp hq => ⟨U.add_mem hp.1 hq.1, by rw [map_add (f := _), hp.2, hq.2, smul_add]⟩
      zero_mem' := ⟨U.zero_mem, by rw [map_zero, smul_zero]⟩
      smul_mem' := fun b p hp => ⟨U.smul_mem b hp.1, by rw [map_smul, hp.2, smul_comm]⟩ }
  have hWU : W ≤ U := fun _ h => h.1
  have hWst : ∀ x, ∀ ψ ∈ W, RU E a x ψ ∈ W := fun x ψ hψ =>
    ⟨hU.stable x ψ hψ.1, by rw [hcomm, hψ.2, map_smul]⟩
  have hvW : f.1 v ∈ W := ⟨f.2.1 v, hTf v⟩
  rcases hU.irred W hWU hWst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hvW)) hv
  · exact ⟨c, fun ψ hψ => (h ▸ hψ : ψ ∈ W).2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaEx
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem cj_cj (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (UpperTheory.Gal.Int.Div.cj E z) = z :=
  Units.ext (GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol _)

private theorem cj_quo_mul (z : Ideles E) : UpperTheory.Gal.Int.Div.cj E (quo E z) * quo E z = 1 := by
  rw [quo_apply, _root_.map_div, cj_cj, div_mul_div_comm, mul_comm z, div_self']

private theorem scal_mem (a : ℕ) (y : Ideles E) (h : UpperTheory.Gal.Int.Div.cj E y * y = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin a) y ∈ UA E a := by
  have hy : conjAd E (y : Ad E) * (y : Ad E) = 1 := congrArg Units.val h
  have e : ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) =
      Matrix.diagonal fun _ => (y : Ad E) := rfl
  show (((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)).map (conjAd E)).transpose * 1 *
    ((Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) = 1
  rw [e, Matrix.mul_one, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  simp only [Function.comp_apply, hy]
  exact Matrix.diagonal_one

private theorem continuous_scal (a : ℕ) :
    Continuous (fun y : Ideles E => (Matrix.GeneralLinearGroup.scalar (Fin a) y : GA E a)) := by
  have h : Continuous ((Matrix.scalar (Fin a)).toMonoidHom : Ad E →* Matrix (Fin a) (Fin a) (Ad E)) :=
    Continuous.matrix_diagonal (A := fun (x : Ad E) (_ : Fin a) => x) (continuous_pi fun _ => continuous_id)
  exact Continuous.units_map _ h

private theorem continuous_quo : Continuous (quo E) :=
  continuous_id.div' (Continuous.units_map _ GlobalTheory.BCT.GlobLev.continuous_conj_ad)

private theorem ratGL_scalar (a : ℕ) (k : Eˣ) :
    ratGL E a (Matrix.GeneralLinearGroup.scalar (Fin a) k) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (diagUnits E k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap E (Ad E) (Matrix.diagonal (fun _ => (k : E)) i j) =
    Matrix.diagonal (fun _ => algebraMap E (Ad E) (k : E)) i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private theorem quo_diag (k : Eˣ) :
    quo E (diagUnits E k) =
      diagUnits E (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) := by
  have e : UpperTheory.Gal.Int.Div.cj E (diagUnits E k) =
      diagUnits E (Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k) :=
    Units.ext (conjAd_algebraMap (k : E))
  rw [quo_apply, e, _root_.map_div]

end

theorem UpperTheory.Gal.Int.Div.zetaEx_of :
    ZetaEx := by
  intro E _ _ _ a
  refine ⟨MonoidHom.codRestrict ((Matrix.GeneralLinearGroup.scalar (Fin a)).comp (quo E)) (UA E a)
    (fun z => scal_mem a _ (cj_quo_mul z)), fun z => rfl, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk ((continuous_scal a).comp continuous_quo) _
  · intro z x
    refine Subtype.ext (Units.ext ?_)
    exact (Matrix.scalar_commute ((quo E z : Ideles E) : Ad E) (fun r => mul_comm _ r) x.1.val).eq
  · intro k
    refine Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.scalar (Fin a)
      (k / Units.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toMonoidHom k), ?_⟩
    rw [ratGL_scalar, ← quo_diag]
    rfl
  · intro z hz
    refine Subtype.ext ?_
    change Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z) = 1
    rw [quo_apply, hz, div_self', map_one]
end

